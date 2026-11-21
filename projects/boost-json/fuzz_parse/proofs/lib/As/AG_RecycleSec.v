(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proof terms re-threaded to the revision's definitions, lemmas added for the revision. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit AW_LargeAlloc1 AW_PoisonRemap1 SecLazy SecLazy2 AS_PoisonRemap AS_SecRecycle1 AS_SecRecycle2 AS_SecRecycle
     AG_WFHit AG_Malloc AG_Malloc2 AG_MallocModel AG_MallocLarge2 AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_RecycleModel AG_WriteSet AG_RecycleDefs
     AG_RecycleSecModel AG_RecycleSec1 AG_RecycleSec2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_RecycleSec () := KReplay.lz_vm "#'2BC46Stdlib9micromega5Tauto5eKindI!sE;8GFormula00!si+5Lists4!s+#6nth_okC47Corelib4Init5Logic8eq_ind_r!s_78map_consK!sa+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!to19Datatypes4prod!sF?list00K!sfA1!uY72In!s=77ex!s2#bI!vR73an!t\5!sA%2ex!wJ9>!sw&_!s-%C!ty;3fstC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqb!sp=snd!sC<4andbK!u89q01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib8PropExec;!td%_reflC13~~~K!va<1K!va;1!uy;?!s<25State7!zf#hasI!uG;!yQ>bool!yQ?!sF$1!{gG3I5!xf'FSets<FMapP!sD&;!s/'Map4tree!y=#!t|66!}F%!wGT2Nd;ex_introF17!wA%C!t_'6ZArith6BinInt1Z2leC7!t0N>AsanAllocModel;compute_req!t8&!st^:rq_primary!ss&!usO2As=!sr$RepFacts<secondary_rz!tle5rq!sn+!#58=Z02!t4_7rq_size!w~B3max!w1crounded!t8Cadd!yU>t!sB<6modulo!tt_9rq_nee!ts+K!sr^3r!#4~#!uc%!}#;sym!v#=leb!uc=leb_gt!#3D;3nat02K!#=N4=RingM!#=\'Psatz!#<0?Z03!sm67Env!sp#3P!#4S$!t6I4!sOK6!sO6:Z!sL+;!v+%!wX$!u3/!#=471!sFB!vD76VarMap1!sDC1!sD@3I!sD?0I!v'C7!#B;'!wH>5PExpr!x1?!#8w+1!snE!sIF3K!u/L!wB=6option02!#EQ;8B!sl&C!xz@=Z!sT$CheckerC!w8<4find!sqAC!sq0_sou!#;VQ2As8AG_WFHitA!#:I,_facts!#9ZU!#<O%:and_elimF6!#8^&!vS;!#H_'4!sJF8!#?dA2I!~v?0!#6i^8kMaxS!#9o'!#A]<unit!{g8!uC%4ki!#CW5!sf31!#57?1I!#86b0!u<'!yu?!#4d/0!#7a@1!#5WM!#6}D3Op205!sMI1!{XU!#A;%9placed_ok!#B+X!so+4a_st!sjY7AG_RepQ3WFQ!tTb8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!uMgregion!spgpclas!w1gA!tb&shadow!swf?!sw&junk!su-!#Gx^ch!sr#li!|9[!z_,!sp%!tdh5as_t!#NYe7qc!uQg;batches!uSmgq!taV3Lib4TacX2wz!uHb5a_ctx!skethr!sk%I!skR>AW_Large!ss$14SENV!#;F&K!v3S5Cells4cell02!vw`b8!tQf4!sjf!#OY&!#O=;pow!sC=sub!uwUStep8rw_!tN#s!u9f5!|9e@as_internal_ini!~#c5zbool!uRf3!tW&!#B\'!#dY$7!s+#Def6repeat!sE;3map!}+`op!}qebot!wge4zlen!v&'!zL&!#hl-hd!s=74last!#Im_qc_bytes!u}b4jun!#E=b7a_cache!ylV!#5^:1!#4rY!#OJ/4!sk];!sk+2!#e`%I!|;_0!w$Y5ASegs5asegs!zhe;kNumClass!yL'!#Nm^5!#@{#!uP[!yR+3ATP!{%cATSD!sjb6AFLAGS!{ocAC!smg<ASHBASE_CELL!yP_!so#ADOW_!st#!tcb;AHIGHMEMEN!w3c:ACANPOISON!w7dINITE!t_c8ACTXSIZE!sndTSD!t`#!w2dALLOC!zQiIA!t`f6AHOOKS!sldDYING!v<dREALMEMSET!v<d!smjGOT_LO!smb9!sm$VAL!xcePAGESZ!{5dSECNAME!uNdPRIM!sof8ATLSSLOT!sndLSANDI!w-c5!ww#2!skb<OT_SWITCH!|%e5OT_T!#`>%!#=s^6q!#UF#!#=t'!#W#_b_addr!wycOT_CACH!#:ec!sk$_STATS!taf!sng!xo#UNWIND!xo\9!sr'X:!#dS#x!#ZF+!#W=R?AW_PoisonRemap14R!#W>Z!ss<!#ISg5!vHc9ALIBCPG!#5}Z!sp,8!#7^#SSP!taeSSPGUAR!#@_b4a_sb!sjepa!~^e=as_n_reserv!$-2'!#4I^as_sec!uSb5w!#dCY!zF#3Arr6u64arr!w&eri!v2e7as_qmax!spkin!spe9!sp#!#Um,!$5$=ulI!$$lB!$B079nth_error!$%TC1!#m8_sc_map_beg!v6e;!ss&!$8:,!wv_sc!$9+F6of_nat!#8ZR7!t7$Wf9!#q'%o!#UF'!sp[8!y$$!so-C!soZ@carved!#?A#!#oG-!#~K;appI!yZ65NoDup00C!uG\!#rR#!#}A'!y0_ch_user!y~i:ch!$B21!$'`;negb!$PD7filter!v9[9q!x['!tO'!t158flat!{v#!#d:_ch_stat!|^f<ch_!x@%!wKh9qb!su%!#_W&!wJ1!$Ke%or!$1y`:get_!}Y%!u%e>rg!wV#ped!zK$!swe6!tl#pc!soe8pc_coun!#k{e:as!vO&s!|'B6length!u-`as!#j>-!#<Cb!yf/C!$P~J!$<b#!tG^4ckey!#7XZ!$2h$5xc!$4@[!sj,b!$5+]sS!$,\#5aceil!skb4aap!#t1dkobj!skd_f!#Ibddisj!{p8!$ZK%not!t'\9!u]$_env!ttb8!w:#!sn-!#@|14Znat5Nat2Z9is_nonneg!$E?59SatDivModCZ_mod!sP&!sW'!|4O8HeapCeil5h!yjf2sh!shb;!{A$!$Fd[!#QC/@sh_!st#ing_range!swV!#u^+:!$&2#!#F&-!snS6!sn$X<!$&~&_!}7,!#Fu:>pow_po!xz+!sN;:!sN#!sJB7compare!$NUD4!sIE7!w]UG_Ma!wa#9!$:X#stk'!vfZ!#z|/10!sl]!#Z&+9!skg3!uFh!#\Jg8!skg7!|>[Frame3st!#;-%!$PME3!sJF5!#6u[5AINS!#k9%!#g{_s!#~q/!$LtH3!u,\;OI_SPACEBE!#e+&!u3^@kPtrArrayR!#]a$!#7PZ!tl&<OI_NRESERV!#z]c!u`$ECMUTEX!sqb9OI_G!#iKf4OI_!$O_b7!sj#MA!uJgQ!v;g5!v;#!uKc:OI_FB!t]g!sp#MAXUSER!}S&!$Wp?!#Pq_9kPageS!#]JgAkC!#L1#BlockC!#O7+!#3b_c!#UW#!#3b'!sqf2!tdf!#Pr$!#^s'!sq_!$SY$!#w8fBkQuarantine!$a2/!s{lin!s{i=kMaxCach!z8/!#RQI3key!|iU!#Gn%6AHI!$'V+!#Vg^kSpac!u5/!~L[8AFS_!$3j+!#\874True!%$y=:!#FB$is!zR$!tXR!#T2&<AREPQ_!$bB$!uKY!sq'9!sq%!$aY[!sn2mem!sn&!#bH5<!#mC'_In!#RC13Nat!$OXS!$EQ#!tN#cycleSec16rs_en!$MxY!sr6bnd!srh8!sr#ands!sth7rs_pnew!ssll1!#sv&c!ssR=!ss0!u]#gpo!#ly&K!%2_I3Run6config!$k:T:AsDepotInv4d_n!#Y~Y!sl1!#Zl'!#v0;div!#ZE2Peano2l!$Oz_7!#n?$!#};e8!%,9#_u!$`ze<find_sec_id!#{#e<ch_!#SN#!#ptiin!#pt1!ss^5ch!%3w+!{qT!#8v%!%4p#!sp#lo!spY!#9h'6ch_e!#41'!%B[?Dbv_unsigned_in!#[v%!sY@;!sY-!sPA:bv_!%2q#us!uBS!$0r,awin_vi!#^Uc7AMODEL!#I3b6!sm%!t\dakernel!t\b?amaps!x$#ledger!sud!$qf%visibl!#A1b7ABUDG!$H4'!#58^as_!u`#!spfmp_kin!%9Ve5m!%%p#3!spl4!uTibase!~ZG7Z_to_bv!t>c!#gA,!%I1O8m_vm!xC$!%IhPvm_!s\U;vm_noac!s;#!ugP<LazyRestrict:!#5y&!#qoc3a_L!x]V:!t\#L!~I$9nooverlap!sna>entries_nowr!ss+!v{T!$>#'!xrQvm_limit!s]Q9!#>H$to!$mb\2RB!uaW<!%Xf%tains!tK\4a_Zr!#99b4hc!#KzZ!sk/!$B2[!sk/!$oq+!skR6SecGap4zsum!z9X!$:@%free!#KL`@!%PK+!%KH-!#s^<di!#@m#!sG<=mod!#ts#b!%@U#!sM@neg!sM25!#ji#8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL&!#koC!%Ib%7!vWaDlarge!#x&%of_arep!%'j%!t#a=senv!sxp>r!sx/!%+3V!$I}#Mem5wr_a!$}&[!#]D%3n!#~w'!$CG;to_nat!t1\8p!$T4#!{4+!#YW5:!$5@$!$<{#!#]367and!%]/#3!#?4$7tac!}G#<f_equal_help!to\<!to%!$zr/!tT78iff!%b9$!{<5;Zify!$u7%!%_+#ff!sLB9!uJ#morph!sOB7rew!sv$!uVR?!#~6'!${%#2:u8arr_app2!wP2!tF93inj!sIB;!ti&_rev!xF7=!%&h$_!$:g%!vs75proj2!#_;6!%[J>8max_spec!yd?app!$[{R<!#9G#WalkKit6hidden!$[z&I!srg0!wA<!$2y/div!$2y1!$3w<2id!sD>7inj!zL%!|f7!x&#sym!~:]!$5m#sub!~:=?!$LT#_!#dq'!xt=1!tr9!~B&!#hh+!%1d1Fora!%$v#!z?7!sC%_f!s,$!yC8in!$Rr#!vA#!#5X;eq_dec!#j:16Specif7sum!%l5$!#7lS9LiaTuning9zify_don!$4P[M!#?r#C!#Mg%_!#Xp-!#8pY!#JE+!#}g&!#K{[8r!s/&!uTZ!$-V%mkR!sgZ!%s$'7seg_rom!w,a2M!$$rY!$jK,ak_sec!#VP+!#@7a!%t3%_of_In!tkc<!tk%!#Qe$!ssc8ak_zrsh2!sogshrf!sojmc!sod7!so$na!snY>AS_Sec!x3&2@r!s/%!w@$!#nJ+!s|b4rs!#U=&!$#&O6!}v#SR4lz!$^oY!|=-6r!$T5-!uFa8rs_mod!#c=Z!st11!v<#W!#4C_5munc!$GbZSec!w,#29wmono_ou!$m,[Mem7mem_i!$LXZ!v729r!$UD1!yRV;!yR#!#]C%!slV9!sl#NodesFlazy!so&_okb!#[n0!thV8!th$SZr!sicZrL!w5[!#7d-2@a!{:$x_after_r!#n%c9depot_co!$RWb4a_A!#a]V!#e|1?!$\w&!%Oo#!#xvfArg!#w4$at!$af0!u`R!$Z~'!$+7#!sjZ!~#&:nonvm_sam!#nvY;AG_WriteSet4avm!%['Y!#~S,5DEP!%3{Z:!#PP'2<!yf%!$10^!uR/6acompl!|JdDefs4a!#wA[!sp25pend!%`'b8agree_on!tah:alive_kept!uYi!sv$!sq%!#EH`?!#<w&_clause!tmdSec1>!#^T#!#5\a!sz2=!#}U#!syp?!%4X%!s{2!#g]O:map_remove!#lnQvm_m!$~R#as!saR6vm_brk!t>Ustart!saU=!#~Y#subtract!#uK]eager!$3#-!x-`2=avmx!y%q>!#5w$!szpB!#6s-!t%%!z}i!#6|$!|usvis!vrr!#76#!tus!#6O'!tul!sy%!tue!#<Z$!#Af$same_but!%yu%!s{Y?!tw,!s|$9del!%$=/!svRB!uo0!sy%sec!s|#l!$d+&!$'Q^set!%;g\!tk6;se!%5Um:!#7T$!#nd#!tpk6!v]%!wUt!&LIgcb_!#W:%!sse>!%5D#i!$87#!$MC,!$[|:or!%25+4Bool!s'$<orb_true!#pn/!sF,=and!sG-!#fN;leb_le!&To8or!&U1:or!&?P,!tC,>!tC$fals!tD%!vC^<as_space!zo-!$HX;lt!&IQ>tb_ge!$QC7In!#kS,!z0e!$R;,lt!{-lC!z:,!#^N#eva!|3W!$q[4!$s6^ex!sk&6!u^Y=!#YZ/B!uV/srea!#\5W!$rZ32!sk]9!uW+!w1h8!slh!$@'%!#cCPSR!vm#6!vt%!$rTK!$,c%5!&AnM!$uUF7!$}'D5!vCT3Arr5!#}h#!#6I&!t24!#}@-5mkrel!sKEapp!sKB6!sK$2!unF6!#8,;:!%LI$!$'v$!#4Q4=!#3Y+!%B=R4Scfg=hunspell_scf!#6F9!#{i,6inj_lt!un68!un#Inst@!%KK$_!$/1$_eq!$4m+!st$8!$XR#Na!$$H;!#}$2!sI/!si7sub!si>;!si#sub_maxI!#NPI>!&kF#!sE+=machine_!$n{%I!#O?O5!#7K#00!$mm^7mapping!$naf!$KE%!$q9e!sp&2!spl6!spl8!#9lX!%|>$8AIMG_TO!%`w&!x]PBtarget!$]T%!$Fl$!uF^;kR!$A%#!$nY^!$,W%9ALOWSH!%to[!v;%7!v;$!sj[!$Dt,AHC0!skfL!skd7ASEC!%$N'!$qh75False!$}2`@!$|>$Header!$wtj!s6#HeapFreeMagi!%N>eI!s{+LeftRedzon!t&0!#8J=7Inj_Z_Z!%Yy66E!&{W#!&Z$3!$uj-1!{C\3!#M?'I!siTl!$14&st!$~Bga!%$s/!sq`effect!$:i+!vX69F!#Me$n!&?$7;!'#m$_last!$6S83sig!$z'3!sB&4sigT00!#<m>8sub_diag!|G3!$oQ%e!'%]9!#@F+app2!$KZa!#J=-!#j5%!#Mvl9!#Mk#nt!&zTW!#JM2!#K9&!#BABe".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14prodk14boolk14listk14pairk14true37Corelib4Init5Logicnc2eq3h5LinuxProcessSemanticsfLinuxProcessSem5Statep57map_has36Stdlib5Lists4Listsd2In69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~u5bcompute_reqk15false01Zu58kMaxSizeu59rq_neededu5arq_primary46Stdlib6ZArith6BinInt1Zhm33addhm32lehm32lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAW_LargeAlloc1~~~~~~hoe4SENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~hta3ATPhta4ATSDhta5a_ctxhta5a_thr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ij92wznc2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_PoisonRemap1~~~~~~inf4RENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~iscaflagsx_repu56astateu56effect79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~jibfsame_but_shadowk14Somek16optionnc3andu5acb_recycle3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjq5dmachine_statep55Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecycleDefs~~~~~~jv5arstep_post99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAG_RecycleSec3HCW6RSStep~~~~~~kk7frs_model_clause3h5LinuxProcessSemanticsfLinuxProcessSem3Runkq85mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ktd5asegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~li16sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~lm4dhunspell_scfgkk78rs_gposthta4a_stu5cch_chunk_beg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~lsf5AREPQk14consu55chunku5achunk_listu5ach_primaryu5bCQuarantineu58ch_stateu56cstateu5fas_cache_initedisc8awin_visisc7AMODELX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~mo95DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~mt2cdepot_placedisc9depot_cov79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~nif7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~nn45aceilhfbbv_unsignedhm36modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~nt33stkhta3a_Lhta3a_Shta4a_Zr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~oic4lzokk14None69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~on48restrictnt33mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~os62MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~pg97seg_romhf7Z_to_bvu56schunku56as_secsd9nth_error79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash2AG_RecycleSecModel~~~~~~pnbbsec_map_begu5asc_map_begk16length37Corelib4Init3Natpu93sub" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma map_has_of_In : ltac2:(zQ "a1!h9!jc!l9!m0!m7!me!n5!p0!s3!u0&@2$2@1$1@1$0#k0@1$1@1$0#k0>1l@1$4~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$9~0@4$5@1$1@1$0#k0@1$1@1$0#k0^2^1^3@3$7$3@3$8^4^3^2$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec ()) [] "##/:h01lh11xh21Ah31bh41fh51Hh62H0h72loh81nh91pp;1p;2p;4p;3p;6p10000p4p711!s2$Op4p73101p8p10013!sB$0g001NR!sO%0R!sC'lp4p7210P1p8g002Ij11Tg002nj1FTg003Lj1A!s/$oj2?Tg004Oj1=!s/$oj4;Tg005Oj33!s/$fR1j36Tg006BR2j25!s1$]j27Tg0077j3>!s/$Zj3:Tg0087j32!s/$dj3<Tg009Aj24!s/$_j2ETg00:9j28TP0j69Tg00;Ej4D!s/$`j4CTg00<:j3BTg00=0j3@!s/$JR0f0R3g00=jR43@p=0g00>J#1!s$-FR5#AR6/?6R7#=P6P6f1R8P3C;f2R9537P1!vL'P0\3R:%=8R;P2A6983#0f3R2f4R<?339P2P3O1#0'5X12'7R=[A3238P9!s=,9,79A6298#0[R>A6<29#0\=A>983P3n200!x7$0012!s-%0W0W4W2P>^0;^4:^21P3P7A:663=25<A<!s/%2'4R1X97P<P7f59373%01'5X17P6P6P2P9C;R1A371<A:661=252A<!s/%9'4#0R1P8P0P4A2522R<,43#0X30P0P414!s3&1E04A25991859E9P<1852E9P1eCDCCO4b6AB!uQ$eW5X86X76W0o"). Qed.

(* [comment removed for export] *)
Lemma secondary_needed : ltac2:(zQ "b0!hi6!m0!hj4!p0!hjc!hjf!hka!hl6!hnb!ho2!ho8>1n$4>0@2$9Z^1>0@3$3$1@1$7@1$0^2$2@2$a@2$8$5+og0@1$6@1$0^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec ()) [] "##<8h01Ph12RNh22H0h32_Hh44__x1h54__x2h64__x3h71bh81xh91yh:1zh;1Hh<2Hnh=2RZh>3_H0h?3_H1h@3_H2hA7__arithhB4__ffhC8__varmaphD5__withE1np;2p;1p;3p;6p;4p;9p;7p;8p100>op4p710R0g00?^R1!s5%p8P0p1001N!s61@:!s6'g00A@j28Tg00A\j11Tg00Bjj1:Tg00D7j2hTg00EHj15Tg002Ij13Tg00FPj1?!s/$nj1KTg00H8j2CTg006BR0j2=!s:$Uj12Tg00Ibj20Tg00J?j27!s/$[j2OTg00=0j34Tg00K;j19Tg00LGj6PTP1j6>Tg009_j2MTg00MOj4[!s/$kj2ATg00NHj2Z!s/$hj1LTg00OGj2@Tg00P0j1Y!s/$Nj2X!s/$oj3WTg00QXj3JTg00RAj2V!s/$mj1UTg00SMj3STg004Oj1R!s8$mj2HTg00TKj1Q!s/$ij4ITg00UGj1T!s/$ej1gTg00VPj2GTg00W3j1f!s/$Xj2eTg00X;j3F!s/$^j4ETg00YIj1c!s/$kj2_Tg00ZMj2^Tg00[9j3`!s/$Xj4]Tg00\Jj2aTg00][l9bTg00^`j7\Tg00_Dj8d!vh$JR1f0R2g00_hR334p=<g00`HR4f1R5;42p=6g00`fR6,A2p=;A4132p=BP5g0000R7g00b1R8P8g00bQR9P2g00c1F\p=Df3R:P7P8P8P9f2R7P5P2Gdp=Ng00cQR;/82%15#:#<1h72%17#5g00>JR<#3R=#3#3R>#3R?#3!s$0?R@'6%1:RA#KRB%?<,C:'6RC%??R?%5ARD'818D@'=%?>R>,C:RE%2ARF'810E>,7F'=1OF>=44;%9ARE10FDP1P4%:ARAP;PDn010!s#$20000'0'6g00coRG%1BPBPBPDPFPEPAEP34106@/7Ef4#1#5RE,8?18E@'=f5RE/C>R?%1E#2RE'810?>,7E'=f6#1#2/O!tP$f7R>#1RE#9%2E%5ER?'0!t[%EP;P?!tY5f8R?!sW$KRA#1PAPA%5E%2E%9E%:EEP54GP1f9#1RG#:f:RE#1RA#9RF%2ARD%5ARA!t0%P2P;PA!t/5X71P5P3P>E>%9G%2G%5GRG'0/0G'6P4PAf;!sy%%2ARG/02/02'6X:4P2P@P>E>10D@/0@,6F%5A,0G#;RG,M1%:A=41GP1f<!tk&=!sn$2RF!td&#;9412X71P2P3PEE>!tK%'0#;#B!tH$>#1#2RA/02#;#B!tB'EE>10F@!sL$1P310A@#;RAP2C[%<Af?!w5$0@#;#<P01A52#<1757[R017251A75#<RA[177:\A1Z52P5n20!v7'1!v8$000X94X84P0^94^84P2fA!t#&R0P6P5O31760g00e7R!s,$cRA#LR3#L,@4%Y<,X41@435W41@4A5J45J4g00fB'V%U03S%R0P41H47P5!s-$:P:%Q4CICI%T4%g4!sE$G4<R<g00fnRA%f=,G41e4@R35F4RFCE,D0%c8R8P!sR%=R=g00gUAF4F3!sD$P8P4AF4<3PAP=!s8$CNCN1_09P2P7g00=jR0,M11^27=410dA`4;5C]bBbCbDX44X54X64107@R;,7210:!xZ%717;:[[^44^54^64P2fC#1R;#2%9;P6P5P?O5bAb0b2W0P2O1b2b0!s$$1b1W3W1W@W?W>X3C1a:7M9bb=W;W<XE4o"). Qed.

(* LPS revision repair (75d69e00, checker 2c6b6db8).  UNIVERSE ANCHOR for
   recycle_sec_arepq_at's replay below; TWIN of Bs/AG_RecycleSec.v's, carrying no address and
   no literal.  `KReplay.run1z` hands the decoded term to the kernel with `Std.exact_no_check`
   (KReplay.v:627), so a replay can only CONSUME universe constraints already in the graph.
   The term applies `Nd.ex_introF17`, a monomorphic `Lemma`, to `ast`, whose level is
   `max(Set, PositiveMap.tree.u0)` through `a_st : astate` and its `as_chunks : PositiveMap.t
   chunk` field; that needs `PositiveMap.tree.u0 <= ex_introF17.u0`.  Measured (scratch probe,
   image 2c6b6db8): `Check (ex_introF17 ast)` elaborates and prints exactly
   `(* {} |= PositiveMap.tree.u0 <= ex_introF17.u0 *)`, so no level moved.
   KNOWN RED BEYOND THIS POINT, and the Bs twin measures it: with the anchor in place the
   file's first error MOVES OFF the eliminator and onto an arity mismatch applying
   `@recycle_sec_sreach`, which is a different repair. *)
Definition u_anchor_ex_introF17_ast := ex_introF17 ast.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Section PreCells.
  Variables (s : ast) (XC XB : list Z) (m : mem).
  Hypothesis RQ : ltac2:(zQ "10!mgc@5$0?5HCEIL?1s?2XC?2XB?1m").
  Let st := a_st s.

  Lemma senv_of_arepq : ltac2:(zQ "60!ht2!ih8!ihf!ii7!ij0!in4@5$0@1$5$1$2@1$3?1s@1$4?1s?1m").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec ()) ["HCW"; "PreCells"] "##Aoh02_Hh12F1h23F10h33F11h43F12h53F13h63F14h73F15h83F16h93F17h:3F18h;3F19h<2F2h=3F20h>3F21h?3F22h@3F23hA3F24hB3F25hC3F26hD3F27hE2F3hF2F4hG2F5hH2F6hI2F7hJ2F8hK2F9hL2FLhM4INSThN2PLhO2T1hP2T2hQ3T2bhR3THRhS2WQhT1chU2chhV1vp;2p;1p;3p;5p;4p;Cp;7p;Np;9g00h<j2{Tg00iEj1zTg00jIj3^Tg00kKj2UTg00lSj2yTg00m\j2mTg00nfj2bTg00omj2]Tg00A@j2YTg00J?j2VTg006Bj2ATg0113j3TTg012=j3STg013Gj3xTg014Xj3sTg015gj1lTg005Oj3kTg0174j2cTg018=j1aTg019Ej1QTg01:Oj2RTg01;Zj1\Tg01<bj1=Tg01=aj1ZTg01>fj1XTg01?kj5WTg002Ij11Tg00W3j10Tg00FPj12Tg01A7j1DTg00Rmj1NTg01B;j1JTg01C:j1ITg01D>j1ETg01EBj2r!s/$_j2@Tg01F<j47Tg00Nhj1G!t:$nj1jTg003Lj1iTg00SMj3:Tg01GAj2dTg01HEj1eTg01IXj1fTg01J]j1gTg01Kaj3hTg01L@j4O!s/$\j1`Tg01Maj1_Tg00Ibj2CTg01Nfj2nTg01Omj3oTg01PDj3p!s/$]j1qTg01Qhj3KTg01Rlj1[Tg01T3lCtTg01U?j7uTg01VDlNvTg00][l9wTf2R0f1R1f0R2'A'Ap=>%12#1p=4%12#2p=6%02#0p=Bg01WJR3?:12p=9A:3129:30p=Mg01XNR4f3R51C01P2C7p=3%1!s^$H!sf$#0#0p=L!s2+!s$'p=<%=1#E=:32p=8%0!tJ$?%=2#Ep=;f4P5P0!t:$C7p=5%G2#Gp=FP4P0P!t7&Pp,5HCEILp,1sR5'{R6%z5R7p,2XCp,2XB3^R8p,1mR9,U5R:1y59R;1m59R<1b591]59g00`HR=g00cQR>/Y2g01YP,V2'AAT591AS591Ax591As591'A3>[]Tg01Z^R?%l79k?21c91[]U%a7R?#QR@,R9%\7#Q,R9'A3>3>RAg01[h#=RBg01\kRC%Z5RD%X5REP9DWRFP9g01]oRGg00>JRH#1RI#0RJ#0RK#4RL#2%1IRM#1RN#1RO#1RP#4!s$$6#=RQ#D%=>RR#DRS%BKRK#0#6#=#D%N3RT'93MC3RUP9PG%0MRM#0RV#0#6%2HRW#J#IRX/9TRYC3RZ!sK$1JRJ#0#H#2PYC3R[!s;$6L!s3$L!ty$_5RG%0N#6!s:$\!t%%HRH#0R]#0R^#1R_#1#6%L^#<!s$02/8TC3R^!sY$4M#4RM#2%ERR`/9TRaC3Rb!sA$?P#6%J>RG#IRc/9TRdC3ReP4!tM$`<g01aH#;PTD5Rf!s<&bQ%2I%2K'r/@W#;19`aD5Ra!sD&c\PYC7RW!s5&df!s5$Y!s5&em%2_#=#D!sx$_!s<&g5PXg00ec#G#FRK%jN#iRI%NI9:IG9:IG7:G'd19STRS'9D5RG!s_&h=Pc19XdD5RX!s9&iH%e7#f#J#I%gR=McTD5Rc!sC&jO%GK#F#F#F9h3`C7R`!s@&kUPSC7RK!s5&l[g01mf!up&R!s<&nmP=P3%;2XV=g0204COC7R2!sD%21=%EQ!sV$Q!s8&2D%1H#B#?#B#H#?#L#2!sx&H!sH&3L%LM#4!sF$!sB'M!sB&4U%;C!s8$3P4P9PC18DTRCC7R7!sH&5]!u'$I!s5&6e%2O!sk&OPFAP9ECRCP9PD%2NRNPSC3RS!s5$4V#618ETC3RVP9PEPN%`5%_5/8T'8C3P9PE%1J#6Pd!s3%g027jPdC3g0296RJ,CERNg02:;R4/n@P4P=g02;FP@COR@9o=>Ap=@>%q?!sx$'8'85P9%2PRP,CNg02<PRN/@J/@P5K9%[5g02=XR5'Cg02>cRP/@N/@55K91CEPg02?kR5!sS%!t}$5PdC3!~S%3>RdPFPB%1]#4#?!w2$4#H!s2$4#6PDPEP9fAf7f6P1fDf;fFfEfIfHfGf<f:f9MCtPFeX0dXQVXPSXOCfLFuXDOXCIXB7XA3X@MX?HX>QX=2X;RX:KX9`X8cX7XX6GX5_X4YX3WX2aXKfXJeXIbXH^XG\XFLXE[X<ZX1UP0MNvX0AXR<XL;XM:XS8XN6p,2RQM9wo"). Qed.
  Lemma renv_of_arepqx : ltac2:(zQ "50!h9!jc!ina!is4!jgb>0@1$4?1m@2$2@1$1@1$0#k0\1g@1$1@1$0#k0@2$2@1$1@1$0#8\1b@1$1@1$0#8@3$3^2^1?1m").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec ()) ["HCW"; "PreCells"] "##@bp'0h01bh11gh21Hh32F1h43F10h53F11h63F12h73F13h83F14h93F15h:3F16h;3F17h<3F18h=3F19h>2F2h?3F20h@3F21hA3F22hB3F23hC3F24hD3F25hE3F26hF3F27hG2F3hH2F4hI2F5hJ2F6hK2F7hL2F8hM2F9hN2FLhO4INSThP2PLhQ2WQhR2X1hS2X2hT2X3hU2X4hV2X5hW2_HhX1chY2chhZ5nd_i1h[1vi001xp;1p;4p;2p;3p;?p;Np;8g02A7j1sTg002Ij11Tg01<bj1<Tg00Rmj1PTg01F<j44!sJ$nj1MTg003Lj1LTg01D>j1@Tg006]R0j2HTg00W3j10Tg00FPj13Tg01B;j1JTg01C:j1CTg02BBj3ITg00h<j2bTg00iEj1aTg00jIj3`Tg00kKj2_Tg00lSj2^Tg00m\j2]Tg00nfj2\Tg00omj2[Tg00A@j2ZTg00J?j2Y!t`$Bj26Tg0113j3XTg012=j3WTg013Gj3VTg014Xj3UTg015gj1TTg005Oj3rTg0174j2qTg018=j1pTg019Ej1STg01:Oj2QTg01;Zj1oTg00Ibj2ATg01A7j1GTg01EBj2m!s/$_j2lTg00Nhj1FTg00SMj3:Tg01GAj2iTg01HEj1hTg01IXj1fTg01J]j1eTg01Kaj3gTg01L@j4jTg01=aj1kTg02COl?cTg00;`j4RTg01VDlNnTg02D\j8NTf0R1#1#1p=>%11#3p=8g01WJR2f1R3#@;:1p=Of4R4f3R5f2R6%<3#@=:21C4p=7P4P5P6A:23!s6$?%01#0p=9g01_5/A1p==!sC$p=2g01XNR5P6P3P!sS$5%0!tH$D%1!s[$B!sc$#0#0p=K!s2+!s$'p=;%F1#Fp=E%<1#@p=dp,1mR6#sP5P6g02Eag00>JR4#1R7#1R8#1R9#1R:#1R;#1R<#1#>#>#8#<R=%P2R>'OR?C4R@!sg&Fkg02H4RAP>D7RB%M<#LR<P5P6PA%@1P>D?RAX1<RC'HRD%04RE#1#9RF#1#9#3#=%34R4#J#CRG/2>RH556RI%M9#LRJ%9ERE#1RK#D#8#=%C1/2>556RLX0JRM'HRNAI316X0J,HJX1<RO,H<RPP0P<PCPP\N\IP1P0PJPMPPP1p,5HCEILp,1sRM'bR0%aMRCp,2X!s'$B3`RQ1_M6RR1^M6RS1]M61\M61[M6g00`HRTg00cQRU/Z1g01YP,Y1'6AXM63AWM63AVM63AUM63'6'6'6[]Xg01Z^RV%TC9rV11q63[]Y%pC#S,Q6%o!s-%'!s$-RVPPg01]oRW%07RX#0RY#>RZ#3'A%G=%<UR=#GR[%9YRY#0#8#<#G/2>'2'2556R\%08R8#9#8,AW=56HR]%BX#B#3!s6'X%8Z!s2'W%09#8#=!s3$9%1K!w0$KE#;!s$03#</O!wB$E%>8#>R8!x'$@=RZ/2>R^556R_%D;!sd$JURU#CR;/2>R`556Ra!yD%1`<g01aH!yB$b!s:&bQ%37%3Y'm/l412Z^D7R^!sB&c\PHC4R4!s5&df!s5$H!s5&em%3K#<#G!y|$K!s<&g5PGg00ec#F#ERY%PJ9:JU!s&''i12[>R['2D?RU!sY&h=P;12G`D?R`!s9&iH%hC#f#J#C%e=/2>,2;D?R;!sE&jO%FY#E#E#E9g2ZC4RZ!s@&kUP[C4RY!s5&l[g01mf!uh$=!s:&nmPTP2%d1X[Tg0204CjC4RT!|`&1=P?C4R?!s5&2D%DF#9#B#D#K#3!so$F!sB&3L%K8#>!sD$!s@%8!s@&4Ug01\kR2!s<$C!}F$2%kM!s5$M!sK&5]!ty$[!s5&6e%3:!sG$>PPP<POfWROPJfX?I!|q$fQRPPOPPP6f7fBfAfEfDfUfPf8f6f\f[fVM?cAIOP6eCRCRXF>XE[XDMXCCXB8XAFX@?X?TX==X<YX;ZX:;X9`X8UX7KX6HX54X4^XMbXLaXK_XJEXI9XHWXGXX>]X3\P3MNnXWVXNSXORXQQXP0p,2RQGNXVLX0JP3P1O2n20010!s#$121!s0%X2NXUIXTAX1<!sL?DXSBXR@P1GNWZo"). Qed.
  Lemma large_cells_of_arepq :
       rw_cells asegs m (AINST + 32) [C8 (wz (a_sb s))]
    /\ rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s))]
    /\ rw_cells asegs m (AINST + 112) [C8 (wz (as_n_reserved st)); C8 (wz (zlen (as_sec st))); C8 (wz 0)]
    /\ stk asegs m (AINST + 136) (AINST + 680)
    /\ rw_cells asegs m (AINST + 680) [C8 (wz 0)]
    /\ stk asegs m (AINST + 688) (AINST + 728)
    /\ stk asegs m (a_thr s + 2800) (a_thr s + 3168)
    /\ u64arr asegs m (a_pa s) (wlist (map sc_map_beg (as_sec st))).
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec ()) ["HCW"; "PreCells"] "#$+{h07__arithh14__ffh28__varmaph35__with46__sat4h5!s/%5h6!s/%6h7!s/%7h8!s/%8h92_Hh:4__x1h;1Hh<2A1h=1Kh>!sH%9h?2chh@4__p1hA1zhB2A0hC7!sD$10hD2HahE2P2hF2T2hG3_H0hH3_H1hI3_H2hJ3_H3hK3_H4hL4__p2hM4__p3hN4__p4hO4__p5hP4__x2hQ4__x3hR4__x4hS4__x5hT1chU2schV2A2hW2A3hX6ACEILBhY1BhZ2FLh[4INSTh\1Jh]2J1h^2J2h_2J3h`2J4ha3Jsthb2NNhc2P1hd2P3he2PLhf2S1hg2S2hh2S3hi3SEChj2T1hk2T3hl3THRhm4Tunwhn1Uho2W'hp2WQhq2Wnhr2Wrhs3_H5ht3_H6hu3_H7hv1bhw3ch'hx4cstrhy1hhz1ih{1kh|1mh}3sc'h~1xp%0p&0p&1p;2p;1p;3p;4p;5p;6p;7p;=p;<p;>p;;p;:p;8g00h<k21VTg00iEk11UTg00jIk30lTg00kKk20`Tg00lSk21TTg00m\k217Tg00nfk20wTg00omk20kTg00J?j2YTg006BR0j23Tg0113k30YTg012=k30TTg013Gk31STg014Xk31FTg015gk116Tg005Oj3LTg0174k20zTg018=k10vTg019Ek10JTg01:Ok20NTg01;Zk10jTg002Ij10Tg00FPj18Tg02I>k10gTg00Rmj1sTg02JBk10_Tg00W3j14Tg02KFk10!s0$LVk10!u/$Nfj2aTg01<bj1RTg01D>j1eTg01>fk11=Tg00Ibj21Tg02M_k10CTg02Ndk40ETg01A7k10BTg02Ofk10xTg01Qhj3|Tg02Pjk10qTg02R4k10pTg02S>k10oTg01Omk30ATg01PDk30@!s0$]k10?Tg01EBj2uTg01J]k10>Tg01B;k10=Tg01C:k10<Tg00Nhj1J!v5$nk10:Tg003Lk10iTg00SMj3CTg01GAk20hTg01=ak10fTg01L\k10!ua$Mak10d!tC$_j2!wz$Rlk10cTg02TJj2b!s/$gk109Tg02UIk30!s:$Ugk208Tg00=0j3=Tg02VIR1j1hTg02WVj1rTg02Xdk10aTg02Ynj1\Tg02ZNk20^Tg02[Xk20]Tg02\ak10!sD$^0j3`!s/$Mj2!v_$^ik20[Tg02`0j1!vh$a>k10ZTg02bKk10X!s0$ik30WTg00A@j29!zo$[j2ITg02cDk206Tg02dLk40V!s0$ik10UTg02f4k10KTg02gCS00k10S!{L$]k20RTg02hOk20Q!s0$ik20!y$$j6k100Tg02kGk202Tg02lPk105Tg02m[k10PTg02nhj2~Tg02oHk1!z#$30Sk11QTg031_k31NTg032Lk11MTg033Sk21LTg034Wk21KTg035[k1!xZ$36`j3jTg037dk31ETg038ik11CTg039nj4{Tg03;2k11BTg004Ok11ATg00TKk11@Tg00UGk11?!s0$ek11>!|:$Xk20HTg00Ykk21!yw$9_k20GTg00ZMk21;Tg00[9k315!s0$Xk4!|m$3;Kk513Tg03<Tk512Tg03=\k111Tg03>Aj2P!zQ$mj2lTg00VPj2d!t9$Ik10}Tg03?2k10|Tg03@4k10!u;$A6k10~Tg03BAk1!~W%;Ej4OTg03CRj1xTg03DZj5yTg001Nj6nTg03Eek20yTg03FMk318Tg03G1k219!s0$Rj3vTg03H5k31:!s0$Xj7wTg00OGj2zTg00QXk30ITg00RAk20u!v^$ij4iTg03Ibm=0tTg03Jhm<1DTg03Kmk60sTg03M2m>0rTg03N8m;1GTg03O=m:1HTg03PBk41ITg01F<j4k!}C$@k40LTg00X^k407Tg00^`k70MTg00_Dk80n!sD$;k31!ur$QCk61P!s0$gk70mTg00cQR2f0R3'9p=2f2R4f1R5/33'3p=5g03RKR6/13p=B%R3#ep=Xg01WJR7?C53p=Z%03#0#0#0p=TAC7539C74p=@!s>$p=f%03#8p=}%R4#e%R5#e=C735C7p=K!sb'8p=7%03#4p=[g01XNR8P4P5P3H1Ip=EP!s4&Ckp=D%4!sN$A%4!t-$c!s6$!tN$>0Fg03SPR9g00`HR:P1P3H0Lp>0DP8f3R1P4P5Ck/33p=W!s^%4#4p=>!te+p=]P8P1114!t=&;1S539|14p=Hg02:;R;P:g02;F!t%'O%J3#Jp>0;P8P1P4!uz$Ckp=tA=:53p=MA=:52!tC$Q!sR$#J#Jp=^A=:32p=g1145/93p=Gf4R<P!ts%{!sV$<1945!s0$F20H:3p=:P4g0000R=g00b1R>P>g00bQR?P:P5g03T[P3H07g00c1R@K0Mp=6!wi+!s$'p=NP1P=P>P>P?!vz%L0np=VB1O!u&$!st&0gU!st$p=mP5!sV+3P!s~%o!s:/J1Pp=_P4!s8+5P3K0mp=Up,5HCEILR=p,1sR@+1VS01&1U@RAp,2XCRBp,2XBRC40lS02p,1mRD-0`@S0321T@DS04217@DS0520w@DS0620k@D%23S07g01YP,Y3'3REB0Y@D5B0T@D5B1S!s+$F@D5'335[^T:g01Z^RF&16ARG9LF3RH20zD5[]?&0vARI$0JRJ-0ND&0jARK$0JRL-0ND3535S08PDg00>JRM#0RN#0RO#0RP#0RQ#0RR#8RS#B&0g@RT#XRU%s7RV'ZRWPD%0R!sF$X#B%0R#TRY#0S09#8RZ#XR[&0_@R\#XR]1Z]V3@R^PD%4MR_#4R`#fRa#0S0:#}S0;#Bp,2stRb$04&03bRb,a9%R2Rc#eRd/ZVRe3KS0<%4P#7Rf#BRg%4NRh#0Ri#4Rj#[#7Rk#BRl5EDADDle%4jRj#0#7Rl#B%4hS0=#0#A#7Rh#B5ED&1=@Rm%4j#c#7Rj'1Rn%0_Ro#0Rp#0Rq$0F#7Rr,1mS0>5EDRsP8PDP\&0Db$0CH0E'3S0?'335CWCWCWRbQ01Q02Q03Q04Q05Q06Q08PDP6g03UB%A`R`#4Rt#4#>#>S0@!s/'A#>#>#8#R$0BRu&0BcRc&0x@#XRvg03VMRw/]V9@]]9@d[3@5@UC;S0B%0q#}#B%8QRQ5|DS0C!t;&W`&04ARq&03ARx,a9Ry;KeS0DC;S0EPDPgg03XlRgPfCHS0FPDP6PgPeC;S0GPDg03Z7Rg,16g03[@RzPgCHS0HPD116zg03\DRgPzCHS0I!s:$g&0qARg&0pAS0J&0oAS0K/]V3KPD%4p!w$$p#Bg03]KRzPpCH!t@$zPeC;!t=$^T,161a;L&0OLRz:0A:2B0@:z2&0?K;K!sp%Aa#7Ra!sn$_YRzPa!sn1%f`#7Rz!sF$`cRaPz!sF&a%8NRN%fiS0L#8Ra'u%RQ$0>%8Y#R!s-$M$0=$0<g00ecS0M#J$0;RY&0:P$0iRQ&0=2R6%sQ9CQ69CQ63C+0h;@V3@']C;!xr%35CWS0NPbQ0BQ0CQ0EQ0FQ0GQ0HQ0IQ0NPDPm&0f@RQ#XPVCtS0OPDPQ%8PRz1ZcVC;S0P!s8$AO#71]m!s8$QPDPmPz&0e@RO&0d@Rp;K!s@$R!s@$a&0<6/ZVR6C;S0SPDPmg027jP!s6$TPDg0296Ra,1mR{1a;J#X&0OJR|!w'+|2&0?I!wu$CtS0UPD11{Sg02<PR{/SaPSCHS0VPD&0c@g02=XRa'1g02>cR|/S{PaCHS0WPD11m|g02?kRaP|CHS0X!tp%!tY%YPbQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0Y!|q+xR6!|s%Ra1bzy,1\1Sqy,bz!{N$Zg03amR|&099B0b9x5208933=PD%h5R{%r5R}&0a5%\4;KV5K{!uJ'3bLR~PSCHCW[^y9]zS0[PbQ0ZQ0[fKQ0220^A520]A5'3\E^T:S0\&0\A=`:C,q:S0]20[A5\H^?FS0^ALF5GRE%p1%p4'MA=F<1[\E[^wF!sG$_&0Z3$0XX?F>0WFG,aF/MyS0`1q:6S0a19yqS0bg03cXR6,IqRG%2qRE%8tS0c/b6,9q'3'QS0d206AI206AKP;P:Q00A`;JLRLH0V=`:B,q:g03dl&0U5g03f73=AL;3L&0K1&0S35L:'3Xv;-0R;&0K4=L:B+0Q[!u@$201A2$00%8`R`-01A$00202A2$05202A`$05g03gB&0PA'~%JYS00#JS0e!|9$#^!s$,RY5=|g03hM&1RA'~==|Yg03iX9=:gQ0Jg03jm5=:Q0Kg03lB5=:g03mRRg&09F&1QA:1NF5208F33=%p5R|$1M9=g41Y2|'3[^~F]{AL:3B21LA5[^|:AL:3C21KA5[^Y:'3353535'Q!s$%!#;'$KPbQ0\Q0]Q0^Q0_Q0`Q0aQ0bQ0dQ0KQ09#0RA!#:]$fRC#8RB,ITRF#gS!u&$n>/9TS0fg03oDR|,1T&1J=Rg7G~S0g1I\~R`#gS0hAj=\wS0iAG\wgRH1Im~R;#gS0jB1E=m~S0kAGm~gRL1IQzQ0L#0#}Rz9j=QAGQzgPT11|~R|P\PwPTP|PmP~!s-$QPz!s:$mP~!s-$QPz&1C@R@g040QRJ5j=AG@Jg!sS$@PJ!sK$@PJ!sW$@PJ!sg$@PJAL93x1I{~Aj={}AG{}g1bN~P{P}!sa${P}!sa${P}!sa${P}!sa${P}P@PJC{D<!s$%7F}35'Q[^U9AL95xR}%h1RJ%h4'M$1B%h<%r<PJ%r1C{[\}[^}9^U9!sz$QPzQ0=#A#8,uN,9O9F~O%2p1YpO35D<35!t2'!s0,D<35'QS0=PbQ0JQ0fQ0gQ0hQ0iQ0jQ0kQ0=P=!t'$4g00e7Rp#sRO&1ApRz&1@:RQ&1?:R}&1>:RJ20H:2R@%:ZR{3621<J?R?P3!sb$=JR|g00=jRK+0G21;34==|KdB15:25H14RKb1b2b3%2ZR|P3b0192~RIeI13AFZmLP=P\Pwf6RtPOPzPQP}%TC#7RC#:96J@P?P!sg+C!se&weI12Q0:#c$0F#N#7Rw?F\H1~9xRx$11%\xRx#21P\~%2\S0:%2`\I[1PTBR`%2T%2B%2F[[RF1Pq61926%2G[\E1Pm~%2mS0L%2;\I[POPz1l:5S0lP}PJ1d:MRM96J@RI&0}>R>PICV!to,X::Q07%25[^::P3Pxf5RxO2b0b4b5b6b7bx%2yRyePyQ0@#0#>#>#T#N!u8$yQ0A!s3+I,9g7Fg1IgZS0A&0|=R;11gZ,Y;5Fg'QS0@'3R;%AARA#[#A#>#[!sr&7&0{gR~%>A#>S07!s>,,9~3FS0m&0~=&10=COQ0m,3;R;eP;f]S0nPD%4o#A#c#[!s{$c#A#7R;/1SR=PU1]CVRV,Z]9@[]R]9@vd9@ucRdCtP0A`7Wd9DD=R[ADD=WR~PDP=%xW#\PdC;S0o'3RA[RGP[\APGP8PDP=PWPdDyP5n2111000010120!s#%PGP3P5O1S0pPAP0P~Q0o11;XRA=DD^RGQ0;,1;S0;Q0D5DDS0D11;fRd11;kRW5ED!tW$WeS0q11;lR611;hRB5EDR913saS0r'3S0s'3S0t'3S0u'3S0v'3S0w,3~S0xP3Q0oP0A@cve9@UuRu=`7]9DD=S0yADD=uRU!u[%u#\P]C;Rv'3Rc[ReQ0y\cPe!u[&uP]!u[<eP3feO1PcP0PUPvQ0xP3P0%\Y,1=RYA`7^V5DDR7ADDY^RcPDPY%x^#\PVC;Re'3R][RuP7\]Pu!t<$YP^PV!t<<uQ0pP]P0PcPe!t9$1PmZR0Q0L1ImZ#2\|[R]Q09#8Ru,PqRV%2u1IquS09#2[\EREP`PF1PgZRY%2gQ0A!sZ%81P\ZR7Q0:1I\!sn&|!~'+:;R;%:X'?%:SS0:,?;Q0:'?'m,oJ!|J,11=SR=,MARSP3!|@-8PSP:P=ADD3^XA:P4PAP3EnPGP~Q0wf?PGQ0vP3Q0DQ0ufpP[Q0tPDPd1SkfRAfoP0P]PVP!u0$PYP8P7P!ti-fS0t,?;S0u!#3q2d!tT20P]20yNXS0D1Y2NS0v%2X1uNXRf,Y2[R^[S0w%2NR=g041YRSB18NX5UWDS0:%2f\S^D=R=!tY4xg04252192N+0GQ0veO1R2P^!tr'Q0u%:kRkQ0t5v:RS'?RX%:N&0:R61::RR56!vd0dARN/9f!u4$>!u6,b>bC!v%?A6J@S!uv/A!uv1FwAEDdN!si?1?;k/mX!xD1MWNRX!vi2XP:PNAEDd3XA:P5PW!x?$[P3b=b;b=Q0qQ0sfnP9Q0rPDP61ShlRWfm!x9AlRl,?;Rd!x736!x75!yC$wQ0:P!wV5!wA-%:hRh=v!t$%dRd=6JR!w1/6W!w1\l!tp/W!w166!w1Ch/md!w12BNR!zt3d!w1&6!w1&B!w1$9!w1'PsPaPDPn1SrjRBfa!tB7p-0R6POPzQ!#;K$A6J{M1_J15UJP>%:jRN,?M!w>%!#;S1W@AFZ35115j#2[^::^@6P3AGmZgPmfNRhO!waSQ0e,z:Q00!s+$M,z:60I!s&$g00fB+0u=CpOPzP:P:P:1l:<PxPQCiPx!s4$xP1PQCiCiP51l:4CiP}PJ%:y1d:PRP56J%:I96JP5UJf7,_J5UJf8!s-%P>PJ1?M{=6JPP>PJ%:w1d:i56Jf9Ri!sJ,Q07#A!#<a&RP#:1d:o56!sB$f:Ro,_J1d:_96J@f;!s]%!vg&rR>=v:NRN!z'+CV!s$'!vu0XP:XQ:XR:XS:X@6XL6XM6XN6XO6191I9Fy1/3x/3tAG5Z<AFwti19Pxf<%2xf=3511xj?GBf[[[[!w\$P:^Q:^R:^S:^@6^L6^M6^N6^O6P3Q0c/bu,9qQ09#gAG\CgQ0mQ0@P\PgPTPqPmPhfSfPfZQ0nO?!{rUN!{r/B!{r311nBRN9EDn!sn;!zV$1?M>!{x3X::113r113j/1B'M!#Bs$mO1!t0/Q0>/MN!|5&n!|5%Q0>!|6$s!|6'f_CO!s$/b<b;X9eX<cP5P3O2n200!#<\'!s/$00!sJ$<vX9U!sJAW9XB~!sI>Bb;bBPDQ0;Q0<Q0qQ0?,3955[CW95~GRGePGebXPbebbbEbFW9XkLWFWjXdHWEWcWhWgWffVN=0tW9WrWqWKWJWIWHWGW9P3N<1DboW9W\XnafDJ0sWmWaWuWtWs!sP0oN>0rW9W`W_WWW^WVW]W<P<N;1GW9WiWlWZW[WpWep,2RQN:1Ho"). Qed.
End PreCells.

Section RSStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (ch : chunk) (d : depot) (lo cb : Z).
  Let st : ltac2:(zQ "10!jh9$0") := ltac2:(zQ "10!lr8@1$0?1s").
  Let mch : ltac2:(zQ "10!hjc$0") := ltac2:(zQ "10!ls0@1$0?2ch").

  Hypothesis RQ : ltac2:(zQ "30!mh5!hjc!mgc@5$2?5HCEIL?1s@3$0$1?3mch?2XC?2XB?1m").
  Hypothesis CHIN : ltac2:(zQ "30!mhc!mi4!u0@3$2$0?2ch@1$1?2st").
  Hypothesis SEC : ltac2:(zQ "40!m0!hj4!p0!mj1@3$2$0@1$3?2ch$1").
  Hypothesis QUAR : ltac2:(zQ "40!p0!mje!mkc!ml7@3$0$3@1$2?2ch$1").
  Hypothesis INIT : ltac2:(zQ "40!m0!n5!p0!mm0@3$2$0@1$3?2st$1").
  Hypothesis AX : ltac2:(zQ "30!jp2!mn2!jgb@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!mne@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!lh8!ms9@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!nh2@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!ni2@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!lh8!nm9@2$1$0?1m").
  Hypothesis LO : ltac2:(zQ "20!nr2!ho2@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!h9!hnb!ho2!nrb@2$2@2$1?2lo+ji0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!p0!h9!hjc!ns9!nrb@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis ST : ltac2:(zQ "40!h9!lh8!ogf!nrb@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis TP : ltac2:(zQ "50!p0!h9!hjc!ih8!nrb@3$0$2@2$4@1$1#k0?2tp$3").
  Hypothesis OK : ltac2:(zQ "60!kt4!lh8!oh6!ohd!oi4!om5@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "e0!h9!in4!omd!p0!jtc!lh8!oh6!ohd!or3!orf!pg3!pk8!pl3!jc@3$3$4@3$8@1$6?1s@1$7?1s?3msF@7$a@hf$9?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$1?2cb@1$1?3mch?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$c@1$0#k0+mrjpc?2fc@1$2@1$d@1$0#k0?1m@1$b$5").

  (* [comment removed for export] *)
  Definition rs_model_clause : ltac2:(zQ "10!jh9>3stX$0P") := ltac2:(zQ "c0!jh9!m7!ji2!l9!ina!jmf!jo2!jo9!me!jp2!p0!jp8\3stX$0>3stA$0>0@2$5^1?2st@2$4$0\4stA'$0@2$4@1$1$2\2ev@1$1$2@2$9@3$a@1$7@2$3$0@1$1$2@2$b^4?3mch@2$6@2$3$0@1$1$2@4$8$0@1$1$2^2^1@2$5^2^5").
  Definition rs_gpost : ltac2:(zQ "20!jtc!jud>0$0>0$1P") := ltac2:(zQ "20!kj9!kp5@hc$0?5HCEIL?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1s?1d?2lo?1m?2mo?2XC?2XB?2XB$1").

  Section At.
    Variables (idx : nat) (h lsth : schunk).
    Hypothesis HIDX : ltac2:(zQ "60!pld!jo2!jo9!p0!pm6!pmf@3$3@1$2$0@3$5$0@1$4?2st?3idx@2$1$0?1h").
    Hypothesis HMAP : ltac2:(zQ "40!p0!hjc!ps4!pt3@3$0$1@1$3?1h@1$2?2ch").
    Hypothesis HLAST : ltac2:(zQ "80!pld!pm6!jo2!pu0!jo9!p0!pvb!pmf@3$5@1$4$0@3$7$0@1$1?2st@2$6@2$3$0@1$1?2stN1@2$2$0?4lsth").
    Let T := a_thr s.
    Let CTX := a_ctx s.
    Let sb := a_sb s.
    Let pa := a_pa s.
    Let nch := zlen (as_sec st).
    Let nres := as_n_reserved st.
    Let U := ch_user_beg ch.
    Let a := sc_map_beg h.
    Let msz := sc_map_size h.
    Let lst := sc_map_beg lsth.
    Let chunks := List.map sc_map_beg (as_sec st).
    Let l1 := secdel_l1 (as_sec st) idx.
    Let st2 := remove_map (set_sec (del_state st ch) nres l1) a.
    Let L2 := rs_L (a_L s) a msz.
    Let sN := mkAst st2 T CTX (a_fsb s) L2 (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

    Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
    Let WQ : WFQ st (mch :: XC) XB. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
    Let MEM : ARmem s m. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
    Let SND : List.NoDup (List.map sc_map_beg (as_sec st)). Proof. pose proof WQ as WW. ndestruct WW as (_ & _ & _ & _ & _ & W6 & _). exact W6. Qed.
    Let HIN : In h (as_sec st). Proof. eapply nth_error_In. exact HIDX. Qed.
    Let LIN : In lsth (as_sec st). Proof. eapply nth_error_In. exact HLAST. Qed.
    Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SECP & SEC2 & TCX).

    Let ENT : sc_map_beg h = a /\ sc_size h = rq_needed (compute_req (ch_used ch)) /\ msz = round_up (sc_size h) kPageSize + kPageSize
              /\ find_sec_idx (as_sec st) a 0%nat = Some idx /\ rq_primary (compute_req (ch_used ch)) = false /\ in_primary st (ch_alloc_beg ch) = false
              /\ ch_rz ch = 2048 /\ U = ch_alloc_beg ch + 2048 /\ mch = ch_alloc_beg ch + 2032 /\ ch_alloc_beg ch = a + kPageSize
              /\ ch_lo ch = a /\ ch_end ch = a + msz /\ 1 <= ch_used ch.
    Proof. eapply rs_ent; eassumption. Qed.
    Let BND : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
              /\ 7430144 <= CTX /\ CTX + 160 <= aceil /\ 7430144 <= pa /\ pa + 8388608 <= aceil
              /\ 7430144 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7430144 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
              /\ 7430144 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil
              /\ 1 <= nch <= nres /\ nres <= 1032192 (* [comment removed for export] *) /\ 7430144 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
              /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 7430144 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
    Proof. eapply rs_bnd; eassumption. Qed.
    Let BANDS : hidden ((T + 4096 <= 65536 \/ (7430144 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                     /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                     /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                     /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                     /\ (d_sb d + 8 * 32768 <= 2147446784 \/ 17594333495296 <= d_sb d)
                     /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                     /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                     /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)
                     /\ (lst + 8192 <= 2147446784 \/ 17594333495296 <= lst)).
    Proof. eapply rs_bands; eassumption. Qed.
    Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
    Let PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz CTX 160
              /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 32768)
              /\ (forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
    Proof. eapply rs_pnew; eassumption. Qed.
    Let L1IN : forall y, In y l1 <-> In y (as_sec st) /\ sc_map_beg y <> a.
    Proof. eapply rs_l1in; eassumption. Qed.

    (* [comment removed for export] *)
    Ltac post L := first [ eapply L with (idx := idx) (h := h) (lsth := lsth) (spv := bv_unsigned sp)
                         | eapply L with (idx := idx) (h := h) (lsth := lsth)
                         | eapply L with (idx := idx) (h := h) ]; eassumption.

    Lemma recycle_sec_arepq_at : ltac2:(zQ "70!kt4!lh8!lla!lpb!jtc!jud!lqc>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
Proof.
      (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay
         whose first error was `Illegal application: the term "proj1" ... cannot be applied to
         "nonvm_same mo mo'" and "vm_maps (m_vmmaps mo') = map_remove (vm_maps (m_vmmaps mo))
         (wz a) /\ ..."`: it destructured rs_model's PRE-REVISION vm_maps conjunct.  rs_model
         was restated in an earlier repair (As/AS_SecRecycle2.v:58) so that conjunct now reads
         `vm_maps h' = maps_subtract (vm_maps h) a (a + msz)`, and the replay's `@recycle_sec_sreach`
         application no longer matched either.  The proof is now plain text, transcribed from the
         plain-text sibling a donor tree:projects/openssl/echconfiglist_parser/proofs/
         lib/As/AG_RecycleSec.v (390 lines, 0 replays), whose RSStep/At section is name-for-name
         this one.  NO STATEMENT CHANGES.  The rs_model conjunct is only ever read here through
         AG_RecycleSec2's amodelx_after_rs / avmx_after_rs, which were ported in the same series
         and already speak maps_subtract, so nothing below has to know which form it is in.
         Every literal is THIS tree's own, read out of its own encoded statements:
         69632 (= 0x11000) and 2^40 are As/AS_SecRecycle.v:35's AR bound; 6128 is its DISJ:50 and
         CHDR:64 offset; 2^20 its NCH:43 bound; 2^47 its DISJ bound; 6955400 and 6955312 are its
         TPR:38 and RNG:39 bounds (the Bs twin's own are 6942920 and 6942832, the only two
         characters in which the twins differ here).  The AINST cell addresses are never written:
         SB32 .. GST are passed in the `AINST + k` form large_cells_of_arepq gives them and the
         kernel converts, and hVISE and hCHDR are obtained by rewriting VISE and HD rather than
         by restating them, so neither the return PC nor the chunk-header cell list is re-keyed. *)
      intros K. pose proof BND as B. pose proof ENT as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
      destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0).
      destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
      pose proof (proj1 AK) as AK'. destruct AK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). destruct K10 as (_ & _ & K10c).
      (* akernel's second conjunct is the pair (nonvm part, alloc_top = hceil); AG_RecycleSec2.v's
         amodelx_after_rs reads the same pair as (K2a & K2c).  Taken by position, not by name, so
         no constant of the ceiling is written here. *)
      pose proof (proj1 AK) as AKz. destruct AKz as (_ & (_ & ATOPc) & _).
      placed. pose proof (SECP h HIN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). pose proof (SECP lsth LIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
      fold a msz in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9. fold lst in R1, R2, R3, R4, R5, R6, R7, R8, R9.
      fold T CTX sb pa in S1, S2, S3, P1, P2, P3, T1, T2, T3, X1, X2, X3, D1, D2, D3, D4, D5, TCX, Q5, Q6, Q7, Q8, R5, R6, R7, R8.
      destruct PNEW as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
      (* The secondary map is at least one page of redzone over a secondary-sized request, and at
         most ASECMAX (As/AllocRepX.v:55, this tree's own 2^32 + 2^14). *)
      assert (MSZ : 0x11000 <= msz < 2 ^ 40).
      { pose proof (secondary_needed (ch_used ch) ltac:(clear - E13; lia) E5) as ND. rewrite <- E2 in ND. pose proof (K10c h HIN) as KS. fold msz in KS.
        rewrite E3. rewrite E3 in KS. unfold ASECMAX in KS. unfold round_up, kPageSize, kMaxSize in *. clear - ND KS. Z.div_mod_to_equations. lia. }
      destruct (large_cells_of_arepq s _ _ m RQ) as (SB32 & INST64 & NRES & SST & MTX & GST & TST & PA).
      pose proof (senv_of_arepq s _ _ m RQ) as SEN. destruct (renv_of_arepqx s _ _ m RQ FXR) as (g & b244 & REN).
      pose proof MEM as (_ & _ & _ & SECR & _ & _ & CHR & _). destruct SECR as (_ & _ & SHDR).
      pose proof (SHDR idx h HIDX) as [HDR _]. pose proof (SHDR _ lsth HLAST) as [LHDR _]. fold a msz in HDR. fold lst in LHDR.
      pose proof (CHR ch CHIN) as CR. destruct CR as ((b1 & actx & HD & Hb1 & Hb1') & LC & STQ & JR & PL' & PR' & PH'). rewrite QUAR in HD, STQ. destruct STQ as [JU SHU].
      rewrite SEC in PH'. fold U in HD, JU, SHU, JR, PR'.
      assert (LEN : length chunks = length (as_sec st)) by (unfold chunks; apply length_map).
      assert (ZL : zlen chunks = nch) by (unfold zlen, nch, zlen; rewrite LEN; reflexivity).
      assert (NCHL : Z.of_nat (length (as_sec st)) = nch) by reflexivity.
      assert (LTI : (idx < length (as_sec st))%nat) by (clear - B; tauto).
      assert (APART : forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> a + msz <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= a).
      { intros sc Hin NE. pose proof (N8 sc Hin NE) as D. unfold disj in D. exact D. }
      pose proof (compute_req_facts (ch_used ch) ltac:(clear - E13; lia)) as (_ & _ & RR & RR8 & RN & _). cbv zeta in RR, RR8, RN. rewrite E5, (secondary_rz _ E5) in RN.
      assert (MSZU : msz = round_up (rq_rounded (compute_req (ch_used ch)) + 4096) 4096 + 4096) by (rewrite E3, E2, RN; unfold kPageSize; f_equal; f_equal; clear; lia).
      set (rd := rq_rounded (compute_req (ch_used ch))) in *.
      (* The whole secondary map's shadow, assembled from the four poisoned/junk runs chunk_rep
         gives for a quarantined secondary chunk (As/AllocRep.v's chunk_rep). *)
      assert (SHDX : exists sbs, u8arr asegs m (sh a) sbs /\ Z.of_nat (length sbs) = msz / 8).
      { destruct PH' as (_ & _ & PH). destruct PL' as (_ & _ & PLz). destruct SHU as (_ & _ & SHUz). destruct PR' as (_ & _ & PRz).
        unfold poison_bytes in *. rewrite E10 in PH. replace (a + kPageSize - kPageSize) with a in PH by (clear; lia).
        exists (repeat (b8 kAsanHeapLeftRedzoneMagic) 512 ++ repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ch_rz ch / 8))
                ++ repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh (ch_used ch)))
                ++ repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((ch_end ch - (U + round_up (ch_used ch) 8)) / 8))).
        assert (A8 : a mod 8 = 0) by (clear - B; Z.div_mod_to_equations; lia).
        split.
        - apply (proj2 (u8arr_app2 m _ _ _)). split; [exact PH|]. rewrite repeat_length.
          replace (sh a + Z.of_nat 512) with (sh (ch_alloc_beg ch)) by (rewrite E10; unfold sh, kPageSize; clear - A8; Z.div_mod_to_equations; lia).
          apply (proj2 (u8arr_app2 m _ _ _)). split; [exact PLz|]. rewrite repeat_length.
          replace (sh (ch_alloc_beg ch) + Z.of_nat (Z.to_nat (ch_rz ch / 8))) with (sh U) by (rewrite E8, E7, E10; unfold sh, kPageSize; clear - A8; Z.div_mod_to_equations; lia).
          apply (proj2 (u8arr_app2 m _ _ _)). split; [exact SHUz|]. rewrite repeat_length.
          replace (sh U + Z.of_nat (Z.to_nat (nsh (ch_used ch)))) with (sh (U + round_up (ch_used ch) 8))
            by (rewrite E8, E10; unfold sh, nsh, round_up, kPageSize; clear - A8 E13; Z.div_mod_to_equations; lia).
          exact PRz.
        - rewrite !length_app, !repeat_length. rewrite E12, E8, E7, E10. rewrite MSZU. unfold nsh, round_up, kPageSize. clear - RR RR8 E13 A8. Z.div_mod_to_equations. lia. }
      destruct SHDX as (sbs & SHD & SHDL).
      assert (hSPA : hidden (bv_unsigned sp mod 16 = 0)) by (constructor; exact SPA).
      assert (hAR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40).
      { split; [exact Q2|]. split; [exact Q3|]. split; [clear - B; tauto|]. split; [clear - B; tauto| exact MSZ]. }
      assert (hSBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a)).
      { constructor. unfold disj, kSpaceSize, kPageSize in *. clear - N1. lia. }
      assert (hSBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil)).
      { constructor. unfold kSpaceSize, kPageSize in *. clear - S2 S3. lia. }
      assert (hTPR : hidden (6955400 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP)).
      { constructor. rewrite TP. unfold ATP, AIMG_TOP. clear. lia. }
      assert (hRNG : hidden (6955312 <= ATSD /\ ATSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj T 4096 /\ T + 4096 <= aceil /\ T mod 16 = 0)).
      { constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T1, T2, T3.
        split; [clear; lia|]. split; [clear; lia|]. split; [exact X2|]. split; [exact X3|]. split; [exact T2|]. split; [exact T3|].
        clear - T1. Z.div_mod_to_equations. lia. }
      assert (hPLC : hidden ((CTX + 160 <= T \/ T + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= T \/ T + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= T \/ T + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a))).
      { constructor. destruct TCX as (TCX & _). unfold disj, kPageSize in *. clear - TCX D4 D5 N2 N3 N4. repeat split; lia. }
      assert (hPAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0).
      { split; [exact P2|]. split; [exact P3|]. unfold kPageSize in P1. exact P1. }
      assert (hNCH : zlen chunks = nch /\ 0 <= Z.of_nat idx < nch /\ nch <= nres <= 2^20).
      { split; [exact ZL|]. clear - B LTI NCHL. lia. }
      assert (hIDX : nth_error chunks (Z.to_nat (Z.of_nat idx)) = Some a).
      { rewrite Nat2Z.id. unfold chunks. rewrite nth_error_map, HIDX. reflexivity. }
      assert (hLNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst).
      { replace (Z.to_nat (nch - 1)) with (length (as_sec st) - 1)%nat by (clear - NCHL LTI; lia). unfold chunks. rewrite nth_error_map, HLAST. reflexivity. }
      assert (hLR : aapp lst 4096 /\ lst + 4096 <= aceil).
      { unfold kPageSize in R4. split; [eapply aapp_sub; [exact R2| clear; lia| clear - R4; lia]| clear - R3 R4; lia]. }
      assert (NELAST : Z.of_nat idx < nch - 1 -> lst <> a).
      { intros LTn E. assert (EI : idx = (length (as_sec st) - 1)%nat); [| clear - EI LTn NCHL; lia].
        apply (proj1 (NoDup_nth_error (List.map sc_map_beg (as_sec st))) SND idx (length (as_sec st) - 1)%nat); [rewrite length_map; exact LTI|].
        rewrite !nth_error_map, HIDX, HLAST. cbn. fold a lst. rewrite E. reflexivity. }
      assert (hPLCL : Z.of_nat idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= T \/ T + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst))).
      { intros LTn. constructor. pose proof (APART lsth LIN (NELAST LTn)) as D. fold lst in D. unfold disj, kPageSize in *. clear - D R4 R6 R7 R8. repeat split; lia. }
      assert (hLSTA : Z.of_nat idx = nch - 1 -> lst = a).
      { intros E. assert (EI : idx = (length (as_sec st) - 1)%nat) by (clear - E NCHL LTI; lia). rewrite <- EI in HLAST. rewrite HIDX in HLAST. injection HLAST as <-. reflexivity. }
      assert (hDISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks).
      { apply Forall_forall. intros c Hc. unfold chunks in Hc. apply in_map_iff in Hc as (sc & <- & Hin).
        pose proof (SECP sc Hin) as (_ & G2 & G3 & G4 & _). apply aapp_env in G2; [| unfold kPageSize in G4; clear - G4; lia].
        split; [clear - G2 G3 G4; unfold kPageSize in *; acb; lia|]. intros LE.
        destruct (Z.eq_dec (sc_map_beg sc) a) as [E|NE]; [clear - E; lia|]. pose proof (APART sc Hin NE) as D. unfold kPageSize in G4. clear - D LE G4 B. lia. }
      assert (hSEN : SENV tp ATSD CTX T m).
      { replace tp with (wz ATP); [exact SEN| unfold wz; rewrite <- TP; apply Z_to_bv_bv_unsigned]. }
      assert (hLSTC : Z.of_nat idx < nch - 1 -> rw_cells asegs m (lst + 24) [C8 (wz (nch - 1))]).
      { intros _. apply (rw_cells_app asegs _ _ [C8 (wz lst); C8 (wz (sc_map_size lsth)); C8 (wz (sc_size lsth))] [C8 (wz (Z.of_nat (length (as_sec st) - 1)))]) in LHDR.
        destruct LHDR as [_ LH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LH.
        replace (Z.of_nat (length (as_sec st) - 1)) with (nch - 1) in LH by (clear - NCHL LTI; lia). exact LH. }
      assert (hCHDR : rw_cells asegs m (a + 6128) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz (ch_used ch)); C8 (wz actx)]).
      { replace (a + 6128) with (U - kChunkHeaderSize) by (rewrite E8, E10; unfold kChunkHeaderSize, kPageSize; clear; lia). exact HD. }
      (* VISE is rewritten rather than restated, so this tree's return PC is never written out. *)
      assert (MEQ : a + 6128 = mch) by (rewrite E9, E10; unfold kPageSize; clear; lia).
      pose proof VISE as hVISE. rewrite <- MEQ in hVISE.
      assert (hWIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x (a_S s) = true).
      { intros x Hx. destruct ASV as [_ V2]. exact (V2 h x HIN Hx). }
      assert (hHAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true) by (apply map_has_of_In; exact (ak_secmaps s mo AK h HIN)).
      assert (hNOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false) by (intros x Hx; exact (IL3 h x HIN Hx)).
      assert (hNOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false) by (intros x Hx; exact (ak_sec_noacc s mo AK h x HIN Hx)).
      pose proof (ak_zrsh2 s mo AK) as hZRSH. pose proof (ak_shrf2 s mo AK) as hHSRF.
      pose proof (ak_shmc2 s mo AK) as hHSMC. pose proof (ak_shna s mo AK) as hHSNA.
      (* Only the Variables of AS_SecRecycle's SecRecycle section are given positionally; the
         hypotheses are discharged by name, so a hypothesis this tree keeps and the sibling
         discharges (NR, ATOP) cannot shift the list. *)
      apply (recycle_sec_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 (wz cb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo a msz (sc_size h) (Z.of_nat idx) pa nres nch lst (nch - 1) ATSD CTX T sb (ch_used ch) actx chunks (b8 3) (b8 b1) sbs g b244);
        try exact MI; try exact ST; try exact LO; try exact HI; try exact hSPA; try exact hAR; try exact hSBX; try exact hSBR;
        try exact hTPR; try exact hRNG; try exact hPLC; try exact hPAR; try exact hNCH; try exact hIDX; try exact hLNTH; try exact hLR;
        try exact hPLCL; try exact hLSTA; try exact hDISJ; try exact hSEN; try exact REN; try exact SB32; try exact INST64;
        try exact NRES; try exact SST; try exact MTX; try exact GST; try exact PA; try exact HDR; try exact hLSTC; try exact hCHDR;
        try exact TST; try exact SHD; try exact SHDL; try exact OK; try exact hVISE; try exact NW; try exact NWA; try exact NOV;
        try exact hZRSH; try exact hHSRF; try exact hHSMC; try exact hHSNA; try exact hWIN; try exact hHAS; try exact hNOL;
        try exact hNOACC; try exact ATOPc; try (clear - B E13 MSZ RR RR8; acb; lia).
      cbv beta. intros msF' mo' P.
      destruct P as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & OK2 & VIS2 & MO2 & MU & WMO & MI2 & SEN2 & REN2 & ST2
                     & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & LSTC2 & TST2 & SH2 & GONE).
      assert (SPV : 0 <= bv_unsigned sp < 2 ^ 64) by exact SPR.
      assert (WSP : wz (bv_unsigned sp) = sp) by (unfold wz; apply Z_to_bv_bv_unsigned).
      assert (MU' : munch (rs_W lo (wz (bv_unsigned sp)) a msz pa nch lst T) m m') by (rewrite WSP; exact MU).
      assert (INST2' : rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]) by exact INST2.
      assert (NRES2' : rw_cells asegs m' (AINST + 112) [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]) by exact NRES2.
      assert (SST2' : stk asegs m' (AINST + 136) (AINST + 680)) by exact SST2.
      assert (MTX2' : rw_cells asegs m' (AINST + 680) [C8 (wz 0)]) by exact MTX2.
      assert (GST2' : stk asegs m' (AINST + 688) (AINST + 728)) by exact GST2.
      assert (NWL : entries_nowrap (a_L s)) by (apply (lazy_ranges_okb_nowrap asegs); exact (lzok_ranges OK)).
      assert (SL : forall x : word, in_rangesb x (a_S s) = true -> in_rangesb x (a_L s) = true).
      { intros x Hx. apply (lzok_ZrL OK). apply (lzok_SZr OK). exact Hx. }
      assert (AMXD : AMODELX sN mo' /\ depot_cov d mo') by (eapply (amodelx_after_rs s m XC XB ch idx h lsth d lo); eassumption).
      destruct AMXD as [AMX2 DCOV2].
      apply K. unfold rs_gpost, rstep_post.
      exists sN, y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros sc Hin; change (as_sec (a_st sN)) with l1 in Hin; exact (proj1 (proj1 (L1IN sc) Hin))|].
      split; [exact INIT|].
      split; [intros c0 _; reflexivity|].
      split; [exact OK2|]. split; [exact VIS2|].
      split; [post arepq_after_rs|].
      split; [post awin_after_rs|].
      split; [post flagsx_after_rs|].
      split; [exact AMX2|].
      split; [pose proof MO2 as M; unfold rs_model in M; cbv beta iota zeta in M; exact (proj1 M)|].
      split; [post avmx_after_rs|].
      split; [exact DCOV2|].
      split; [post depot_after_rs|].
      split; [post depot_placed_after|].
      split; [exact MI2|]. split; [exact ST2|].
      split; [post acompl_after_rs|].
      split; [post avis_after_rs|].
      split; [post pendz_after_rs|].
      split; [post alive_kept_rs|].
      split; [post alive_after_rs|].
      intros stA SBS. change (a_st sN) with st2.
      assert (EQ2 : secdel st ch = st2) by (rewrite (secdel_eq st XC XB ch WQ idx h HIDX HMAP); unfold st2, a; rewrite HMAP; reflexivity).
      rewrite <- EQ2.
      apply (cb_recycle_sec_eval stA st XC XB ch idx h SBS WQ CHIN SEC QUAR HIDX HMAP); rewrite <- ?HMAP; fold a msz mch.
      - unfold kPageSize. clear - B. tauto.
      - bands_as (_ & _ & _ & _ & _ & BA & _). unfold addr_is_in_mem, kLowMemEnd, kShadowOffset, kHighMemBeg, kHighMemEnd.
        clear - BA B MSZ. acb. repeat split; apply orb_true_iff; (destruct BA as [BA|BA]; [left| right]); apply andb_true_iff; split; apply Z.leb_le; lia.
      - unfold in_primary. apply andb_false_iff. rewrite E9, E10. unfold disj, kSpaceSize, kPageSize in *. unfold sb, a_sb in N1. unfold st.
        clear - N1 MSZ. destruct N1 as [N1|N1]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
      - intros h' Hin LE. destruct (Z.eq_dec (sc_map_beg h') a) as [E|NE].
        + left.
          destruct (In_nth_error _ _ Hin) as (j & Hj).
          assert (EJ : j = idx); [| subst j; rewrite HIDX in Hj; injection Hj as <-; reflexivity].
          apply (proj1 (NoDup_nth_error (List.map sc_map_beg (as_sec st))) SND j idx); [rewrite length_map; exact (nth_error_lt _ _ _ Hj)|].
          rewrite !nth_error_map, HIDX, Hj. cbn. fold a. rewrite E. reflexivity.
        + right. pose proof (APART h' Hin NE) as D. pose proof (SECP h' Hin) as (_ & _ & _ & G4 & _). unfold kPageSize in G4.
          rewrite E9, E10 in LE. unfold kPageSize in LE. clear - D LE G4 MSZ. lia.
    Qed.
  End At.

  (* [comment removed for export] *)
  Theorem recycle_sec_arepq : ltac2:(zQ "70!kt4!lh8!lla!lpb!jtc!jud!lqc>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec ()) ["HCW"; "RSStep"] "##N;p'0h04HIDXh14__x1h21ni001nh31Hh43idxh57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;1ah<4cstrh=1hh>7heq_mchh?1lh@3s12hA1EhB2ELhC3H12hD5HLASThE4HMAPhF1KhG2NEhH2WQhI2_HhJ7__sat12hK!s0&3hL1ei011ehM2l'hN2l0hO4lsthhP1mhQ3mo'hR4msF'hS1oi021ohT1xi031xhU1yhV3z12i041sp&0p;2p;4p;3p;6p;1p;<p;7p;5p;Bp;8g04<nk20UTg04>;j2gTg074Nj4XTg00SMj37Tg043fk60TTg00iEk10HTg00jIk30@Tg02TgR0j1YTg02LVj1zTg02VIj1`Tg06\@j1jTg02Xdj1fTg04B1k10OTg00A\k10GTg00K;k10ETg02WVj1dTg04C;j2]Tg00IbR1j24Tg04DFk30:Tg02Ugj2LTg00=0j30j1^Tg00Bjk103Tg04EUj1yTg04Fdj2xTg04H1j1wTg002Ij1ATg00FPj1!tA$`0j1sTg02f4j1pTg00W3j1>Tg006Bj26Tg004Oj1bTg00Rmj1eTg00?^j6J!tY$Ij3MTg07[gk20STg00Nhj1DTg03;2k10RTg07\Fk30Q!s0$fR2k20NTg07]BR3k20MTg046Wj28Tg05Clj2PTg009_j2!ud$YnR4j19Tg01E_j2;Tg00H8j2ITg05Hkk20DTg05INk30CTg078nl<\Tg03=\j1[Tg05DCk20!s_$J?j2Z!wE$@R5j2CTg02hOj2!u0$2nk108Tg04L<k207Tg03>Ak20!u|$J[k205Tg00OGj2!x$$P0k104!s0$Nk202!s0$ok301Tg00QXj3!yD$RAj2N!yj$mj2WTg00TKj1{!s/$ij4|Tg00UGj1}!s/$ej1~Tg03QCk600Tg00VPj2U!wa$Xj2VTg00X;j3vTg03GRj3uTg07:^j7tTg00YIk109!s0$kj2rTg00ZMj2qTg00[9k30<!s0$Xk40=Tg05BDj4_Tg07?`R6k20A!wa$_j1oTg001Nj6FTg07^DR7k20B!s2$^j5m!vv$ek30!sE$_Aj7lTg03Kmk50ITg07`Zk70JTg07amj6kTg02^0k30KTg02nhk20L!u/$8lBa!uJ$^j4cTg00^`j7i!ux$gj7hTg00_Dk80PTg03SPR8f0R9'Lp=5f3R:f2R;f1R<5M8;09p=2g00`HR=?0<9p=1%A9#Ap=?16<9,6;p=BAM8<9p=QB0K!s/$=20L89p=3g03amR>P>P>P=P=P=g07>]P4!s$$1g07?=f5R1f4R?P:P;P<P9MBap>0?P!s[-P6!sX%f6R6g07@@P1P!sV2>g00cQR@/C9p=<P=P<g00gUP9Ccp=O!s4$00RAg00b1RBPBg00bQRCP9g00c1Fip=@P;PAPBPBPCP<P9Fhp=T!sn%3T[!sn%KP:!sI+!tJ$L0Pp=R!tu$7P4P5g07c1!tk0<\p=ng07@gg07An20U<9g01XNR5g07<HR7p,1QRD1g;<CX[]Q]Rp,5HCEILp,1sREp,3mchRFp,2XCRG57=RHp,2XBRIp,1mp,2RQJ0T&0HE@0@HIP>P8%Y8!sK$stRE#zRJP<%59C2RK%`9p,2chRL#jRM'1RN%f9RO&0OL$0GRP$0ERQ'1%d9g03bLRR,]O/4R'1%Y>ROg00ecRS:0:JMRT1L><30g00=JRU&03Pg00_hRP30%yLRV,xE=0UP%wLg00>JRP#ARW#A#?RX#?RY#A#?#?#ERZ'1%sL14VZ'1%pLRZ%>P#>!s$+!sK$,4V'13B3BRV'63BR[3BX=8X4>P5P7PDp,3msFp,2mo'gCXRDPKPNP[PD%`</1M%f;RM/1Q%d;1]MR!uF$1L>:90OT/6V3B%b8RV%e8RT70JROPVPJPHP9P6%51RRC2X?VP:PTP9EJPHPTP1%5?C2P>!s3$9%56RMC2g07QKRQ]0P6AM8TSR[=0HRPHP[P0P8p-0R0P9PQg041Yn101102000210!s#$XLHR[g07VmRRPM!t8$Q20SQ9RMb3W0PHPT%D9f7RN#5C2PH%D<,QTP[PRf8RR#5!sX%P!sS$X4>P9O1n01!t'%20010100P9O1b0WA&0ROROePOB0Q8J9A789TRO,=<90VJX;8-0N8RMXMVRQ-0MVP3PVPQPDP9P2P81=;O!sN&PDP91=?!s5$PVA78<!sm$1RDPHP9%39%DSR2'8%5;RQ!vd%>%31R3%3O'PR[PHA78;TR7,=6R51892PQC2X2>1:=Z11FZRZeRFPZ%36R\1P\2R]/82R^50>%9\R_%EPR`,4_Ra/;`,I@Rb'1P>P=%^>P4%^=%9<%99'1A0><920D<940CXU>XT>P\P_1:=_R4P^Pb1;<9,I@XP=X2=P]PaP\P_P4P2P`1:=`R4J0?P2P`P4K0>M<\%[\%<_%3NR_#9R4/4`/;`Ra-0;@1Z@a1I@aR]/1a'61Ca@A0=]@'6'S%3R#9!sS%,I@P=&08Yp,2sp+07RY%EXRX+06RR%<Y%<X205YX#<[[RXg00e7RY%D2R]#D,G=&04P-02=1G=]R]601=1G=SRa5H=Rb5H=g00fBRc'N1G=2=H=a9H=]/Nc1Nbc%eYRc57Y57Y37%bYRYP=1W=;P<%{=C|%}=Rb%~=R]P]!#5B'!s0,?J001U=WRW1U=PRP1V=`RA5v==u=ARA'O,@]5T]1V=@Ra,KA,@]1OWa!s<%Ft&09BRBP]1KaP,@]PB1OPW,@]CRCR1r]CRCP9P;g00=jRW,:U1q9;=0UWdB0<=@<H0=RWb6b8b9X1=X:=X70149!wE$U,1<,6;1CU@A0=<!w8%<<11;:[[^1=^:=^70P9f;#3#9R0!wO&Z@P;P0P:P?O5b5bKbVbCb<C_b>1P32/8290>3P>P\!zl$:TRT,=NP9%5:R:!zk$PH18\\,Q7A0H9:XSHP>PS!~x%P!sH%1:HQ20A\\%o\EF1Q5\P8P6P7P\PFPZ20B__1C44P_P41:=4RZ!z;$ZEn%[_%<4PRPXPcPY1W=<Pb1KP!vX$CP!v#,1C99^1=P9f:#3#9O1b5bJ!u;%DmEFP^P9EJb3PHPD18[2%5<R[C2e%3DB0F81OEFPJP9EFPHPJ%3J/82P[C2f?f>P;f=f<P9fAFlbDWBXO8P<P9O2n2001104000121103101X@MXNV!sF<4b@bGWIWEX0KI0I!#7g%EPGPIPLP9p,4CHINp,3SECK0JEkbHWFo"). Qed.
End RSStep.
End HCW.
