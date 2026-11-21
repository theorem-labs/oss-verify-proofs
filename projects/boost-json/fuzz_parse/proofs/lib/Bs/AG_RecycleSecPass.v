(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proof terms re-threaded to the revision's definitions, lemmas added for the revision. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit AW_LargeAlloc1 AW_PoisonRemap1 SecLazy SecLazy2 AS_PoisonRemap AS_SecRecycle1 AS_SecRecycle2 AS_SecRecycle
     AG_WFHit AG_Malloc AG_Malloc2 AG_MallocModel AG_MallocLarge2 AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_RecycleModel AG_WriteSet AG_RecycleDefs
     AG_RecycleSecModel AG_RecycleSec1 AG_RecycleSec2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_RecycleSecPass () := KReplay.lz_vm "#'<[C46Stdlib9micromega5Tauto5eKindI!sE;8GFormula00!si+5Lists4!s+#6nth_okC47Corelib4Init5Logic8eq_ind_r!s_78map_consK!sa+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!to19Datatypes4prod!sF?list00K!sfA1!uY72In!s=77ex!s2#bI!vR73an!t\5!sA%2ex!wJ9>!sw&_!s-%C!ty;3fstC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqb!sp=snd!sC<4andbK!u89q01C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib8PropExec;!td%_reflC13~~~K!va<1K!va;1!uy;?!s<25State7!zf#hasI!uG;!yQ>bool!yQ?!sF$1!{gG3I5!xf'FSets<FMapP!sD&;!s/'Map4tree!y=#!t|66!}F%!wGT2Nd;ex_introF17!wA%C!t_'6ZArith6BinInt1Z2leC7!t0N>AsanAllocModel;compute_req!t8&!st^:rq_primary!ss&!usO2Bs=!sr$RepFacts<secondary_rz!tle5rq!sn+!#58=Z02!t4_7rq_size!w~B3max!w1crounded!t8Cadd!yU>t!sB<6modulo!tt_9rq_nee!ts+K!sr^3r!#4~#!uc%!}#;sym!v#=leb!uc=leb_gt!#3D;3nat02K!#=N4=RingM!#=\'Psatz!#<0?Z03!sm67Env!sp#3P!#4S$!t6I4!sOK6!sO6:Z!sL+;!v+%!wX$!u3/!#=471!sFB!vD76VarMap1!sDC1!sD@3I!sD?0I!v'C7!#B;'!wH>5PExpr!x1?!#8w+1!snE!sIF3K!u/L!wB=6option02!#EQ;8B!sl&C!xz@=Z!sT$CheckerC!w8<4find!sqAC!sq0_sou!#;VQ2Bs8AG_WFHitA!#:I,_facts!#9ZU!#<O%:and_elimF6!#8^&!vS;!#H_'4!sJF8!#?dA2I!~v?0!#6i^8kMaxS!#9o'!#A]<unit!{g8!uC%4ki!#CW5!sf31!#57?1I!#86b0!u<'!yu?!#4d/0!#7a@1!#5WM!#6}D3Op205!sMI1!{XU!#A;%9placed_ok!#B+X!so+4a_st!sjY7AG_RepQ3WFQ!tTb8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!uMgregion!spgpclas!w1gA!tb&shadow!swf?!sw&junk!su-!#Gx^ch!sr#li!|9[!z_,!sp%!tdh5as_t!#NYe7qc!uQg;batches!uSmgq!taV3Lib4TacX2wz!uHb5a_ctx!skethr!sk%I!skR>AW_Large!ss$14SENV!#;F&K!v3S5Cells4cell02!vw`b8!tQf4!sjf!#OY&!#O=;pow!sC=sub!uwUStep8rw_!tN#s!u9f5!|9e@as_internal_ini!~#c5zbool!uRf3!tW&!#B\'!#dY$7!s+#Def6repeat!sE;3map!}+`op!}qebot!wge4zlen!v&'!zL&!#hl-hd!s=74last!#Im_qc_bytes!u}b4jun!#E=b7a_cache!ylV!#5^:1!#4rY!#OJ/4!sk];!sk+2!#e`%I!|;_0!w$Y5ASegs5asegs!zhe;kNumClass!yL'!#Nm^5!#@{#!uP[!yR+3ATP!{%cATSD!sjb6AFLAGS!{ocAC!smg<ASHBASE_CELL!yP_!so#ADOW_!st#!tcb;AHIGHMEMEN!w3c:ACANPOISON!w7dINITE!t_c8ACTXSIZE!sndTSD!t`#!w2dALLOC!zQiIA!t`f6AHOOKS!sldDYING!v<dREALMEMSET!v<d!smjGOT_LO!smb9!sm$VAL!xcePAGESZ!{5dSECNAME!uNdPRIM!sof8ATLSSLOT!sndLSANDI!w-c5!ww#2!skb<OT_SWITCH!|%e5OT_T!#`>%!#=s^6q!#UF#!#=t'!#W#_b_addr!wycOT_CACH!#:ec!sk$_STATS!taf!sng!xo#UNWIND!xo\9!sr'X:!#dS#x!#ZF+!#W=R?AW_PoisonRemap14R!#W>Z!ss<!#ISg5!vHc9ALIBCPG!#5}Z!sp,8!#7^#SSP!taeSSPGUAR!#@_b4a_sb!sjepa!~^e=as_n_reserv!$-2'!#4I^as_sec!uSb5w!#dCY!zF#3Arr6u64arr!w&eri!v2e7as_qmax!spkin!spe9!sp#!#Um,!$5$=ulI!$$lB!$B079nth_error!$%TC1!#m8_sc_map_beg!v6e;!ss&!$8:,!wv_sc!$9+F6of_nat!#8ZR7!t7$Wf9!#q'%o!#UF'!sp[8!y$$!so-C!soZ@carved!#?A#!#oG-!#~K;appI!yZ65NoDup00C!uG\!#rR#!#}A'!y0_ch_user!y~i:ch!$B21!$'`;negb!$PD7filter!v9[9q!x['!tO'!t158flat!{v#!#d:_ch_stat!|^f<ch_!x@%!wKh9qb!su%!#_W&!wJ1!$Ke%or!$1y`:get_!}Y%!u%e>rg!wV#ped!zK$!swe6!tl#pc!soe8pc_coun!#k{e:as!vO&s!|'B6length!u-`as!#j>-!#<Cb!yf/C!$P~J!$<b#!tG^4ckey!#7XZ!$2h$5xc!$4@[!sj,b!$5+]sS!$,\#5aceil!skb4aap!#t1dkobj!skd_f!#Ibddisj!{p8!$ZK%not!t'\9!u]$_env!ttb8!w:#!sn-!#@|14Znat5Nat2Z9is_nonneg!$E?59SatDivModCZ_mod!sP&!sW'!|4O8HeapCeil5h!yjf2sh!shb;!{A$!$Fd[!#QC/@sh_!st#ing_range!swV!#u^+:!$&2#!#F&-!snS6!sn$X<!$&~&_!}7,!#Fu:>pow_po!xz+!sN;:!sN#!sJB7compare!$NUD4!sIE7!w]UG_Ma!wa#9!$:X#stk'!vfZ!#z|/10!sl]!#Z&+9!skg3!uFh!#\Jg8!skg7!|>[Frame3st!#;-%!$PME3!sJF5!#6u[5AINS!#k9%!#g{_s!#~q/!$LtH3!u,\;OI_SPACEBE!#e+&!u3^@kPtrArrayR!#]a$!#7PZ!tl&<OI_NRESERV!#z]c!u`$ECMUTEX!sqb9OI_G!#iKf4OI_!$O_b7!sj#MA!uJgQ!v;g5!v;#!uKc:OI_FB!t]g!sp#MAXUSER!}S&!$Wp?!#Pq_9kPageS!#]JgAkC!#L1#BlockC!#O7+!#3b_c!#UW#!#3b'!sqf2!tdf!#Pr$!#^s'!sq_!$SY$!#w8fBkQuarantine!$a2/!s{lin!s{i=kMaxCach!z8/!#RQI3key!|iU!#Gn%6AHI!$'V+!#Vg^kSpac!u5/!~L[8AFS_!$3j+!#\874True!%$y=:!#FB$is!zR$!tXR!#T2&<AREPQ_!$bB$!uKY!sq'9!sq%!$aY[!sn2mem!sn&!#bH5<!#mC'_In!#RC13Nat!$OXS!$EQ#!tN#cycleSec16rs_en!$MxY!sr6bnd!srh8!sr#ands!sth7rs_pnew!ssll1!#sv&c!ssRA!ss0Pass9rs_gpost!#|z%K!%2dI3Run6config!$k?T:AsDepotInv4d_n!#Z'Y!sl1!#Zq'!#v5;div!#ZJ2Peano2l!$P#_7!#nD$!#}@e8!%,>#_u!$a#e<find_sec_id!#{+e<ch_!#SS#!#pyiin!#py1!ss^5ch!%3|+!yYR!%4u0!sp#lo!spY!#9m'6ch_e!#46'!%B`?Dbv_unsigned_in!#[{%!sY@;!sY-!sPA:bv_!%2v#us!uBS!$0w,awin_vi!#^Zc7AMODEL!#I8b6!sm%!t\dakernel!t\b?amaps!x$#ledger!sud!$qk%visibl!#A6b7ABUDG!$H9'!#58^as_!u`#!spfmp_kin!%9[e5m!%%u#3!spl4!uTibase!~ZG7Z_to_bv!t>c!#gF,!%I6O8m_vm!xC$!%ImPvm_!s\U;vm_noac!s;#!ugP<LazyRestrict:!#5y&!#qtc3a_L!x]V:!t\#L!~I$9nooverlap!sna>entries_nowr!ss+!v{T!$>+'!xrQvm_limit!s]Q9!#>H$to!$mg\2RB!uaW<!%Xk%tains!tK\4a_Zr!#99b4hc!#L#Z!sk/!$B7[!sk/!$ov+!skR6SecGap4zsum!z9X!$:E%free!#KQd@!%PT+!%KQ-!#sg<di!#@q#!sG<=mod!#t|#b!%@^#!sM@neg!sM25!#jr#8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL&!#kxC!%Ik%7!v[eDlarge!#x7%of_arep!%'w%!t'e=senv!s|t>r!s|/!%+HV!$J:#Mem5wr_a!$}?[!#]Y%3n!$#4'!$C\;to_nat!t1\8p!$TI#!{@+!#Yl5:!$5U$!$=8#!#]H67and!%]D#3!#?D$7tac!}W#<f_equal_help!to\<!to%!${//!tT78iff!%bN$!{H5;Zify!$uL%!%_A#ff!sLB9!uJ#morph!sOB7rew!sv$!uVR?!#~K'!${>#2:u8arr_app2!wP2!tF93inj!sIB;!ti&_rev!xF7=!%&}$_!$:|%!vs75proj2!#_P6!%[_>8max_spec!yd?app!$\8R<!#9W#WalkKit6hidden!$\7&I!srg0!wA<!$36/div!$361!$44<2id!sD>7inj!zL%!|f7!x&#sym!~:]!$6&#sub!~:=?!$Li#_!#e-'!xt=1!tr9!~B&!#h}+!%1y1Fora!%%3#!z?7!sC%_f!s,$!yC8in!$S/#!vA#!#5X;eq_dec!#jO16Specif7sum!%lJ$!#7lS9LiaTuning9zify_don!$4e[M!#@&#C!#Mw%_!#Y$-!#8pY!#JU+!#}|&!#L3[8r!s/&!uTZ!$-k%mkR!sgZ!%s='7seg_rom!w,a2M!$%/Y!$j`,ak_sec!#V`+!#@?e!%tL%_of_In!toc<!to%!#Qy$!vMZ3Mem2wa!sd^;wa!{/k8agree_on!t]^7mem_i!$E9cE!$?D'transport_p!%Ajb@stk!svoB!#>n$!sxnC!$iD$!syc!~p,7outside!sk`5munc!#G'%!$;$E1!t5Z=disjoint_f!#4-X!%?k4>!#Kh#!vl+!szY!$v;2!#Kg$!s{b!#jk-k_zrsh2!sogshrf!sojmc!sod7!so$na!x:[S_Sec!#7i%2@r!s/%!#6r#post!s|h4rs!#a'&!$2uO6LazySR4lz!$jbY!#;s,6r!$`$-!uFa8rs_mod!#o'Z!st11!v<#W!#5&YSec!vB#29wmono_ou!wwh19r!$_a1!#]1I>!&6q#!&7$+wviewC!xaV;!xa#!#h@%!tQ&!slO9!sl#NodesFlazy!so&_okb!#fk0!thV8!th$SZr!sicZrL!wr[!#BQ-2@a!zI$x_after_r!#x~c9depot_co!#?Fb4a_A!#lZV!#py1?!$gy&!%Zq#!$'sfArg!$&1$at!$lh0!u`R!$f$'!$79#!sjZ!}y&:nonvm_sam!#ysY;AG_WriteSet4avm!%f,Y!$1P,5DEP!%>}Z:!#[='2<!yf%!$<2^!uR/6acompl!|JdDefs4a!$&>[!sp25pendz!sqh:alive_kept!tii!sv$!sq%!#OEd?!#;B&_clause!#4rf1>!#hU#!#4pa!sz2=!$/f#!syp?!%>n%!s{2!#qnO:map_remove!#w#Qvm_m!%0h#as!saR6vm_brk!t>Ustart!saU=!$0j#subtract!$#\]eager!$=8-!x-`2=avmx!y%q>!#53$!szpB!#6/-!t%%!z}i!#68$!|usvis!vrr!#6J#!tus!#6S'!tul!sy%!tue!#;n$!#@z$same_but!&+3%!s{Y?!tw,!s|$9del!%2S/!svRB!uo0!sy%sec!s|#l!$nB&!$5b^set!%E}\!tk6;se!%?km:!#7T$!#xe#!tpk6!v]%!wUt!&V_gcb_!#U]%!ss&!$eA;or!%;R+4Bool!s'$<orb_true!#yv/!sF,=and!sG-!#oV;leb_le!&^48or!&^N:or!&Hm,!tC,>!tC$fals!tD%!v?^<as_space!yv-!$Qp;lt!&Rn>tb_ge!$Z`7In!#t[,!y7e!$[X,lt!z5lC!yA,!#[x#eva!{:W3!$zx3!$|S^ex!sk&6!u^Y=!#XZ/B!uV/sreach!tj^!%{p+!sk]9!uW+!w1h8!slh!$IC%!#`mPSR!vm#6!vt%!${qK!$6w%5!&K3M!$~rF7!%-HD5!vCT3Arr5!#o$#!#6I&!t24!$-H-5mkrel!sKEapp!sKB6!sK$2!unF6!#8,;:!%Uf$!$4~$!#4Q4=!#3Y+!%KZa>!%QO#i!$T=#!$iN+!swO4Scfg=hunspell_scf!#7?9!$,j,6inj_lt!vg68!vg#Inst@!%Ua$_!$92$_eq!$>z+!st$8!$bc#Na!$2I;!$/%2!sI/!si7sub!si>;!si#sub_maxI!#eiX=machine_!$y9%I!#O?O5!wu$00!$x'^7mapping!$xwf!$UV%!${Oe!sp&2!spl6!spl8!#:eX!&-T$8AIMG_TO!%k5&!x]PBtarget!$ge%!$P}$!uF^;kR!$K:#!$xo^!$7X%9ALOWSH!&#,[!v;%7!v;$!sj[!$O,,AHC0!skfL!skd7ASEC!%2d'!${~75False!%/H`@!%-T$Header!%&2j!s6#HeapFreeMagi!%XTeI!s{+LeftRedzon!t&0!#8J=7Inj_Z_Z!%d766E!',m#!&d>3!%$$-1!{C\3!#;J'I!siT!xw&3ast!%0Xga!%31/!sq`effect!$Dj+!vX69F!#N^$n!&I>7;!'2'$_last!$@T83sig!%+A3!sB&4sigT00!#<m>8sub_diag!|G3!$yb%e!'3s9!#A?+app2!#k&dC!$&d/ass!$S$[!#V%9_ent!'+mW!#KI2!#L5&!#BDBe".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14prodk14boolk14listk14pairk14true37Corelib4Init5Logicnc2eq3h5LinuxProcessSemanticsfLinuxProcessSem5Statep57map_has36Stdlib5Lists4Listsd2In69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~u5bcompute_reqk15false01Zu58kMaxSizeu59rq_neededu5arq_primary46Stdlib6ZArith6BinInt1Zhm33addhm32lehm32ltp55Model3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshp6dmachine_state3h5LinuxProcessSemantics5Riscv7Preludehte5bvmapu56astate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~ih63ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~ilb5depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~iq43memnc3andnc2exih64a_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~ivc5asegsu56schunkih64a_Zru5fas_cache_initedu56as_secu5aget_regionu5h1rg_allocated_userih64a_ALih63a_Lih63a_Sih65a_botih65a_ctxih65a_fsbih64a_paih64a_sbih65a_thrih65a_topih68agree_onhfbbv_unsignedk14None3h5LinuxProcessSemanticsfLinuxProcessSem3Runkg25mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAG_Malloc2~~~~~~kj7cdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_RecycleDefs~~~~~~ko75aliveko7aalive_keptko74avisko75pendz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AG_RepQ~~~~~~kv35AREPQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_WriteSet~~~~~~lj96acompllj94avmx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~loc7AMODELXloc8awin_visloc9depot_covlocaflagsx_repilb5DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~mg6anonvm_same69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~ml18restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~mpc4lzok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mtd3mkRmtd3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ni72MSni76ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~nn47mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nr97seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAW_LargeAlloc1~~~~~~og34SENVih63ATPih64ATSD79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ole2wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsfAW_PoisonRemap1~~~~~~opf4RENVu56effect79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_MallocModel~~~~~~ov5fsame_but_shadowk14Somek16optionu5acb_recycle99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh1AG_RecycleSecPass3HCW6RSStep~~~~~~pm9frs_model_clause89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh1AG_RecycleSecPass3HCW~~~~~~psfbrstep_postP69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~qia6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~qmddhunspell_scfgpm99rs_gpostPu5cch_chunk_begk14consu55chunku5achunk_listu5ach_primaryu5bCQuarantineu58ch_stateu56cstateiq45aceilhm36modulomtd5wmonohf7Z_to_bvsd9nth_erroru5asc_map_beg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bsh2AG_RecycleSecModel~~~~~~rlbbsec_map_begk16length37Corelib4Init3Natrrc3sub" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma map_has_of_In : ltac2:(zQ "a1!h9!jc!l9!m0!m7!me!n5!p0!s3!u0&@2$2@1$1@1$0#k0@1$1@1$0#k0>1l@1$4~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$9~0@4$5@1$1@1$0#k0@1$1@1$0#k0^2^1^3@3$7$3@3$8^4^3^2$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSecPass ()) [] "##/:h01lh11xh21Ah31bh41fh51Hh62H0h72loh81nh91pp;1p;2p;4p;3p;6p10000p4p711!s2$Op4p73101p8p10013!sB$0g001NR!sO%0R!sC'lp4p7210P1p8g002Ij11Tg002nj1FTg003Lj1A!s/$oj2?Tg004Oj1=!s/$oj4;Tg005Oj33!s/$fR1j36Tg006BR2j25!s1$]j27Tg0077j3>!s/$Zj3:Tg0087j32!s/$dj3<Tg009Aj24!s/$_j2ETg00:9j28TP0j69Tg00;Ej4D!s/$`j4CTg00<:j3BTg00=0j3@!s/$JR0f0R3g00=jR43@p=0g00>J#1!s$-FR5#AR6/?6R7#=P6P6f1R8P3C;f2R9537P1!vL'P0\3R:%=8R;P2A6983#0f3R2f4R<?339P2P3O1#0'5X12'7R=[A3238P9!s=,9,79A6298#0[R>A6<29#0\=A>983P3n200!x7$0012!s-%0W0W4W2P>^0;^4:^21P3P7A:663=25<A<!s/%2'4R1X97P<P7f59373%01'5X17P6P6P2P9C;R1A371<A:661=252A<!s/%9'4#0R1P8P0P4A2522R<,43#0X30P0P414!s3&1E04A25991859E9P<1852E9P1eCDCCO4b6AB!uQ$eW5X86X76W0o"). Qed.

(* [comment removed for export] *)
Lemma secondary_needed : ltac2:(zQ "b0!hi6!m0!hj4!p0!hjc!hjf!hka!hl6!hnb!ho2!ho8>1n$4>0@2$9Z^1>0@3$3$1@1$7@1$0^2$2@2$a@2$8$5+og0@1$6@1$0^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSecPass ()) [] "##<8h01Ph12RNh22H0h32_Hh44__x1h54__x2h64__x3h71bh81xh91yh:1zh;1Hh<2Hnh=2RZh>3_H0h?3_H1h@3_H2hA7__arithhB4__ffhC8__varmaphD5__withE1np;2p;1p;3p;6p;4p;9p;7p;8p100>op4p710R0g00?^R1!s5%p8P0p1001N!s61@:!s6'g00A@j28Tg00A\j11Tg00Bjj1:Tg00D7j2hTg00EHj15Tg002Ij13Tg00FPj1?!s/$nj1KTg00H8j2CTg006BR0j2=!s:$Uj12Tg00Ibj20Tg00J?j27!s/$[j2OTg00=0j34Tg00K;j19Tg00LGj6PTP1j6>Tg009_j2MTg00MOj4[!s/$kj2ATg00NHj2Z!s/$hj1LTg00OGj2@Tg00P0j1Y!s/$Nj2X!s/$oj3WTg00QXj3JTg00RAj2V!s/$mj1UTg00SMj3STg004Oj1R!s8$mj2HTg00TKj1Q!s/$ij4ITg00UGj1T!s/$ej1gTg00VPj2GTg00W3j1f!s/$Xj2eTg00X;j3F!s/$^j4ETg00YIj1c!s/$kj2_Tg00ZMj2^Tg00[9j3`!s/$Xj4]Tg00\Jj2aTg00][l9bTg00^`j7\Tg00_Dj8d!vh$JR1f0R2g00_hR334p=<g00`HR4f1R5;42p=6g00`fR6,A2p=;A4132p=BP5g0000R7g00b1R8P8g00bQR9P2g00c1F\p=Df3R:P7P8P8P9f2R7P5P2Gdp=Ng00cQR;/82%15#:#<1h72%17#5g00>JR<#3R=#3#3R>#3R?#3!s$0?R@'6%1:RA#KRB%?<,C:'6RC%??R?%5ARD'818D@'=%?>R>,C:RE%2ARF'810E>,7F'=1OF>=44;%9ARE10FDP1P4%:ARAP;PDn010!s#$20000'0'6g00coRG%1BPBPBPDPFPEPAEP34106@/7Ef4#1#5RE,8?18E@'=f5RE/C>R?%1E#2RE'810?>,7E'=f6#1#2/O!tP$f7R>#1RE#9%2E%5ER?'0!t[%EP;P?!tY5f8R?!sW$KRA#1PAPA%5E%2E%9E%:EEP54GP1f9#1RG#:f:RE#1RA#9RF%2ARD%5ARA!t0%P2P;PA!t/5X71P5P3P>E>%9G%2G%5GRG'0/0G'6P4PAf;!sy%%2ARG/02/02'6X:4P2P@P>E>10D@/0@,6F%5A,0G#;RG,M1%:A=41GP1f<!tk&=!sn$2RF!td&#;9412X71P2P3PEE>!tK%'0#;#B!tH$>#1#2RA/02#;#B!tB'EE>10F@!sL$1P310A@#;RAP2C[%<Af?!w5$0@#;#<P01A52#<1757[R017251A75#<RA[177:\A1Z52P5n20!v7'1!v8$000X94X84P0^94^84P2fA!t#&R0P6P5O31760g00e7R!s,$cRA#LR3#L,@4%Y<,X41@435W41@4A5J45J4g00fB'V%U03S%R0P41H47P5!s-$:P:%Q4CICI%T4%g4!sE$G4<R<g00fnRA%f=,G41e4@R35F4RFCE,D0%c8R8P!sR%=R=g00gUAF4F3!sD$P8P4AF4<3PAP=!s8$CNCN1_09P2P7g00=jR0,M11^27=410dA`4;5C]bBbCbDX44X54X64107@R;,7210:!xZ%717;:[[^44^54^64P2fC#1R;#2%9;P6P5P?O5bAb0b2W0P2O1b2b0!s$$1b1W3W1W@W?W>X3C1a:7M9bb=W;W<XE4o"). Qed.

(* LPS revision repair (75d69e00, checker 2c6b6db8).  UNIVERSE ANCHOR for recycle_sec_pass_at's
   replay below.  `KReplay.run1z` hands the decoded term to the kernel with
   `Std.exact_no_check` (KReplay.v:627), so a replay can only CONSUME universe constraints
   already in the graph and cannot add one.  The term applies `Nd.ex_introF17`, a monomorphic
   `Lemma`, to `ast`, whose level is `max(Set, PositiveMap.tree.u0)` through `a_st : astate`
   and its `as_chunks : PositiveMap.t chunk` field; that needs
   `PositiveMap.tree.u0 <= ex_introF17.u0`.  Measured (scratch probe, image 2c6b6db8):
   `Check (ex_introF17 ast)` elaborates and prints exactly
   `(* {} |= PositiveMap.tree.u0 <= ex_introF17.u0 *)`, so no level moved — what the revision
   removed is whatever elaborated declaration used to contribute that constraint ahead of the
   replay.  The line below is that declaration, written out. *)
Definition u_anchor_ex_introF17_ast := ex_introF17 ast.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition rstep_postP : ltac2:(zQ "b0!h9!jc!hjc!m7!hoe!hsd!ig4!igd!il4!ipb!iu2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$8>1d$9>2lo$2>1m$a>2mo$4>3XC'@1$3$2>3XB'@1$3$2>2PZ@1$3$2>5MODEL>0$7P>4msF'$5>3mo'$4P") := ltac2:(zQ "je0!h9!jc!iu9!iuf!hjc!p0!iv4!jj7!m7!jk0!jk9!il4!iu2!hsd!hoe!jl1!jm3!jmc!jn9!joe!jp6!jpd!jq4!jqd!jr6!jrf!js7!jsf!jt8!ju1!u0!jud!jvb!m0!l9!kie!ig4!igd!kn7!ksb!kt4!ku2!kua!lj0!lna!lo4!lsb!lt6!lu2!luf!lvd!ipb!mk3!mp0!mt5!nh9!ni0!nm4!nma!nqe!nv8!ho2\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$i4@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$b\1d$j3\2lo$4\1m$c\2mo$e\3XC'@1$8$4\3XB'@1$8$4\2PZ@1$8$4\5MODEL>0$i5P\4msF'$d\3mo'$e@2$3$b\2s'$b@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3$c\2m'$c@2$2@3$5$4@1$hb^h1@1$hb^hc@2$2@3$5$4@1$h7^h1@1$h7^hc@2$2@3$5$4@1$h8^h1@1$h8^hc@2$2@3$5@1$8@2$i2@1$1@1$0#k0@1$1@1$0#k0@1$a^h1@1$a^hc@2$2@3$5$4@1$hc^h1@1$hc^hc@2$2@3$5$4@1$h6^h1@1$h6^hc@2$2@3$5$4@1$h3^h1@1$h3^hc@2$2@3$5$4@1$ha^h1@1$ha^hc@2$2@3$5$4@1$h9^h1@1$h9^hc@2$2>2sc$9>0@3$he$9^1@1$h0@1$6^h2@3$he$9^2@1$h0@1$6^he@2$2@3$5$i1@1$f@1$6^h1@1$f@1$6^hc@2$2>2c0$4>0@2$jdZ^1@3$5$4@1$h2@2$h1@1$6^h3^2@1$h2@2$h1@1$6^he^2@2$2@5$j6$7@1$h4^h1@1$h5^h1@1$a^h1@2$i3^h3^h2@2$2@3$5$d@3$j5@1$h4^h1@1$h5^h1^h3@7$j9@hf$j7^ie^id^ic^ib^h0^f^e^ia^i9^d^c^b^a^9^8^7^6^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^5^4^3^2^he@1$ja^ie^hd@1$i0@1$1@1$0#k0^1@1$jc$7@2$2@5$ib?5HCEIL^h1^h7^h6^1@2$2@2$if^h1^1@2$2@1$j1^1@2$2@3$ie?5HCEIL^h1^h2@2$2@2$j4^h8^h2@2$2@4$id^hc^h1^h8^h2@2$2@2$j0^hb^h2@2$2@3$j2$7^hb^1@2$2@3$i6?5HCEIL^h1^hb@2$2@2$jb$7^1@2$2@4$j8$7^1^ha@2$hf@1$0#k0^id@2$2@7$ic^hc^h1^hb^ha@2$hf@1$0#k0^id^h9^1@2$2@4$i9^hc^h1^h9^1@2$2@3$hd@2$ia@1$6^hc^h5^h9^1@2$2@2$i8@1$6^hc@1$6^h1@2$2@3$hd@1$i7@1$6^hc^h9^1@1^h4@1$6^h1").


(* [comment removed for export] *)
Section PreCells.
  Variables (s : ast) (XC XB : list Z) (m : mem).
  Hypothesis RQ : ltac2:(zQ "10!lj0@5$0?5HCEIL?1s?2XC?2XB?1m").
  Let st := a_st s.

  Lemma senv_of_arepq : ltac2:(zQ "60!ok7!okf!ol6!jqd!jsf!op9@5$0@1$5$1$2@1$3?1s@1$4?1s?1m").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSecPass ()) ["HCW"; "PreCells"] "##Auh02_Hh12F1h23F10h33F11h43F12h53F13h63F14h73F15h83F16h93F17h:3F18h;3F19h<2F2h=3F20h>3F21h?3F22h@3F23hA3F24hB3F25hC3F26hD3F27hE2F3hF2F4hG2F5hH2F6hI2F7hJ2F8hK2F9hL2FLhM4INSThN2PLhO2T1hP2T2hQ3T2bhR3THRhS2WQhT1chU2chhV1vp;2p;1p;3p;5p;4p;Cp;7p;Np;9g00h<j2|Tg00iEj1{Tg00jIj3_Tg00kKj2VTg00lSj2zTg00m\j2oTg00nfj2cTg00omj2^Tg00A@j2ZTg00J?j2WTg006Bj2>Tg0113j3UTg012=j3TTg013Gj3yTg014Xj3sTg015gj1nTg005Oj3kTg0174j2iTg018=j1bTg019Ej1RTg01:Oj2QTg01;Zj1]Tg01<bj1=Tg01=aj1[Tg01>fj1YTg01?kj5XTg002Ij11Tg00W3j10Tg00FPj12Tg01A7j1HTg00Rmj1NTg01B;j1JTg01C:j1KTg01D>j1ITg01EBj2m!s/$_j2ATg01F<j44Tg00Nhj1F!t:$nj1jTg003Lj1hTg00SMj38Tg01GAj2dTg01HEj1eTg01IXj1fTg01J]j1gTg01Kaj3aTg01L@j4O!s/$\j1`Tg01Maj1lTg00Ibj2@Tg01Nfj2pTg01Omj3qTg01PDj3r!s/$]j1\Tg01Qhj3LTg01Rlj1tTg01T3lCuTg01U?j7vTg01VDlNwTg00][l9xTf2R0f1R1f0R2'>'>p=B%12#1p=5%12#2p=E%02#0p=Dg01WJR3?812p=9A83129830p=Mg01XNR4f3R51@01P2C4p=CP4P5%11#2,@0!s9%:%1!sq$?!sy$#0#0p=S!s2+!s$'p=;%=1#I=832p=6%0!t]$<%=2#Ip=7f4P5P0!tM$C4p=3%F2#Fp=GP4P0P!tJ&Pp,5HCEILp,1sR5'|R6%{5R7p,2XCp,2XB3_R8p,1mR9,V5R:1z59R;1o59R<1c591^59g00`HR=g00cQR>/Z2g01YP,W2'>AU591AT591Ay591As591'>3B[!ze$Z^R?%n79k?21i91[]U%b7R?#RR@,Q9%]7#R,Q9'>3B3BRAg01[h#=RBg01\kRC%[5RD%Y5REP9DXRFP9g01]oRGg00>JRH#1RI#0RJ#0RK#5RL#2%1IRM#1RN#1RO#1RP#5!s$$E#=RQ#H%=>RR#HRS%DKRK#0#E#=#H%N3RT'93MCCRUP9PG%0MRM#0RV#0%2HRW#J#KRX/9TRYC:RZ!sI$1JRJ#0#?#2PYCCR[P9PGPLPYC:RL!tv$_5RG%0N!s8$\!s|%HRH#0R]#0R^#1R_#1%S^#;!s$02/6TC:R^!t2%M#5RM%IRR`/9TRaC:Rb!s?$<P%J>RG#KRc/9TRdC:ReP4!tE$`<g01aH#7PTD3Rf!s<&bQ%2I%2K'm/AW#719`aD3Ra!sD&c\PYC4RW!s5&df!s5$Y!s5&em%2_#=#H!sx$_!s<&g5PXg00ec#F#GRK%jN#hRI%NI98IG98IG78G'd19STRS'9D3RG!s_&h=Pc19XdD3RX!s9&iH%e7#f#J#K%gR=McTD3Rc!sC&jO%FK#G#G#G9a3`C4R`!s@&kUPSC4RK!s5&l[g01mf!up&R!s<&nmP=P3%72XV=g0204COC4R2!sD%21=%IQ!sV$Q!s8&2D%?H#D#<#?!s+$D#E!sx&H!sH&3L%0M#5!sF&?#2!sF&M!sF&4U%7C!s8$3P4P9PC16DTRCC4R7!sH&5]!u/$I!s5&6e%2O!sk&OPFAP9ECRCP9PD%2NRNPSCCRS!s5$5V16ETC:RVP9PEPN%`5%l5/6T'6CCP9PE%1JPdC:P9PEg027jPdCCg0296RJ,@ERNg02:;R4/p@P4P=g02;FP@COR@9q=>Ar=@>%\?!sv$'6'65P9%2PRP,@Ng02<PRN/AJ/AP5L9%t5g02=XR5'@g02>cRP/AN/A55L91@EPg02?kR5!sS%!t{$5PdCC!~H%3BRdPFPB%1]#5!vb$5#S#<#<#5#EPDPEP9fAf7f6P1fDf;fFfEfIfHfGf<f:f9MCuPFeX0dXQVXPSXOCfLFvXDOXCIXB7XA3X@MX?HX>QX=2X;RX:KX9`X8cX7XX6GX5_X4YX3WX2aXKfXJeXIbXH^XG\XFLXE[X<ZX1UP0MNwX0AXR<XL;XM:XS8XN6p,2RQM9xo"). Qed.
  Lemma renv_of_arepqx : ltac2:(zQ "50!h9!jc!iuf!ou4!luf>0@1$4?1m@2$2@1$1@1$0#k0\1g@1$1@1$0#k0@2$2@1$1@1$0#8\1b@1$1@1$0#8@3$3^2^1?1m").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSecPass ()) ["HCW"; "PreCells"] "##@hp'0h01bh11gh21Hh32F1h43F10h53F11h63F12h73F13h83F14h93F15h:3F16h;3F17h<3F18h=3F19h>2F2h?3F20h@3F21hA3F22hB3F23hC3F24hD3F25hE3F26hF3F27hG2F3hH2F4hI2F5hJ2F6hK2F7hL2F8hM2F9hN2FLhO4INSThP2PLhQ2WQhR2X1hS2X2hT2X3hU2X4hV2X5hW2_HhX1chY2chhZ5nd_i1h[1vi001xp;1p;4p;2p;3p;?p;Np;8g02A7j1sTg002Ij11Tg01<bj1:Tg00Rmj1OTg01F<j44!sJ$nj1LTg003Lj1KTg01D>j1?Tg006]R0j2HTg00W3j10Tg00FPj13Tg01B;j1JTg01C:j1FTg02BBj3ITg00h<j2aTg00iEj1`Tg00jIj3_Tg00kKj2^Tg00lSj2]Tg00m\j2\Tg00nfj2[Tg00omj2ZTg00A@j2YTg00J?j2X!t`$Bj27Tg0113j3WTg012=j3VTg013Gj3UTg014Xj3TTg015gj1STg005Oj3rTg0174j2qTg018=j1pTg019Ej1RTg01:Oj2PTg01;Zj1oTg00Ibj2@Tg01A7j1GTg01EBj2l!s/$_j2iTg00Nhj1DTg00SMj3<Tg01GAj2gTg01HEj1fTg01IXj1eTg01J]j1dTg01Kaj3hTg01L@j4jTg01=aj1kTg02COl?bTg00;`j4QTg01VDlNnTg02D\j8MTf0R1#1#1p=B%11#3p=5g01WJR2f1R3#?;<1p=Nf4R4f3R5f2R6%:3#?=<21C4p=8P4P5P6A<23!s6$>%01#0p=9g01_5/@1p==!sC$p=2g01XNR5P6P3P!sS$6%0!tH$C%1!s[$A!sc$#0#0p=m!s2+!s$'p=;%D1#Dp=E%:1#?p=cp,1mR6#sP5P6g02Eag00>JR4#1R7#1R8#1R9#1R:#1R;#1R<#1#B#B#5#:R=%O2R>'NR?C4R@!sg&Fkg02H4RAP>D8RB%L<#KR<P5P6PA%?1P>D>RAX1<RC'HRD%04RE#1#9RF#1#9#3#=%34R4#J#FRG/2>RH566RI%L9#KRJ%9ERE#1RK#C#5#=%F1/2>566RLX0JRM'HRNAI316X0J,HJX1<RO,H<RPP0P<PCPP\N\IP1P0PJPMPPP1p,5HCEILp,1sRM'aR0%`MRCp,2X!s'$B3_RQ1^M6RR1]M6RS1\M61[M61ZM6g00`HRTg00cQRU/Y1g01YP,X1'7AWM63AVM63AUM63ATM63'7'7'7[]Xg01Z^RV%SC9rV11q63[]Y%pC#R,P6%o!s-%!sT%!s$%RVPPg01]oRW%07RX#0RY#BRZ#3'@%G=%:UR=#GR[%9YRY#0#5#:#G/2>'2'2566R\%08R8#9#5,@W=66HR]%AX#A#3!s6'X%5Z!s2'W%09#5#=!s3$9%1K!w0$mE#;!s$03#:/N!wB$E%18#BR8!sN$?=RZ/2>R^566R_%C;!s<$JURU#FR;/2>R`566Ra!yD%1`<g01aH!yB$b!s:&bQ%37%3Y'l/i412Z^D8R^!sB&c\PHC4R4!s5&df!s5$H!s5&em%3K#:#G!y|$K!s<&g5PGg00ec#D#ERY%OJ9<JU!s&''g12[>R['2D>RU!sY&h=P;12G`D>R`!s9&iH%fC#e#J#F%d=/2>,2;D>R;!sE&jO%DY#E#E#E9h2ZC4RZ!s@&kUP[C4RY!s5&l[g01mf!uh$=!s:&nmPTP2%c1X[Tg0204CjC4RT!|`&1=P?C4R?!s5&2D%0F#C#A#9#C#9#5!sq$F!sD&3L%08#B!sD&A#3!sD$8!sD&4Ug01\kR2!s<$C!}L$2%kM!s5$M!sK&5]!u#$[!s5&6e%3:!sG$>PPP<POfWROPJfX?I!|w$fQRPPOPPP6f7fBfAfEfDfUfPf8f6f\f[fVM?bAIOP6eCQCQXF>XE[XDMXCCXB8XAFX@?X?TX==X<YX;ZX:;X9`X8UX7KX6HX54X4^XMbXLaXK_XJEXI9XHWXGXX>]X3\P3MNnXWVXNSXORXQQXP0p,2RQGMXVLX0JP3P1O2n20010!s#$121!s0%X2NXUIXTAX1<!sL?DXSBXR@P1GMWZo"). Qed.
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
ltac2:(KReplay.run1z (kr_t_AG_RecycleSecPass ()) ["HCW"; "PreCells"] "#$+{h06__sat6h17__arithh24__ffh38__varmaph45__with5!sS%4h6!s/%5h7!s/%7h8!s/%8h92_Hh:4__x1h;1Hh<2A1h=1Kh>2chh?4__p1h@1zhA2A0hB7!s]$10hC!sg%9hD2HahE2P2hF2T2hG3_H0hH3_H1hI3_H2hJ3_H3hK3_H4hL4__p2hM4__p3hN4__p4hO4__p5hP4__x2hQ4__x3hR4__x4hS4__x5hT1chU2schV2A2hW2A3hX6ACEILBhY1BhZ2FLh[4INSTh\1Jh]2J1h^2J2h_2J3h`2J4ha3Jsthb2NNhc2P1hd2P3he2PLhf2S1hg2S2hh2S3hi3SEChj2T1hk2T3hl3THRhm4Tunwhn1Uho2W'hp2WQhq2Wnhr2Wrhs3_H5ht3_H6hu3_H7hv1bhw3ch'hx4cstrhy1hhz1ih{1kh|1mh}3sc'h~1xp%0p&0p&1p;2p;1p;3p;4p;5p;6p;7p;=p;<p;>p;;p;:p;8g00h<k21VTg00iEk11UTg00jIk30lTg00kKk20`Tg00lSk21TTg00m\k217Tg00nfk20wTg00omk20kTg00J?j2YTg006BR0j23Tg0113k30YTg012=k30TTg013Gk31STg014Xk31FTg015gk116Tg005Oj3LTg0174k20zTg018=k10vTg019Ek10JTg01:Ok20NTg01;Zk10jTg002Ij10Tg00FPj18Tg02I>k10gTg00Rmj1sTg02JBk10_Tg00W3j14Tg02KFk10!s0$LVk10!u/$Nfj2bTg01<bj1RTg01D>j1fTg01>fk11=Tg00Ibj21Tg02M_k10CTg02Ndk40ETg01A7k10BTg02Ofk10xTg01Qhj3|Tg02Pjk10qTg02R4k10pTg02S>k10oTg01Omk30ATg01PDk30@!s0$]k10?Tg01EBj2uTg01J]k10>Tg01B;k10=Tg01C:k10<Tg00Nhj1G!v5$nk10:Tg003Lk10iTg00SMj3CTg01GAk20hTg01=ak10!uW$L\k10eTg01Mak10d!tC$_j2!wz$Rlk10cTg02TJj2!s/%gk109Tg02UIk30b!s0$gk208Tg00=0j3=Tg02VIR1j1hTg02WVj1rTg02Xdk10aTg02Ynj1\Tg02ZNk20^Tg02[Xk20]Tg02\ak10!sD$^0j3`!s/$Mj2!v_$^ik20[Tg02`0j1!vh$a>k10ZTg02bKk10X!s0$ik30WTg00A@j29!zo$[j2JTg02cDk206Tg02dLk40V!s0$ik10UTg02f4k10KTg02gCS00k10S!{L$]k20RTg02hOk20Q!s0$ik20!y$$j6k100Tg02kGk202Tg02lPk105Tg02m[k10PTg02nhj2~Tg02oHk1!z#$30Sk11QTg031_k31NTg032Lk11MTg033Sk21LTg034Wk21KTg035[k11JTg036`j3jTg037dk31ETg038ik11CTg039nj4{Tg03;2k11BTg004Ok11ATg00TKk11@Tg00UGk11?!s0$ek11>!|:$Xk20HTg00Ykk21!yw$9_k20!yx$ZMk21;Tg00[9k315!s0$Xk4!|m$3;Kk513Tg03<Tk512Tg03=\k111Tg03>Aj2P!zQ$mj2lTg00VPj2e!t9$Ik10}Tg03?2k10|Tg03@4k10!u;$A6k10~Tg03BAk1!~W%;Ej4!vN$CRj1xTg03DZj5yTg001Nj6nTg03Eek20yTg03FMk318Tg03G1k219!s0$Rj3vTg03H5k31:!s0$Xj7wTg00OGj2zTg00QXk30ITg00RAk20u!v^$ij4iTg03Ibm=0tTg03Jhm<1DTg03Kmk60sTg03M2m>0rTg03N8m;!}W$3O=m:1HTg03PBk41ITg01F<j4k!}C$@k40LTg00X^k407Tg00^`k70MTg00_Dk80n!sD$;k31OTg03QCk61P!s0$gk70mTg00cQR2f0R3'9p=2f2R4f1R5/33'3p=5g03RKR6/13p=A%R3#fp=Xg01WJR7?C53p=Z%03#0#0#0p=WAC7539C74p=@!s>$p=a%03#8p=}%R4#f%R5#f=C735C7p=K!sb'8p=7%03#4p=[g01XNR8P4P5P3H1Ip=DP!s4&Ckp=B%4!sN$H%4!t-$d!s6$!tN$>0Fg03SPR9g00`HR:P1P3H0Lp>0DP8f3R1P4P5Ck/33p=V!s^%4#4p=>!te+p=]P8P1114!t=&;1S539|14p=Ig02:;R;P:g02;F!t%'O%G3#Gp>0;P8P1P4!uz$Ckp=tA=:53p=OA=:52!tC$Q!sR$#G#Gp=^A=:32p=g1145/93p=Ff4R<P!ts%{!sV$<1945!s0$E20H:3p=:P4g0000R=g00b1R>P>g00bQR?P:P5g03T[P3H07g00c1R@K0Mp=6!wi+!s$'p=MP1P=P>P>P?!vz%L0np=UB1O!u&$!st&0gU!st$p=mP5!sV+3P!s~%o!s:/J1Pp=_P4!s8+5P3K0mp=Tp,5HCEILR=p,1sR@+1VS01&1U@RAp,2XCRBp,2XBRC40lS02p,1mRD-0`@S0321T@DS04217@DS0520w@DS0620k@D%23S07g01YP,Y3'3REB0Y@D5B0T@D5B1S!s+$F@D5'335[^T:g01Z^RF&16ARG9LF3RH20zD5[]>&0vARI$0JRJ-0ND&0jARK$0JRL-0ND3535S08PDg00>JRM#0RN#0RO#0RP#0RQ#0RR#8RS#A&0g@RT#XRU%s7RV'ZRWPD%0R!sF$X#A%0R#WRY#0S09#8RZ#XR[&0_@R\#XR]1Z]V3@R^PD%4MR_#4R`#aRa#0S0:#}S0;#Ap,2stRb$04&03bRb,b9%R2Rc#fRd/ZVRe3KS0<%4P#7Rf#ARg%4NRh#0Ri#4Rj#[#7Rk#ARl5DDABDle%4jRj#0#7Rl#A%4hS0=#0#H#7Rh#A5DD&1=@Rm%4j#d#7Rj'1Rn%0_Ro#0Rp#0Rq$0F#7Rr,1mS0>5DDRsP8PDP\&0Db$0CH0E'3S0?'335CVCVCVRbQ01Q02Q03Q04Q05Q06Q08PDP6g03UB%H`R`#4Rt#4#>#>S0@!s/'A#>#>#8#R$0BRu&0BcRc&0x@#XRvg03VMRw/]V9@]]9@d[3@5@UC;S0B%0q#}#A%8QRQ5|DS0C!t;&W`&04ARq&03ARx,b9Ry;KeS0DC;S0EPDPgg03XlRgPfCIS0FPDP6PgPeC;S0GPDg03Z7Rg,16g03[@RzPgCIS0HPD116zg03\DRgPzCIS0I!s:$g&0qARg&0pAS0J&0oAS0K/]V3KPD%4p!w$$p#Ag03]KRzPpCI!t@$zPeC;!t=$^T,161b;L&0OLRz:0A:2B0@:z2&0?K;K!sp%Ha#7Ra!sn$_YRzPa!sn1%a`#7Rz!sF$`cRaPz!sF&a%8NRN%aiS0L#8Ra'u%RQ$0>%8Y#R!s-$M$0=$0<g00ecS0M#G$0;RY&0:P$0iRQ&0=2R6%sQ9CQ69CQ63C+0h;@V3@']C;!xr%35CVS0NPbQ0BQ0CQ0EQ0FQ0GQ0HQ0IQ0NPDPm&0f@RQ#XPVCtS0OPDPQ%8PRz1ZcVC;S0P!s8$HO#71]m!s8$QPDPmPz&0e@RO&0d@Rp;K!s@$R!s@$a&0<6/ZVR6C;S0SPDPmg027jP!s6$TPDg0296Ra,1mR{1b;J#X&0OJR|!w'+|2&0?I!wu$CtS0UPD11{Sg02<PR{/SaPSCIS0VPD&0c@g02=XRa'1g02>cR|/S{PaCIS0WPD11m|g02?kRaP|CIS0X!tp%!tY%YPbQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WQ0XQ0Y!|q+xR6!|s%Ra1czy,1\1Sqy,cz!{N$Zg03amR|&099B0b9x5208933=PD%h5R{%r5R}&0a5%\4;KV5K{!uJ'3bLR~PSCICV[^y9]zS0[PbQ0ZQ0[fKQ0220^A520]A5'3\E^T:S0\&0\A=`:C,q:S0]20[A5\H^>FS0^ALF5GRE%p1%p4'OA=F<1[\E[^wF!sG$_&0Z3$0XX>F>0WFG,bF/OyS0`1q:6S0a19yqS0bg03cXR6,JqRG%2qRE%8tS0c/c6,9q'3'QS0d206AI206AKP;P:Q00A`;JLRLH0V=`:B,q:g03dl&0U5g03f73=AL;3L&0K1&0S35L:'3Xv;-0R;&0K4=L:B+0Q[!u@$201A2$00%8`R`-01A$00202A2$05202A`$05g03gB&0PA'~%GYS00#GS0e!|9$#^!s$,RY5=|g03hM&1RA'~==|Yg03iX9=:gQ0Jg03jm5=:Q0Kg03lB5=:g03mRRg&09F&1QA:1NF5208F33=%p5R|$1M9=g41Y2|'3[^~F]{AL:3B21LA5[^|:AL:3C21KA5[^Y:'3353535'Q!s$%!#;'$KPbQ0\Q0]Q0^Q0_Q0`Q0aQ0bQ0dQ0KQ09#0RA!#:]$aRC#8RB,JTRF#gS!u&$n>/9TS0fg03oDR|,1T&1J=Rg7F~S0g1J\~R`#gS0hAj=\wS0iAF\wgRH1Jm~R;#gS0jB1E=m~S0kAFm~gRL1JQzQ0L#0#}Rz9j=QAFQzgPT11|~R|P\PwPTP|PmP~!s-$QPz!s:$mP~!s-$QPz&1C@R@g040QRJ5j=AF@Jg!sS$@PJ!sK$@PJ!sW$@PJ!sg$@PJAL93x1J{~Aj={}AF{}g1cN~P{P}!sa${P}!sa${P}!sa${P}!sa${P}P@PJC{D<!s$%7E}35'Q[^U9AL95xR}%h1RJ%h4'O$1B%h<%r<PJ%r1C{[\}[^}9^U9!sz$QPzQ0=#H#8,uN,9O9E~O%2p1YpO35D<35!t2'!s0,D<35'QS0=PbQ0JQ0fQ0gQ0hQ0iQ0jQ0kQ0=P=!t'$4g00e7Rp#sRO&1ApRz&1@:RQ&1?:R}&1>:RJ20H:2R@%:ZR{3621<J?R?P3!sb$=JR|g00=jRK+0G21;34==|KdB15:25H14RKb2b3b4%2ZR|P3b1192~RIeI13AEZmLP=P\Pwf6RtPOPzPQP}%WC#7RC#:96J@P?P!sg+C!se&weI12Q0:#d#[#d#M#7Rw?E\H1~9xRx$11%\xRx#21P\~%2\S0:%2`\I[1Pq61926%2G[\E1PTBRG%2T%2B%2F[[RF1Pm~%2mS0L%2;\I[POPz1l:5S0lP}PJ1e:MRM96J@RI&0}>R>PICU!tp,X::Q07%25[^::P3Pxf5RxO2b1b5b6b0b7bx%2yRyePyQ0@#0#>#>#W#M!u8$yQ0A!s3+I,9g7Eg1JgZS0A&0|=R;11gZ,Y;5Eg'QS0@'3R;%HARA#[#H#>#[!sr&7&0{gR~%>A#>S07!s>,,9~3ES0m&0~=&10=CNQ0m,3;R;eP;f]S0nPD%4o$0F#H!vv$a#H#7R;/1SR=PU1]CVRV,Z]9@[]R]9@vd9@ucRdCtP0A`7Wd9BD=R[ABD=WR~PDP=%xW#\PdC;S0o'3RA[RBP[\APBP8PDP=PWPdDyP5n2111000010120!s#%PBP3P5O1S0pPAP0P~Q0o11;XRA=BD^RBQ0;,1;S0;Q0D5BDS0D11;fRd11;kRW5DD!tW$WeS0q11;lR611;hR`5DDR913saS0r'3S0s'3S0t'3S0u'3S0v'3S0w,3~S0xP3Q0oP0A@cve9@UuRu=`7]9BD=S0yABD=uRU!u[%u#\P]C;Rv'3Rc[ReQ0y\cPe!u[&uP]!u[<eP3feO1PcP0PUPvQ0xP3P0%\Y,1=RYA`7^V5BDR7ABDY^RcPDPY%x^#\PVC;Re'3R][RuP7\]Pu!t<$YP^PV!t<<uQ0pP]P0PcPe!t9$Q09#8R0,PqR]%201Jq0S09#2[\ERE1PmZRuQ0L1JmZ#2\|[RVPGPF1PgZRY%2gQ0A!s=%81P\ZR7Q0:1J\!sQ&|!~'+:;R;%:X'?%:SS0:,?;Q0:'?'m,oJ!|I,11=SR=,OARSP3!|?-8PSP:P=ABD3^X@:P4PAP3EnPBP~Q0wf?PBQ0vP3Q0DQ0ufpP[Q0tPDPd1SkfRAfoP]PEPuP!u0$PYP8P7P!ti-fS0t,?;S0u!#3q2d!tT2!sm220yNXS0D1Y2NS0v%2X1uNXRf,Y2[R^[S0w%2NR=g041YRSB18NX5UWDS0:%2f\S^D=R=!tY$4g04252192N+0GQ0veO1R2P^!tr'Q0u%:kRkQ0t5v:RS'?RX%:N&0:R61::RR56!vd0dARN/9f!u4$0!u6,bCbB!v%?A6J@S!uv/A!uv1FwADDdN!si?1?;k/mX!xD1OWNRX!vi2XP:PNADDd3X@:P5PW!x?$[P3b=b;b=Q0qQ0sfnP9Q0rPDP61ShlRWfm!x9AlRl,?;Rd!x736!x7A!yO$wQ0:P!wV%!wA-%:hRh=v!t$%dRd=6JR!w1/6W!w1\l!tp/W!w166!w1Ch/md!w12`NR!zt3d!w1&6!w1&`!w1$9!w1'PsPaPDPn1SrjR`fa!tB7p-0R6POPzQ!#;J$A6J{M1_J15TJP>%:jRN,?M!w>%!#;R1W?AEZ35115j#2[^::^?6P3AFmZgPmfNRhO!waSQ0e,z:Q00!s+$M,z:60I!s&$g00fB+0u=CpOPzP:P:P:1l:<PxPQCiPx!s4$xP1PQCiCiP51l:4CiP}PJ%:y1e:PRP56J%:I96JP5TJf7,_J5TJf8!s-%P>PJ1?M{=6JPP>PJ%:w1e:i56Jf9Ri!sJ,Q07#H!#<`&RP#:1e:o56!sB$f:Ro,_J1e:_96J@f;!s]%!vg&rR>=v:NRN!z'+CU!s$'!vu0XP:XQ:XR:XS:X?6XL6XM6XN6XO6191I9Ey1/3x/3tAF5Z<AEwti19Pxf<%2xf=3511xj?F`f[[[[!w\$P:^Q:^R:^S:^?6^L6^M6^N6^O6P3Q0c/c0,9qQ09#gAF\CgQ0mQ0@P\PgPTPqPmPhfSfPfZQ0nO?!{rUN!{r/`!{r311n`RN9DDn!sn;!zV$1?M>!{x3X::113r113j/1`'O!#Br$mO1!t0/Q0>/ON!|5&n!|5%Q0>!|6$s!|6'f_CN!s$/b<b;X9eX<cP5P3O2n200!#<\'!s/$00!sJ$<vX9U!sJAW9XA~!sI>Ab;bAPDQ0;Q0<Q0qQ0?,3955[CV95~BRBePBebXPbebbbEbFW9XkLWFWjXdHWEWcWhWgWffVN=0tW9WrWqWKWJWIWHWGW9P3N<1DboW9W\XnafDJ0sWmWaWuWtWs!sP0oN>0rW9W`W_WWW^WVW]W<P<N;1GW9WiWlWZW[WpWep,2RQN:1Ho"). Qed.
End PreCells.

Section RSStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (ch : chunk) (d : depot) (lo cb : Z).
  Let st : ltac2:(zQ "10!igd$0") := ltac2:(zQ "10!iv4@1$0?1s").
  Let mch : ltac2:(zQ "10!hjc$0") := ltac2:(zQ "10!qs2@1$0?2ch").

  Hypothesis RQ : ltac2:(zQ "30!qt1!hjc!lj0@5$2?5HCEIL?1s@3$0$1?3mch?2XC?2XB?1m").
  Hypothesis CHIN : ltac2:(zQ "30!qt8!qu0!u0@3$2$0?2ch@1$1?2st").
  Hypothesis SEC : ltac2:(zQ "40!m0!hj4!p0!qud@3$2$0@1$3?2ch$1").
  Hypothesis QUAR : ltac2:(zQ "40!p0!qva!rg8!rh3@3$0$3@1$2?2ch$1").
  (* [comment removed for export] *)
  Hypothesis AX : ltac2:(zQ "30!iu9!lt6!luf@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!lsb@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!jj7!lvd@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!kn7@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!lu2@2$0?1d?2mo").
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : ltac2:(zQ "20!rhc!ho2@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!h9!hnb!ho2!jud@2$2@2$1?2lo+ji0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!p0!h9!hjc!ri5!jud@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis ST : ltac2:(zQ "40!h9!jj7!ni0!jud@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis TP : ltac2:(zQ "50!p0!h9!hjc!okf!jud@3$0$2@2$4@1$1#k0?2tp$3").
  Hypothesis OK : ltac2:(zQ "60!kie!jj7!jp6!jpd!jk9!mt5@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  (* [comment removed for export] *)
  Variables (mr : mem) (sbs0 : list byte).
  Let wlo := sh (ch_user_beg ch).
  Let wn := nsh (ch_used ch).
  Hypothesis GW : forall x : word, ~ (wlo <= bv_unsigned x < wlo + wn) -> mr x = m x.
  Hypothesis WMR : ltac2:(zQ "20!jj7!rif@3$1$0?1m?2mr").
  Hypothesis WMR' : wmono asegs mr m.
  Hypothesis MIR : ltac2:(zQ "20!jj7!nqe@2$1$0?2mr").
  Hypothesis USH : u8arr asegs mr wlo sbs0 /\ Z.of_nat (length sbs0) = wn.
  Hypothesis VISE : ltac2:(zQ "e0!h9!op9!jvb!p0!hsd!jj7!jp6!jpd!mp0!nh9!nm4!nv8!rj8!jc@3$3$4@3$8@1$6?1s@1$7?1s?3msF@7$a@hf$9?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$1?2cb@1$1?3mch?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$c@1$0#k0+mrjjc?2fc@1$2@1$d@1$0#k0?2mr@1$b$5").

  (* [comment removed for export] *)
  Definition rs_model_clause : ltac2:(zQ "10!igd>3stX$0P") := ltac2:(zQ "c0!igd!m7!ouc!l9!iuf!pj9!pkc!pl3!me!iu9!p0!plc\3stX$0>3stA$0>0@2$5^1?2st@2$4$0\4stA'$0@2$4@1$1$2\2ev@1$1$2@2$9@3$a@1$7@2$3$0@1$1$2@2$b^4?3mch@2$6@2$3$0@1$1$2@4$8$0@1$1$2^2^1@2$5^2^5").
  Definition rs_gpostP : ltac2:(zQ "20!hsd!hoe>0$0>0$1P") := ltac2:(zQ "20!prc!qhb@hb$1?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1s?1d?2lo?1m?2mo?2XC?2XB?2XB$0").

  Section At.
    Variables (idx : nat) (h lsth : schunk).
    Hypothesis HIDX : ltac2:(zQ "60!jk0!pkc!pl3!p0!jm3!rk2@3$3@1$2$0@3$5$0@1$4?2st?3idx@2$1$0?1h").
    Hypothesis HMAP : ltac2:(zQ "40!p0!hjc!rke!rq4@3$0$1@1$2?1h@1$3?2ch").
    Hypothesis HLAST : ltac2:(zQ "80!jk0!jm3!pkc!rr3!pl3!p0!rse!rk2@3$5@1$4$0@3$7$0@1$1?2st@2$6@2$3$0@1$1?2stN1@2$2$0?4lsth").
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
              /\ 7417856 <= CTX /\ CTX + 160 <= aceil /\ 7417856 <= pa /\ pa + 8388608 <= aceil
              /\ 7417856 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7417856 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
              /\ 7417856 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil
              /\ 1 <= nch <= nres /\ nres <= 1032192 (* [comment removed for export] *) /\ 7417856 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
              /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 7417856 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
    Proof. eapply rs_bnd; eassumption. Qed.
    Let BANDS : hidden ((T + 4096 <= 65536 \/ (7417856 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
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
    (* The rstep_postP components come in several shapes: some take idx/h/lsth/spv, some only
       h, some are fixed by the goal.  Their side goals are not all assumptions here, because
       this file's machine facts hold of `m` while the post speaks of `mr`: `pdis` carries the
       window visibility across with WMR and supplies the two lazy-set facts by name. *)
    Ltac pdis := first [ eassumption
                       | (match goal with
                          | HW : wmono asegs ?mm ?mm2 |- awin_vis ?ss ?mm2 =>
                              match goal with HA : awin_vis ss mm |- _ => intros xx Hxx; apply HW; exact (HA xx Hxx) end
                          end)
                       | (eapply wmono_out_wmono_l; [eassumption| eassumption])
                       | fail ].
    Ltac post L := first [ (eapply L with (idx := idx) (h := h) (lsth := lsth) (spv := bv_unsigned sp); pdis)
                         | (eapply L with (idx := idx) (h := h) (lsth := lsth); pdis)
                         | (eapply L with (idx := idx) (h := h); pdis)
                         | (eapply L with (h := h); pdis)
                         | (eapply L; pdis) ].

    Lemma recycle_sec_pass_at : ltac2:(zQ "70!kie!jj7!qm3!qq4!hsd!hoe!qr5>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
Proof.
      (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay that
         destructured rs_model's PRE-REVISION vm_maps conjunct (map_remove) and applied
         @recycle_sec_sreach at its pre-revision arity; rs_model was restated in an earlier repair
         (Bs/AS_SecRecycle2.v:58) to `vm_maps h' = maps_subtract (vm_maps h) a (a + msz)`.
         It is now plain text.  NO STATEMENT CHANGES.
         It is the twin of Bs/AG_RecycleSec.v's recycle_sec_arepq_at, which was written out in
         the same series from the plain-text sibling a donor tree:projects/openssl/
         echconfiglist_parser/proofs/lib/As/AG_RecycleSec.v, and differs from it in exactly the
         three ways this file's RSStep differs:
           - the machine hypotheses hold of `m`, but VISE holds of `mr`, the memory after the pass
             that rewrites the shadow of the chunk's user bytes ([wlo, wlo + wn) = [sh U,
             sh U + nsh (ch_used ch))).  recycle_sec_sreach therefore runs on `mr`, and every
             machine fact is carried across by AllocRep's Transport section (agree_on + wmono),
             whose side condition is always "this range misses the window";
           - the shadow run of the user bytes is no longer the pre-pass poisoned run but USH's
             `sbs0`, so the whole-map shadow array is assembled with sbs0 in the middle;
           - rstep_postP's eleventh conjunct is `as_cache_inited (a_st s') = as_cache_inited
             (a_st s)` rather than `= true` (this file carries no INIT hypothesis), so it is
             discharged by reflexivity; and its memory-relation conjuncts speak of `m`, so the
             round-trip munch is composed from the pass's own munch and the recycle's.
         Every literal is THIS tree's own, read out of its own encoded statements:
         69632 (= 0x11000) and 2^40 are Bs/AS_SecRecycle.v:35's AR bound; 6128 is its DISJ:50
         and CHDR:64 offset; 2^20 its NCH:43 bound; 2^47 its DISJ bound; 6942920 and 6942832 are its
         TPR:38 and RNG:39 bounds.  2147446784, 17594333495296, 2415881728 and 2201439137792 are
         this file's own BANDS (:166-174).  No cell address is written: SB32 .. GST keep the
         `AINST + k` form large_cells_of_arepq gives them, and hVISE and hCHDR are obtained by
         rewriting VISE and HD rather than by restating them. *)
      intros K. pose proof BND as B. pose proof ENT as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
      destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0).
      destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
      pose proof (proj1 AK) as AK'. destruct AK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). destruct K10 as (_ & _ & K10c).
      pose proof (proj1 AK) as AKz. destruct AKz as (_ & (_ & ATOPc) & _).
      placed. pose proof (SECP h HIN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). pose proof (SECP lsth LIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
      fold a msz in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9. fold lst in R1, R2, R3, R4, R5, R6, R7, R8, R9.
      fold T CTX sb pa in S1, S2, S3, P1, P2, P3, T1, T2, T3, X1, X2, X3, D1, D2, D3, D4, D5, TCX, Q5, Q6, Q7, Q8, R5, R6, R7, R8.
      destruct PNEW as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
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
      assert (A8 : a mod 8 = 0) by (clear - B; Z.div_mod_to_equations; lia).
      bands_as (BT & BC & BP & BN & BD & BA & BSH & BF & BL).
      (* ---- the pass's write window, and the one disjointness every transport below reuses ---- *)
      (* wlo = sh U sits one 2048-byte redzone (256 shadow bytes) above sh (ch_alloc_beg ch),
         which is itself 512 shadow bytes above sh a; wlo + wn is where the right redzone's shadow
         starts.  So the window lies strictly inside the map's own shadow run [sh a, sh a + msz/8). *)
      (* `wlo` is a Let of the OUTER section, elaborated before the inner `Let U :=
         ch_user_beg ch`, so it unfolds to `sh (ch_user_beg ch)` and a `rewrite E8` -- stated
         about U -- finds no subterm.  This one equation carries E8 and E10 down to the raw
         projection, and the two window facts rewrite with it. *)
      assert (UEQ : ch_user_beg ch = a + 6144).
      { change (ch_user_beg ch) with U. rewrite E8, E10. unfold kPageSize. lia. }
      assert (WLO : wlo = sh a + 768).
      { unfold wlo, sh, ASHADOW_BASE. rewrite UEQ. clear - A8. Z.div_mod_to_equations. lia. }
      assert (WHI : wlo + wn = sh (U + round_up (ch_used ch) 8)).
      { unfold wlo, wn, sh, nsh, ASHADOW_BASE, round_up. change U with (ch_user_beg ch). rewrite UEQ.
        clear - A8 E13. Z.div_mod_to_equations. lia. }
      assert (WIN : sh a + 768 = wlo /\ wlo + wn <= sh a + msz / 8).
      { split; [symmetry; exact WLO|]. rewrite WHI. unfold sh, ASHADOW_BASE. rewrite E8, E10.
        unfold kPageSize, round_up in *. clear - A8 E12 E13 B MSZ RR RR8 MSZU. Z.div_mod_to_equations. lia. }
      assert (WB1 : 2147446784 < wlo) by (rewrite WLO; unfold sh, ASHADOW_BASE; clear - B; Z.div_mod_to_equations; lia).
      assert (WB2 : wlo + wn <= 17594333495296).
      { pose proof (proj2 WIN) as W2. unfold sh, ASHADOW_BASE in W2, B. clear - W2 B; try acb; Z.div_mod_to_equations; lia. }
      assert (AGm : agree_on (fun aa : Z => ~ (wlo <= aa < wlo + wn)) m mr).
      { intros aa Haa Hr. apply GW.
        replace (bv_unsigned (wa aa)) with aa; [exact Haa| unfold wa; symmetry; apply unsigned_lit; clear - Hr; lia]. }
      (* ---- every machine fact recycle_sec_sreach reads, carried from m to mr ---- *)
      assert (rST : stk asegs mr lo (bv_unsigned sp)).
      { eapply stk_transport_pt; [exact AGm| exact WMR| exact ST|]. intros aa Haa. clear - Haa WB2 B; try acb; lia. }
      assert (rTST : stk asegs mr (T + 2800) (T + 3168)).
      { eapply stk_transport_pt; [exact AGm| exact WMR| exact TST|]. intros aa Haa. clear - Haa WB1 WB2 BT B; lia. }
      (* AINST is a literal of this tree (Bs/AllocRep.v:35), far below the window's 2147446784
         lower bound; lia cannot see that through the Definition, so it is unfolded here. *)
      assert (rSST : stk asegs mr (AINST + 136) (AINST + 680)).
      { eapply stk_transport_pt; [exact AGm| exact WMR| exact SST|]. intros aa Haa. clear - Haa WB1; unfold AINST in *; lia. }
      assert (rGST : stk asegs mr (AINST + 688) (AINST + 728)).
      { eapply stk_transport_pt; [exact AGm| exact WMR| exact GST|]. intros aa Haa. clear - Haa WB1; unfold AINST in *; lia. }
      assert (rSB32 : rw_cells asegs mr (AINST + 32) [C8 (wz sb)]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact SB32|]. intros aa Haa. cbn [cells_size csize] in Haa. clear - Haa WB1; unfold AINST in *; lia. }
      assert (rINST64 : rw_cells asegs mr (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact INST64|]. intros aa Haa. cbn [cells_size csize] in Haa. clear - Haa WB1; unfold AINST in *; lia. }
      assert (rNRES : rw_cells asegs mr (AINST + 112) [C8 (wz (as_n_reserved st)); C8 (wz (zlen (as_sec st))); C8 (wz 0)]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact NRES|]. intros aa Haa. cbn [cells_size csize] in Haa. clear - Haa WB1; unfold AINST in *; lia. }
      assert (rMTX : rw_cells asegs mr (AINST + 680) [C8 (wz 0)]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact MTX|]. intros aa Haa. cbn [cells_size csize] in Haa. clear - Haa WB1; unfold AINST in *; lia. }
      assert (rHDR : rw_cells asegs mr a [C8 (wz a); C8 (wz msz); C8 (wz (sc_size h)); C8 (wz (Z.of_nat idx))]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact HDR|]. intros aa Haa. cbn [cells_size csize] in Haa. clear - Haa WB1 WB2 BA B; lia. }
      assert (rLHDR : rw_cells asegs mr lst [C8 (wz lst); C8 (wz (sc_map_size lsth)); C8 (wz (sc_size lsth)); C8 (wz (Z.of_nat (length (as_sec st) - 1)))]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact LHDR|]. intros aa Haa. cbn [cells_size csize] in Haa. clear - Haa WB1 WB2 BL B; lia. }
      assert (rPA : u64arr asegs mr pa (wlist (map sc_map_beg (as_sec st)))).
      { eapply u64arr_transport_pt; [exact AGm| exact WMR| exact PA|]. intros aa Haa.
        assert (WLN : Z.of_nat (length (wlist (map sc_map_beg (as_sec st)))) <= 1032192) by (unfold wlist; rewrite !length_map; clear - B NCHL; lia).
        clear - Haa WLN WB1 WB2 BP B; lia. }
      assert (rHD : rw_cells asegs mr (U - kChunkHeaderSize) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz (ch_used ch)); C8 (wz actx)]).
      { eapply rw_cells_transport_pt; [exact AGm| exact WMR| exact HD|]. intros aa Haa. cbn [cells_size csize] in Haa.
        (* [a + 6128, a + 6152) lies inside the map [a, a + msz) (msz >= 8192), so this is rHDR's
           band argument: BA puts the whole map either below the window's 2147446784 floor or
           above its 17594333495296 ceiling. *)
        rewrite E8, E10 in Haa. unfold kChunkHeaderSize, kPageSize in Haa. clear - Haa WB1 WB2 BA B; lia. }
      (* SENV's fourteen cells sit at this tree's own literals (Bs/AW_LargeAlloc1.v), at
         bv_unsigned tp - 88, at ATSD and at CTX + 152.  lia cannot see through `bv_unsigned (wz
         ATP)` or through AGOT_VALS's length, so both are reduced first. *)
      assert (TPU : bv_unsigned (wz ATP) = ATP) by (unfold wz; apply unsigned_lit; unfold ATP; clear; lia).
      assert (rSEN : SENV (wz ATP) ATSD (a_ctx s) (a_thr s) m -> SENV (wz ATP) ATSD (a_ctx s) (a_thr s) mr).
      { intros HS. destruct HS; constructor;
          (eapply rw_cells_transport_pt; [exact AGm| exact WMR| eassumption|]);
          intros aa Haa; cbn [cells_size csize] in Haa;
          try rewrite TPU in Haa; try unfold ATP in Haa; try unfold ATSD in Haa; try unfold AGOT_VALS in Haa;
          cbn [cells_size csize length map Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in Haa;
          try fold CTX in Haa; clear - Haa WB1 WB2 BT BC B; lia. }
      (* RENV's twelve cells are all at literals of this tree (Bs/AW_PoisonRemap1.v), well under
         the window's 2147446784 floor; only re_got's length needs AGOT_VALS reduced before lia
         can bound its span. *)
      assert (rREN : RENV g b244 mr).
      { destruct REN; constructor;
          (eapply rw_cells_transport_pt; [exact AGm| exact WMR| eassumption|]);
          intros aa Haa; try unfold AGOT_VALS in Haa;
          cbn [cells_size csize length map Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in Haa;
          cbn in Haa;
          (* the side condition arrives as the un-applied redex
             `(fun aa => ~ wlo <= aa < wlo + wn) aa`, which lia reads as one opaque atom *)
          cbv beta; clear - Haa WB1; lia. }
      (* ---- the whole map's shadow over mr: the three redzone runs carry across, the user run
             is the one the pass rewrote and comes from USH ---- *)
      assert (SHDX : exists sbs, u8arr asegs mr (sh a) sbs /\ Z.of_nat (length sbs) = msz / 8).
      { (* poisoned_transport_pt asks for the WHOLE `poisoned m ...` fact; PH'/PL'/PR' are
           already in that shape here (their third component is only the u8arr over
           poison_bytes, measured in a farm round), so they are kept whole and
           the destructured halves are only what the shadow assembly below reads. *)
        pose proof PH' as PHf. pose proof PL' as PLf. pose proof PR' as PRf.
        destruct PH' as (_ & _ & PH). destruct PL' as (_ & _ & PLz). destruct PR' as (_ & _ & PRz).
        assert (rPH : poisoned mr (ch_alloc_beg ch - kPageSize) 512%nat kAsanHeapLeftRedzoneMagic).
        { eapply poisoned_transport_pt; [exact AGm| exact WMR| exact PHf|]. intros aa Haa.
          rewrite E10 in Haa. replace (a + kPageSize - kPageSize) with a in Haa by (clear; lia).
          rewrite WLO. clear - Haa; lia. }
        assert (rPL : poisoned mr (ch_alloc_beg ch) (Z.to_nat (ch_rz ch / 8)) kAsanHeapLeftRedzoneMagic).
        { eapply poisoned_transport_pt; [exact AGm| exact WMR| exact PLf|]. intros aa Haa.
          rewrite E10 in Haa. rewrite E7 in Haa. rewrite WLO. unfold sh, ASHADOW_BASE, kPageSize in *.
          clear - Haa A8; Z.div_mod_to_equations; lia. }
        assert (rPR : poisoned mr (U + round_up (ch_used ch) 8) (Z.to_nat ((ch_end ch - (U + round_up (ch_used ch) 8)) / 8)) kAsanHeapLeftRedzoneMagic).
        { eapply poisoned_transport_pt; [exact AGm| exact WMR| exact PRf|]. intros aa Haa.
          rewrite <- WHI in Haa. clear - Haa; lia. }
        (* the shadow array is assembled from the u8arr COMPONENT of each transported
           `poisoned`, not from the record itself *)
        destruct rPH as (_ & _ & rPHa). destruct rPL as (_ & _ & rPLa). destruct rPR as (_ & _ & rPRa).
        unfold poison_bytes in rPHa, rPLa, rPRa. rewrite E10 in rPHa. replace (a + kPageSize - kPageSize) with a in rPHa by (clear; lia).
        exists (repeat (b8 kAsanHeapLeftRedzoneMagic) 512 ++ repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ch_rz ch / 8))
                ++ sbs0
                ++ repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((ch_end ch - (U + round_up (ch_used ch) 8)) / 8))).
        split.
        - apply (proj2 (u8arr_app2 mr _ _ _)). split; [exact rPHa|]. rewrite repeat_length.
          replace (sh a + Z.of_nat 512) with (sh (ch_alloc_beg ch)) by (rewrite E10; unfold sh, kPageSize; clear - A8; Z.div_mod_to_equations; lia).
          apply (proj2 (u8arr_app2 mr _ _ _)). split; [exact rPLa|]. rewrite repeat_length.
          replace (sh (ch_alloc_beg ch) + Z.of_nat (Z.to_nat (ch_rz ch / 8))) with wlo by (rewrite WLO, E7, E10; unfold sh, kPageSize; clear - A8; Z.div_mod_to_equations; lia).
          apply (proj2 (u8arr_app2 mr _ _ _)). split; [exact (proj1 USH)|]. rewrite (proj2 USH).
          replace (wlo + wn) with (sh (U + round_up (ch_used ch) 8)) by (symmetry; exact WHI).
          exact rPRa.
        - rewrite !length_app, !repeat_length, !Nat2Z.inj_add. rewrite (proj2 USH). rewrite E12, E8, E7, E10. rewrite MSZU.
          unfold wn, nsh, round_up, kPageSize. clear - RR RR8 E13 A8. Z.div_mod_to_equations. lia. }
      destruct SHDX as (sbs & SHD & SHDL).
      (* ---- from here the shape is recycle_sec_arepq_at's, over mr ---- *)
      assert (hSPA : hidden (bv_unsigned sp mod 16 = 0)) by (constructor; exact SPA).
      assert (hAR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40).
      { split; [exact Q2|]. split; [exact Q3|]. split; [clear - B; tauto|]. split; [clear - B; tauto| exact MSZ]. }
      assert (hSBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a)).
      { constructor. unfold disj, kSpaceSize, kPageSize in *. clear - N1. lia. }
      assert (hSBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil)).
      { constructor. unfold kSpaceSize, kPageSize in *. clear - S2 S3. lia. }
      assert (hTPR : hidden (6942920 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP)).
      { constructor. rewrite TP. unfold ATP, AIMG_TOP. clear. lia. }
      assert (hRNG : hidden (6942832 <= ATSD /\ ATSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj T 4096 /\ T + 4096 <= aceil /\ T mod 16 = 0)).
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
      assert (hSEN : SENV tp ATSD CTX T mr).
      { replace tp with (wz ATP); [exact (rSEN SEN)| unfold wz; rewrite <- TP; apply Z_to_bv_bv_unsigned]. }
      assert (hLSTC : Z.of_nat idx < nch - 1 -> rw_cells asegs mr (lst + 24) [C8 (wz (nch - 1))]).
      { intros _. apply (rw_cells_app asegs _ _ [C8 (wz lst); C8 (wz (sc_map_size lsth)); C8 (wz (sc_size lsth))] [C8 (wz (Z.of_nat (length (as_sec st) - 1)))]) in rLHDR.
        destruct rLHDR as [_ LH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LH.
        replace (Z.of_nat (length (as_sec st) - 1)) with (nch - 1) in LH by (clear - NCHL LTI; lia). exact LH. }
      assert (hCHDR : rw_cells asegs mr (a + 6128) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz (ch_used ch)); C8 (wz actx)]).
      { replace (a + 6128) with (U - kChunkHeaderSize) by (rewrite E8, E10; unfold kChunkHeaderSize, kPageSize; clear; lia). exact rHD. }
      assert (MEQ : a + 6128 = mch) by (rewrite E9, E10; unfold kPageSize; clear; lia).
      pose proof VISE as hVISE. rewrite <- MEQ in hVISE.
      assert (hWIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x (a_S s) = true).
      { intros x Hx. destruct ASV as [_ V2]. exact (V2 h x HIN Hx). }
      assert (hHAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true) by (apply map_has_of_In; exact (ak_secmaps s mo AK h HIN)).
      assert (hNOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false) by (intros x Hx; exact (IL3 h x HIN Hx)).
      assert (hNOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false) by (intros x Hx; exact (ak_sec_noacc s mo AK h x HIN Hx)).
      pose proof (ak_zrsh2 s mo AK) as hZRSH. pose proof (ak_shrf2 s mo AK) as hHSRF.
      pose proof (ak_shmc2 s mo AK) as hHSMC. pose proof (ak_shna s mo AK) as hHSNA.
      apply (recycle_sec_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 (wz cb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mr
                lo a msz (sc_size h) (Z.of_nat idx) pa nres nch lst (nch - 1) ATSD CTX T sb (ch_used ch) actx chunks (b8 3) (b8 b1) sbs g b244);
        try exact MIR; try exact rST; try exact LO; try exact HI; try exact hSPA; try exact hAR; try exact hSBX; try exact hSBR;
        try exact hTPR; try exact hRNG; try exact hPLC; try exact hPAR; try exact hNCH; try exact hIDX; try exact hLNTH; try exact hLR;
        try exact hPLCL; try exact hLSTA; try exact hDISJ; try exact hSEN; try exact rREN; try exact rSB32; try exact rINST64;
        try exact rNRES; try exact rSST; try exact rMTX; try exact rGST; try exact rPA; try exact rHDR; try exact hLSTC; try exact hCHDR;
        try exact rTST; try exact SHD; try exact SHDL; try exact OK; try exact hVISE; try exact NW; try exact NWA; try exact NOV;
        try exact hZRSH; try exact hHSRF; try exact hHSMC; try exact hHSNA; try exact hWIN; try exact hHAS; try exact hNOL;
        try exact hNOACC; try exact ATOPc; try (clear - B E13 MSZ RR RR8; acb; lia).
      cbv beta. intros msF' mo' P.
      destruct P as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & OK2 & VIS2 & MO2 & MU & WMO & MI2 & SEN2 & REN2 & ST2
                     & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & LSTC2 & TST2 & SH2 & GONE).
      assert (SPV : 0 <= bv_unsigned sp < 2 ^ 64) by exact SPR.
      assert (WSP : wz (bv_unsigned sp) = sp) by (unfold wz; apply Z_to_bv_bv_unsigned).
      (* The recycle's munch starts at mr; the pass's own munch carries it back to m, because the
         window the pass wrote is inside the map's shadow run and so inside rs_W. *)
      assert (MUW : munch (rs_W lo (wz (bv_unsigned sp)) a msz pa nch lst T) m mr).
      { eapply munch_weaken with (W := [(wlo, wlo + wn)]).
        - intros x Hx. unfold rs_W in Hx. cbn [outside] in Hx |- *. split; [| exact I].
          clear - Hx WIN. tauto || lia.
        - intros x Hx. cbn [outside] in Hx. apply GW. clear - Hx. tauto. }
      assert (MU' : munch (rs_W lo (wz (bv_unsigned sp)) a msz pa nch lst T) m m').
      { eapply munch_trans; [exact MUW|]. rewrite WSP. exact MU. }
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
      apply K. unfold rs_gpostP, rstep_postP.
      exists sN, y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros sc Hin; change (as_sec (a_st sN)) with l1 in Hin; exact (proj1 (proj1 (L1IN sc) Hin))|].
      split; [reflexivity|].
      split; [intros c0 _; reflexivity|].
      split; [exact OK2|]. split; [exact VIS2|].
      split; [post arepq_after_rs|].
      (* awin_after_rs asks for two facts that are not assumptions here: the shadow-inside-lazy
         inclusion and the map's absence from the lazy set (hNOL, proved above). *)
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
      - bands_as (_ & _ & _ & _ & _ & BA2 & _). unfold addr_is_in_mem, kLowMemEnd, kShadowOffset, kHighMemBeg, kHighMemEnd.
        clear - BA2 B MSZ. acb. repeat split; apply orb_true_iff; (destruct BA2 as [BA2|BA2]; [left| right]); apply andb_true_iff; split; apply Z.leb_le; lia.
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
  Theorem recycle_sec_pass : ltac2:(zQ "70!kie!jj7!qm3!qq4!hsd!hoe!qr5>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSecPass ()) ["HCW"; "RSStep"] "##PIp'0h04HIDXh14__x1h21ni001nh31Hh43idxh57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;1ah<4cstrh=5cstr0h>1hh?7heq_mchh@!s0$wlohA6!s0$nhB1lhC3s12hD1EhE2ELhF3H12hG5HLASThH4HMAPhI1KhJ2NEhK2WQhL2_HhM7__sat12hN!s0&3hO1ei011ehP2l'hQ2l0hR4lsthhS1mhT3mo'hU4msF'hV1oi021ohW1xi031xhX1yhY3z12i041sp&0p;2p;4p;3p;6p;1p;<p;7p;5p;Bp;8g04<nk20YTg04>@j2jTg07ACj4YTg00SMj39Tg043fk60XTg00iEk10KTg00jIk30ETg02TgR0j1\Tg02LVk105Tg02VIj1cTg06jFj1nTg02Xdj1hTg04B6k10RTg00A\k10JTg00K;k10GTg02WVj1aTg04C@j2`Tg00IbR1j24Tg04DKk30=Tg02Ugj2LTg00=0j30j1dTg00Bjk10!u$$EZk10!sY$Fij2|Tg04H6j1{Tg002Ij1ATg00FPj1KTg02`0j1wTg02f4j1tTg00W3j1@Tg006Bj28Tg004Oj1iTg00Rmj1eTg00?^j6!u%$UIj3RTg07imk20WTg00Nhj1DTg03;2k10VTg07jLk30U!s0$lR2k20QTg07kHR3k20PTg046Wj27Tg05DAj2ITg059Ak10ITg03@4k10FTg02YnR4j15Tg01E_j2<Tg00H8j2JTg05I@k20D!s0$ck30CTg07Ecl<^!uo$nj1TTg003Lk10<Tg02nhj2]Tg03=\j1Q!tJ$Xk20;Tg00J?j2[!wm$@R5j2CTg02hOj2UTg04LAk20:Tg03>Ak20!vA$J[k207Tg00OGj2ETg00P0k103!s0$Nk202!s0$ok301Tg00QXj3F!vr$Aj2O!z1$mj2!v_$TKj1}!s/$ij4~Tg00UGk100!s0$ej1zTg03QCj6yTg00VPj2Z!w~$Xj2!zg$X;j3xTg03GRk306Tg07GSj7vTg00YIj1u!s/$kk20?Tg009_j2MTg00ZMj2sTg00[9k30!y=$[Xk40BTg05BYj4bTg07MfR6j2r!x/$ej1qTg001Nj6HTg07lJR7j2p!s1$dj5oTg05E:k30LTg07mGk70MTg03Kmj5mTg07nck70NTg0806k60OTg02^0j3lTg07FmlBf!uH$^j4gTg00^`j7k!uu$gk70STg00_Dk80TTg03SPR8f0R9'Lp=6f3R:f2R;f1R<5R8;09p=3g00`HR=?0<9p=1%A9#Ap=;18<9,8;p=BAR8<9p=SAl!s-$>1]89p=21M=9p=?g03amR>P>P>P=P=P=g07LcP4!s$$1g07MCf5R1f4R?P:P;P<P9MBfp>0@P!s[-P6!sX%f6R6g07NFP1P!sV2>g00cQR@/C9p=:P=P<g00gUP9Cgp=N!s4$00RAg00b1RBPBg00bQRCP9g00c1Fkp==P;PAPBPBPCP<P9K0Sp=V!so%3T[!so%PP:!sJ+!tK$L0Tp=_!tv$7P4P5g081:!tl0<^p>0Hg07Nmg07P420Y<9g01XNR5g07JNR7p,1QRD1j;<CY[]T]Up,5HCEILp,1sREp,3mchRFp,2XCRG59=RHp,2XBRIp,1mp,2RQJ0X&0KE@0EHIP>P8%\8!sK$stRE$05RJP<%69C3RK%c9p,2chRL#nRM'1RN%h9RO&0RLRP$0JRQ$0GRR'1%a9g03bLRS,`O/4S'1%\>ROg00ecRT:0=JMRU1L><30g00=JRV&09Qg00_hRQ30&04LRW,|E=0VQ%{Lg00>JRQ#ARX#;RY#ARZ#;R[#A#;#;#KR\'1%wLR]14W\'1%tLR\%@Q#@!s$+!sM$,4W'13B3BRW'83BR^3BX>8X4>P5P7PDp,3msFp,2mo'jCYRDPKPNP^PD%c</1M%h;RM/1R%a;1`MS!uK$1L>:90OU/8W3B%i8RW%e8RU70JROPWPJPHP9P6%61RSC3XBWP:PUP9EGPHPUP1%6?C3P>!s3$9%66RMC3g07_QRR]0P6AR8UTR^=0HSPHP^P0P8p-0R0P9PRg041Yn101102000210!s#$XOHR^g07e3RSPM!t8$R20WR9RMb3W0PHPU%D9f7RN#6C3PH%D<,SUP^PSf8RS#6!sX%P!sS$X4>P9O1n01!t'%20010100P9O1b0WD&0VOROePOB0U8J9A989URO,><90WJX;8-0Q8RMXPWRR-0PWP3PWPRPDP9P2P81>;O!sN&PDP91>?!s5$PWA98<!sm$1RDPHP9%29%DTR2'7%6;RR!vd%>%21R3%2O'IR^PHA98;UR7,>6R51792PRC3X2>&0IPRP#?p,2wn/1PRPeR_PP&0F]R]#?p,3wlo/1]R]eR`P]%?\11F\R\eRFP\%2SRS1IS2Ra/72Rb50>%5SRc%KQRd,4cRe/<d,J@Rf'1P>P=%d>P4%d=%5<%59'1A0><920D<940CXX>XW>PSPc%?cR4PbPf1<<9,J@XS=X2=PaPePSPcP4P2Pd%?dR4J0@P2PdP4K0>M<^%TY$0<p,4sbs0']RY#QR4%5Y#:RYf9#2Rc#Q%5cRS#:f:#2Re#5Ra/4d/<dRf-0;@1[@f1J@fRb/1f'81Cf@A0=b@'8'Uf;#2#5!sT%,J@P=%T[p,2sp+0:R[%KZRZ+08Rb%:[%:Z207[Z#:[[RZg00e7R[%D2Rf#D,E=&03Q-02=1E=fRf601=1E=TRg5F=Rh5F=g00fBRi'O1E=2=F=g9F=f/Oi1Ohi%e[Ri59[59[39%i[R[P=1W=;P<%}=C~&00=Rh%z=RfPf!#6F'!s0,?Ey1Z=XRX1Z=QRQ1X=dRA5x=>06=ARA'N,=f5Vf1X=@Rg,PA,=f1NXg!s<%Fv%uBRBPf1PgQ,=fPB1NQX,=fC_C_20?fCRCP9P;g00=jRX,MV1s9;=0VXdB0A=@<H0BRXb6b8b9X1=X:=X70149!wF$V,1<,8;1CV@A0=<!w9$%:<11;:[[^1=^:=^70P9f>R0#2#5RV!wQ&[@P;PVP:P?O5b5bNbYbFb=b<Cbb?b@bA1I32/7290>3P>%26R3!{r$:URU,>NP9%6:R:!{q$PH1733,S7A0H9:XVHP>PT!#3~$P!sH%1MHR1r33%q3EH1S53P8P6P7P3P_PPP`P]PFP\1pcc1CSSPcPS%?SR\PcPSP\J0HP4PY%Qe%:aPbPZPiP[1W=<Ph1PQ!vn$CP!v<,1C99^1=P9f=R=#2#5O1b5bM!uP/DoEH!uT&P9EGb3PHPD17^2%6<R^C3e%2DB0L81OEHPJP9EHPHPJ%2J/72P^C3f?P0P;P=f<P9fAK0MbGWEXR8P<P9O2n2001104000121103101XCMXQW!sF<4bCbJWLWHX0KDm!#9+%EPGPIPLP9p,4CHINp,3SECK0NJ0ObKWIo"). Qed.
End RSStep.
End HCW.
