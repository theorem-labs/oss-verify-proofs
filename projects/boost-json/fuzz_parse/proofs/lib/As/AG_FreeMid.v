(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_LargeAlloc1 AW_InitCache AW_IAInit AW_FreePre
     AW_Refill AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AS_Free3 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_ColdModel AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 AG_MallocCold
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 AG_Free8 SecLazy AG_FreeModel2 AG_Free3 AG_Free5 AG_RepQ AS_Free4 AW_Enqueue2 AG_WriteSet.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_FreeMid () := KReplay.lz_vm "#'}oC47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?Krespectful_per_oblig!t3$_1I56Stdlib5FSets<FMapPositive;!s/'Map4tree00C89OSSVerify!u:#ofs:boost_json:fuzz_parse3lib3Lib2Nd9ex_elimF2C13~~~!sj`3!sj]:ex_intro!sk+4!ur&9micromega5Tauto5eKindI!sE;8GFormula00C4ELinuxProcessSemantics5Riscv7Prelude5bvma!wi-4Init5Logic8eq_ind_rI!sD19Datatypes4prod00!sF=list00K!sFA1c!vPO2As:AG_FreeMid7ARHEAPQ!wAV2As8AllocRep4a_st!sjY7AG_RepQ7qbounds!sla5ARE!uD'!xS+5Lists4!s+#5NoDup!xK#!sB52In!uw\3alb!z8'!xy63iff!t&\6!wj%!wic!v8#!v7'!tq7and!~cR!w>-=!t+#_of_!wF-K!t5<1!~BXand!#3//I!ws]!|d#!v&37Numbers7BinNums1Z!v,U8AsShadow3mem!x~>5proj1!y$]ast_ok!y$b8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!sl-!#<=&6ZArith6BinInt1Z2le!sB>t!v,]region!vwgpclas!wigA!tb&s!{L$!swf?!sw&junk!su-7!suN>Asan!sv$Model:ch!sr#li!#:0Z!{?,!sp%!tdh5as_tq!sne7qc!uQg;batches!uSmg!uS&K!#6O>1!t4_;kNum!#G$%!t:%I!u&_!xK$!#8U&!y:]placed!#74[7!so$Wf2WF!sg&!#8~;2!v[_@as_internal_init!wtF2!#==S4TacX2b8!t'&!seS5Cells4cell04!vnV!tQ,wz!tQf3!vBC8p!#M\%02!sKG1!t\`2!uHf1!vs&!#:M:3pow!sC=sub!wUUStep8rw_!tN#s!vo3!#L>13nat!vi?1N02I45stdpp9bitvector;def!{8#ions2bv!#MFC2!va`5!#37a5zbool!~J3!#KM$7!s+#Def6repeat!sE;3map!tN]a_ctx!|kZ2Nd;!#HU'17!sl]!#IC+4!zQCaddI!ww_!#80Y5ASegs5asegs!xab7AIAINIT!sm%!#UD<!y/#!z|/!#3P<3!tZ\6AFLAGS!uHdC!smg<ASHBASE_CELL!wm_!so#ADOW_!st#!tcb;AHIGHMEMEND!sqb:ACANPOISON!yYeNITE!t_c8ACTXSIZE!sndTSD!{9,!#7w@1!wQ^ALLO!z%h6AHOOK!sleDYING!yxdREALMEMSET!y-d!smjGOT_LO!smb9!sm$VAL!#3fdPAGESZ!zedSECNAME!uNdPRIM!sof8ATLSSLO!wvc4!}6#!tZdLSANDI!wrc5!xc#2!skY9AW_IAInit8ia_after!soc;ia_pristine!srV!#@-37!t_Y=!v='Facts5ch_lo!#4'bch_end!sl[!#bx%5acei!#EV&!#P_]<ch_a!s4#_beg!su&!#CJ:6modulo!#hF72eq00C!#Tw`_rz!uGe;ch_user!uF-!#ZF^!st%d!spe8round_up!xgb3nsh!wnB3mul!#_aa!}2#mary!unfch_!#c=#!|E_Kit6carv!wOg:!#ds$size!sse6as_sec!tdfsc_map!zti;!ss&!uZ,!}j:x!#p&T>!#5h/2;record_ba!#5%c4aap!|+&K!#}o4=RingM!#}}'Psatz02!sO6:Z!sL+;!|#%!tS$!sR86VarMap1t!sDB1I!sD?0I!t}C7!$#u'!t567Env!sT#5PExpr!#Y/-!#HU16option!tz8!sk21!sIE3!$&;;8B!t}&K!#88:1C!w>@=Z!sn$CheckerC!vZ<4find!sqAC!sq0_sound!#Ab\!yx#_env!zh&!tH59SatDivModCZ_mod_nonneg!s,&!#e=?3!w9>3Pol!wZ8!{<84!x'E4K!z1L1!|2N3!tHE5!#Ay`!#r5%geom!#35X!#4-1:!#4-%ex!#pZV!#DU39!#4-P6!#3<?!vl7!$3f24!sJF!snG5!sJF8!#]J<unit!#4K7!sj%4kind!{#F3Op2!t}#!t5@!#VGS!#[c$8AIMG_TO!$-|&!#=L^s!#s<0!sq^9kPageS!#<W,!|{L0!}ON1K!#bM@!waJ!#Zb\5a_thr!#?3>or!$07V!t,&4a_sb!#DP^!tq&op!skebot!y-e7as_qmax!spkin!zjf!sp#cach!#Fwe4zle!taf8qc_byte!#kbb4a_pa!sjY:AsDepotInv4d_nb!slg!{2]!#G2%2!#OK'!#u~?;bv_unsignedK!#5g^q!$+w#!#yO'!#3S&!$AM,4last!{-`qb_addr!{xfqb!#N}i8qb_coun!~Of9!sq#hunk!{1c5w!$27Y3Lib3Arr6u64arr!shZ5Frame3st!$/0&!#m';appI!#{@:Fora!#w[#!y`62hd!$GD8not!#7^]kobj!#3Lbdis!sjc5a_f!~]+!yfO8HeapCeil5h!#`i,!#3GZ;!#aV#_fact!zOZ9!uH'X@sh_!st#ing_rang!}/'!#\n:7div_mod!#]7<div!sC<=mod_pos_!$Oo#!sMAneg!sM25!#@{#8PreO!s/#1Z;!t[#0_r!#J@#!sL=!st#!sL3!uN4compare!#J<J7!sOK!#I3F7!sJF6!u1<>pow!vs$!#R#$!sN<:!sN#!#RK&!t>4!#Oq17!#3cS!$,O0!$[0]!sl-0!slh6!|~b6AHI!#vx+!#a?^kSpac!#Jp,!ss_BkQuarantineMax!s{vin!s{i=kMaxCach!#Mb-!#@`e0!wXgB!sq#!u^i;!ss%C!#?[h!st'!#j~,!st^@kFreeArrayOffset!sygPtr!sx$Reserve!|u[!#:&%8AFS_!$-x+!#Ww;:!#7Q$ison!#Sn7!#Rz55!#R575False!$es3!sC%4Tru!sB#!uDR=AW_M!#vs#Base4IENV0!#4tZ!#C5%mkR!sg&!#JN?7Z_to_bv!t5T8PropExec7seg_r!#`KW!sn#6MState2MS!sgZ4!tS#3ev!$RX[!$ij$18free_plu!sn[!#ns&SHA!$'I&!#k~;length!#|F<of_nat!v&T3Arr5u8!#Ib+!#Lx^ch_s!wa#!}Wb4junk!xJZ3Mem5wr_a!xK'!vO<to!vOT!w{/8po!~x#!#yD'!~:76!$qm$!}GZ?stk_of_!$L`0!ssU!$F?#:!si$!#RQ-!u#13Nat3ad!#H>=max!$tJ8iff_refl!#oq5;Zify!$Y^%3inj!sIB5mkrel!tQ<8max_spec!smB;rew_!td%!#JA<;le_gt_cases!wgZ9!wg#spli!#3OY<!{W$WalkKit!ss$!xV/!u/24Znat5Nat2Z7inj!uV#!wU87!uo#sym!#vv9x!#f>T9AG!#9a%9!$e1#stk'!#9`_!ua$merg!$6Tg6!skg!$T9[S!#8Y$;!#8Y#head_W!sqY!#=g0:icpt_cha!#f2'!#4VTUnwind6utrace!uVa4?!uV$append_arm!sub=!su$mi!#TS#!$av&!|L_6hidden!#b['!x{S!#?:%<!#d7&_!~3Y!sq#9LiaTuning9zify_don!wD\!#9b&!$#Z#su!#g8[!#@?$3A!$kq&len!#XB%!#8Z%!#3r%!#_H,:!#?W$!xb#!#6mA7!#6m%!#4`=9i!#V4'!z@hmi!u0&!#I3;!$-f&0!t?bcommon!t?,!%/G]=!u8'_g!su+!#6@Y5munch!siawmono!siZ3Mem7mem_i!$/-'!v6R7AW_Put19put_f!t_#!zI'!#?}4!$gSR2As;!#pY%Hash:d!s0#_hash!tzY!#qN,7d_putid!sod5!so$!smeDEPO!$aD85Peano2le!{jW!zs%29lb_remov!#W\e<am_!{h$ful!#hhY=!|['!sv#2!#<b$tail_!$1~[!#@h&!sx$?same_but!%#z%!uje;syscalls_of!tqY;AW_Enqueue18enq_r!$gk]!#8U%?arepq!$S&$_!$@~'!y;\?!y;+_nod!$J{'!zL+!%DY4?eq_p!%Eq#!s,#xy!tI\<!tI,In!tFEIr!%Fe&_!s0,!tP%!s\>F!sR0!u',!sY4>!sY+_Prop@and!#KM#m!s=&!#<U66filter!#S}_as_!$&p-!vk[!#Wu$st!#IS&!#>S6in!$IK#!#KC/!%Js:?Equivalence_PER!w&?Ntrans_sym_co_inv_impl!vX@9!vX%_!%AaV!uh&!#3H$old_!#H5Z<!#4@-3qch!wJb7!#?[$!$w{3!#O&,9!#b+#!#VVW!#La/!%M>f1!#48a>need_new_f!uK#!wJf8!sx'!tha1;aim_of_!$Ov+!}Y_>addr_is_!|N#!%Bm'!sw^Aset!%0S6!vZ`>!#Ew'!#`T]9AG_WF!sz#9!#>+$i!#K+'!#Z%:4ones!sD=la!#}Y=9!sD#_!sg$!twR!#?30?!#@+&!#Hn#en!|']!#x_+2!#z;^!%VE'!%%R^!tZ-!#{%]:!~M+!tY[!#k8#8evt_!#K;]!uF16!slg19!#3,a:!#7V$!#eu]!#6M-!uJ'!#dTC!#TCD6!sK$!$Zf<!%[6$1!$6X<fst!#=G>M!#=G$co_!#iZ#!#=F2!vnT!#wB&is!$ly$!v$%!#U5;!$~L#0!uz68!uz#Inst@!#ow$_!#lU$_eq!$1/+!#3H#8!#M5#Na!#ip;!#eG2!sI#!#A&C>iff_T!v9#!%0+#!u~\5AINS!$|ycOI_QMAX!smb5OT_T!%_}b;OI_SPACEBE!%%&b3AT!%\p&!$#<_ChunkHeader!$+^ic!#;~#!$+^fBk!s6#Heap!#:A#agi!$lNeI!s{+LeftRedzon!t&/K!urf1!#4q;!}P+7Inj_Z_Z!#6%S!$$6%iv!#GE%!#oI7!$&-$1I!%jQ9?!s<2>!%ja#!sE+=machine_!x8&!x}`a!x}0!sq`effect!sqg=!#W9%_even!sx+!#50D=iff_!%s,6!#Od:!sV#e!#Oh+!#O%67ex!s2#b!$\GA!%P|_?!$1<#c!#8W#!$Oah8pc!$No/!#4vQ!%Sm&8WF!#Te^!sm+co!$PMj6get_p!#3oe9!v@#!$Q>-!sr^<ch!sr%!$z5,!vIR!#LS/6tq!#P,,!tg^4zidx!#67e!%d?$!#67'!sq^7upd_nt!#W&[l!#<N%a_L!sie!%7rb4a_A!tU\!#YD/s'!smY!#eQ,29en!yM$!#}t'!#4|52tl!$D\`!~l$!#8}g!yj&!%b0b7a_!$f%i9max!#4U/!v^63rev!#88_!#d6&!#X^#!%0ug!%m$%!%/7g<as_space!#4w\!w_%Kit=!tg,_eq!ssbB!#;h1!sxY!$%|#!$8y#X<!$9h&!#ms\!#:|-!$$7,!$4C8or!$s[ZKit<!%7:$!#<y^!#9V&!$~L#@!sv&vs_!%y:$!szf?!sz,!#zj#!{@fget_!y[%!sse=rg!#^z%rray!wpB2!v$S!%&K1@!t8#ch!v&#!%&U$!{d[!$'m/newhit!$4H^!wu%5B!#iH'tru!#{2`!um/>!$10#_not!w0$!yjq!t&$!una1!ve%last!#^Lb!#`+,5!sl]!#oN+8!y7o!$1~f@!sw/!$2%,!$G`;eqb!~J`as!~I&!#H]e=as_n_r!$Y?$!u03!&B|A1!$wb_9as!$u3aG_WFHit6WF!%6iY!#oE/<WFQ_!x9'!}Ga!uV$>!sr'!#q4^!&:c&3WF!#`@Y!%GB2!$8x#_ag!#3|[!#3%&4!$,M/!vR\!#5n0!#4t&in!#B:$!sz[!#ri-B!#ri&!}Y'en!yB]!$2}$A!sn#!#AI$of_a!&3rX!#mD2!&#}Z!$}6$32!$ZR'!#K1_!#3`$!#K1Z:AS_Refill16rf_au'!snd7rf_mfa'!t_hnf1!t_hn!{V\!t_2m!v@f4!t_#!sl&!xi^>rg_mapped!%]C#!sweArg!#r[$at!szlD!ts,!#Ey2!#O3_rg_nu!#3-$!#EX[l!#X8'ri!sj%!#?<cr!xP$!#?<,K!#i~I3Run6config!$[$V!uA&X8awin_vi!%'vc:!&HX#x!&Bu\!sq,7AMODEL!#u]b6!sm%!t\dakerne!$7H'!$p9>D!%;a,_in!%-w%!sY@:b!%-u#ulus!u`\2FA!vJb2RB!sh%I!#4T]R!$tB-!#[^^!~W,_base!uR_KitB!su2!#Yw[!#8$1fl!#9ad8rf_tota!#Q&Y>!#Dl#!sp#!#5;%!#<8#_delta!#5;dZr!sj[!#NH$3E!w@$h!&S^$!#5>#!$a4+!s{\@!s{3!z/V<LazyRestrictE!$Ol'materializ!#bkW6!s|#SR8hid_s!$X/+!tg\8r!s/&!vPV!#|m+7outside!x~b8!#Jp#_o!$hm[!#;?$75ZH!%zm]!$7+&rec_vs!&?4Y!uM1app_!$r0[!uM0hi!woZ!#Y;0!$Hv%I!~jTW_Large!uQ$14S!#74-!$92Aeq_!&gL^E!#gf'!$8s#port_p!$lTY!u=81!srY!#:;3!#7WY!#>K+;!#@%%_mat!z8b?amap!$J?#ledger!sud!&^V%visibl!~Mc7ABUDG!&8''!#=d]7as_!u`#!spfmp_k!$J|'!#}Z^5m!%h&#3!spl4!uTi!#@|,!spb!%'~-!#JoH5!$ug#8m_vm!wu$!s]P7vm_!s\U;vm_noac!s;#!#;m\:!#H7&!%R`W:!sq#L!}8$9nooverlap!sna>entries_nowr!ssX!uV1eager!&20Z!sq0;pages!#EH^!#DN,P!#;6'!yxQvm_limit!#7+\:ak_resf_!tPY<map_contains!tT]7ak!&3x#!vgY!#T1-k_zr!%f=[!t_1zr!$uKZ!sn,6ak_l!sm[;!sm$Budget6pusage!uNga!%pt[!#`g1!%&|Y3!%+b+6r!$;|-!#rc;ltb!zUQ=!#>N#subtrac!|+T7Sec!~I#:nonvm!#KF-!#79S!#s3'!|dQvm_m!&8\#ase!saQ6vm_brk!xH^4rf!$7P+!$$W&!%gE1first!$mR[7C!#on$!#R#%bund!#BCZ!#Td18!sy%!#8+&K!#78Z!',1#!$kga7!$<0$mR!smb8ZR_stac!'+VbC!%mm$!#Jv5!}t[;!}t%!$L|#!tk[!$#O%I!vJ$!%#v#!y+&!%:?0!t#\D!t#7!umZ!#U[$;!%1s#!ve%!tkY=AW_!%,[#!sv%!%01$avoid!yAbF!#y\-!ue&!#q3[;AG_WriteSet4avm!#UuY:!#xW'2<!u`%!&|Y$!stY!#:h+9!ss%cov!vSbDalb!vQj!sz+4win3!#3Ec!#lt#!sm'!#^|U;lzok!#IF%!slV9!sl#NodesFlazy!so&_okb!#H\0!uWR!#<L&?!#<L+!#?y_!#8O&3Damodelx!x;0!wKa8<!sz'f!$+2[!uf'>!uf-!#XA[!ss'@!ss-!#48-!#L=[L!#f87!#Qw&!#3Gc9avmx!#B$-!#61_6!#6'#!%71a!#<G#!$DA-!ta`8d_sb!%?=\!ss4n!ssl?!%@5#!#>5+!vT[!#<?$2;!#iz%!$KfY3!%F@%2wa!x,b4AGR!$~cZ!#@O%C!%jm%_!#yb,!|WV!$<[2upd!$<\$!sre6s!$b5i!so$t!#wTY!#H419!#t0&c!z^[!$9%7!$'F&e!#o~b;!#u$#!#jd#!&$1h8!sl]!%+-+6!x3V!#=_%Bevt_sreach_!#<y#at!uNg31!uNf2!#}Pc4=!xh&!uX%!xkb@!ss&!$Y;%t!uZg13!uZ[!|F'1D!te0!$@Wc!z[-!uW&!$?oO6SR!w1#6!w8%!$deW!zY&4lzok!#urI9!u'#!%-e#C3!$1>$7tactics<!$uE#al_help!|0P4Scfg=hunspe!yY#cf!$aV%I!#Y,O5!#4:#!&tp`>!&&]+!&,BhA!sw,Map!szi<kUser!su1!|yT!#NB%;PCLAS!&'V-!sq\?REGIONINFO!sug8OT_CACH!snc4OI_!%14b!'>5$!%3W\!%hV%9ALOWSH!&9Z'!$K?^7mapping!$p>f!#w\%!sp&!#xNe2!spl6!spl!#>?&!#3ZO9page!#y4$!tP^;kR!$P4#!}f]!#m]/B_PRIM!so%!$GX]4fr!#gK&!#6gP6VmMaps!#6h`;kHighMemB!&{tg!st'E!$%F&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~k23ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~o63mem37Corelib4Init5Logicsa3and36Stdlib5Lists4Listu42Insa3iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~hg25AREPQk23albu45NoDuphc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_FreeMid3HCW~~~~~~hlc7ARHEAPQhg27qboundsk26ARHEAPk24a_st3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshs6dmachine_state04Npos35stdpp9bitvectorbdefinitionsih42bvsa2ex69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~ijc6effecthc6optionsa2eqijc6astate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ipf5asegsijcdsyscall_eventhc4None79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_Free2~~~~~~ivb9lb_remove79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAG_FreeModel2~~~~~~jk6bfree_tail_m79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~jp8fsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AS_Free4~~~~~~jufffree_common_mid79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAW_Enqueue1~~~~~~kk08enq_regs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~kod5DEPOTijccam_free_fullijcdkMaxCacheSizeijcbsyscalls_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lg62MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~lk97seg_romih47Z_to_bv99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_FreeMid3HCWaFreeAppMid~~~~~~lpedfree_app_gmid79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~lve3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mk03mkR99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_FreeMid3HCWdFreeNewHitMid~~~~~~mo3h0free_newhit_gmidmk03ivlhc3app3h5LinuxProcessSemanticsfLinuxProcessSem5Statemv75Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~nie4cellhc4consnie2C846Stdlib6ZArith6BinInt1Znnf3addih4bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nqd8rw_cellshc6length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~nvd2wzk23a_Lk23a_Shc3nat37Corelib4Init3Natol03sub37Corelib5Lists7ListDefom93map3h5LinuxProcessSemanticsfLinuxProcessSem3Runoo75mkCfg99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_FreeMid3HCWdFreeRefillMid~~~~~~orc4fr_W79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~ph6cdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_WriteSet~~~~~~pm64avmx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AW_Put1~~~~~~pqf9put_framek24a_Zr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~qg07AMODELXqg08awin_visqg09depot_covqg0aflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7SecLazy~~~~~~qn1anonvm_same69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~qrc8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~rg74lzok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~rk86u64arrnie2CBmk05munchmk03stkmk05wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~rqb7mem_invnnf6of_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~rva6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~sjddhunspell_scfgorch0free_refill_gmidk25a_thrijcbch_user_begijc7ch_usedijc6qcacheijc5as_tqijc6qbatchijc7qc_listijc4mkQBu44lastijc7qb_addrijc8qb_count79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAW_MallocBase~~~~~~tgaaicpt_chaink25a_topk25a_bot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsUnwind~~~~~~tmb6utracekod5depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsDepotHash~~~~~~trcadepot_hashkod5d_put79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAG_FreeModel~~~~~~uh46tq_appijccch_chunk_begivb7free_s'k24a_ALijc8as_cache79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AS_Free1~~~~~~uoebfree_head_Whc4pairk25OT_TQnnf3mulijc6pclassijc6get_pcijcbkBatchClassijc8pc_countijc9pc_chunksu42hdijcfcompact_to_addruh46tq_newijc4mkPCijc7upd_nthijc4zidxu42tlnnf3sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAW_Enqueue2~~~~~~vn69enq_new_Wk24a_riijc6regionijcaget_regionijccrg_num_freedijch4rg_mapped_free_arrayijch1rg_allocated_userijcerg_mapped_userijcdrg_free_array79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAS_Refill1~~~~~~hgk54rf_nhgk56rf_mu'hgk57rf_mfa'hgk56rf_fl179OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RefillModel~~~~~~hgr08refilledom96firstnnnf6to_nathc4boolk22RBmv7dmaps_subtractnnf3ltbk22FAo62shnnf3divk25a_ctxk25a_fsbk25mkAsthgk54rf_Wijc5chunkijcachunk_listijcaCAllocatedijc8ch_stateijc6cstateo64aappijc8round_upo65aceilnnf2lennf6modulonnf3powk23ATPkod4d_nbkod4d_sbkod8d_frameskod5d_idsnnf2lthc4truetmb9goodframetmbbframe_chaino64SHADo63nshijch2kQuarantineMaxSizesa3notijcbkBatchCountuh48need_new79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAG_MallocCold~~~~~~hin19COLD_COST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~his26B_PRIMhis26pusageijch0kFreeArrayOffsetijcckUserMapSize" s.   (* [comment removed for export] *)
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
Definition ARHEAPQ : ltac2:(zQ "50!h9!j4!jb!o0!s4>1s$3>2XC@1$1$0>2XB@1$1$0>2LB@1$1@2$2$0$0>1m$4P") := ltac2:(zQ "b0!h9!jb!j4!te!v7!vc!hjf!hk8!o0!s4!hke\1s$8\2XC@1$2$0\2XB@1$2$0\2LB@1$2@2$1$0$0\1m$9@2$3@5$6?5HCEIL^5^4^3^1@2$3@2$a@2$1$0$0^2>1b@2$1$0$0@2$5@3$4@2$1$0$0^1^3@3$4@2$1$0$0^1@1$7^6").
Lemma ARHEAP_of_Q : ltac2:(zQ "a0!h9!hl6!j4!jb!hq0!hqb!hr6!hrf!o0!s4>1s$8>2LB@1$2@2$3$0$0>1m$9>0@5$4^3@1$1$0@1$1$0^2^1>0@1$5@1$7^4@4$6?5HCEIL^5^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_FreeMid ()) ["HCW"] "##-Bh01bh11Bh22LBh33LBsh42NDh51Rh61mh75nd_i1h81sp;2p;1p;5p;3p;4p;6p-1R0p10000p4p710p9P!s6%S!s611?R1!s8,P!s2$2!s3/31!sS-]!sQ'p1002U!s4%!t7%3D!sB&8!sR%4H!s615L!s6'p1006Q!s4$1p1007!tq$3101!sB%7T!tS'1008@!s]'g008^j2@Tg009>j1?!s/$^j16Tg00:>j55Tg00;Gj1>Tg00<Kj1:Tg00=Qj57Tg00>Uj22Tg00?1j30!s/$Hj11Tg00@Kj23!s/$dj48Tg00Ajj39Tg00Bnj2=Tg00CIj5;Tg00DUj44Tg00E0j6<Tg00F5g00G:R0/@0R1#?g00GXf2R2%60R0P0f1R3f0R4D5f3R5#>#:p,5HCEILR6f4R7P0P0P2D7R01215A0147f5R8#19014'3^01P6P7P5P2C81217f6R79014f7R9!sK-A969!sF$R7A0149f!sh/R1'=P6P9P8P2P5D;P7P1P3P4C4C4W3W4X50P3E<W1W7W6W2W8o"). Qed.

Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

Section FreeAppMid.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st : ltac2:(zQ "10!ip5$0") := ltac2:(zQ "10!hrf@1$0?1s").
  Let TH : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!spa@1$0?1s").
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sq2@1$0?2ch").
  Let size : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sr1@1$0?2ch").
  Let tq : ltac2:(zQ "10!src$0") := ltac2:(zQ "10!ss6@1$0?2st").
  Let l : ltac2:(zQ "20!j4!ssf@1$0$1") := ltac2:(zQ "10!st9@1$0?2tq").
  Let k := zlen l.
  Let lb : ltac2:(zQ "10!ssf$0") := ltac2:(zQ "50!hl6!h9!su4!ssf!suc@3$4$3?1l@4$2ZZZ@1$0$1").
  Let LA : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sv3@1$0?2lb").
  Let lcount : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sve@1$0?2lb").
  Let CHI : ltac2:(zQ "30!h9!j4!jb@1$1@2$2$0$0") := ltac2:(zQ "40!ige!npe!tkd!tlb@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "50!ige!tm3!tlb!tq9!npe@6$3+pgsq0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!nv4!h9!rv0@1$2@2$0$1?1T").
  Let d' : ltac2:(zQ "10!tr3$0") := ltac2:(zQ "20!tvd!ugb@3$1?1d@1$0?1T?2nT").
  (* [comment removed for export] *)
  Let tq' : ltac2:(zQ "10!src$0") := ltac2:(zQ "20!ul6!um0@3$0?2tq@1$1?2ch?4size").
  Let lb' := mkQB LA (qb_size lb + size) (lcount + 1) (qb_chunks lb ++ [ch_chunk_beg ch]).
  Let s' : ltac2:(zQ "10!o0$0") := ltac2:(zQ "50!un0!unb!oje!ok4!uo2@7$0?1s?2ch?3tq'@1$4?2st@1$2?1s@1$3?1s@1$1?1s").
  (* [comment removed for export] *)
  Let Wh : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "30!ige!usc!npe@6$1?2lo@2$2@1$0#k0?2sp?2TH?1U?4size?1d").
  Let Wa : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "a0!h9!np7!jb!nn2!utb!uu2!uua!hl6!ige!npe@3$3@2$2$0$0@4$4$0$0?2lo@2$1@2$9@1$8#k0?2sp-oq0@3$3@2$2$0$0@4$4$0$0@2$1@2$1?2TH$5+h8@2$1@2$1?2TH$5+i0@3$3@2$2$0$0@4$4$0$0@2$1?2LA+8@2$1?2LA+h8@3$3@2$2$0$0@4$4$0$0@2$1@2$1?2LA+h8@2$6+8?6lcount@2$1@2$1?2LA+i0@2$6+8?6lcount@1$7@2$2$0$0").
  Let W : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "20!mv1!mua@3$0$1?2Wh?2Wa").

  Hypothesis HR : ltac2:(zQ "10!hr6@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis CHIN : ltac2:(zQ "30!hhmb!hhn4!v7@3$2$0?2ch@1$1?2st").
  Hypothesis ALLOC : ltac2:(zQ "40!ip0!hho2!hhp0!hhpc@3$0$3@1$2?2ch$1").
  Hypothesis UHI : ltac2:(zQ "60!hhq6!sr1!sq2!hhqd!np7!vmf@3$0?5HCEIL@2$5@1$2?2ch+h0@2$4+h0@2$3@1$1?2ch+8").   (* [comment removed for export] *)
  Hypothesis DEP : ltac2:(zQ "20!ita!ksd@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!pl6@3$0?5HCEIL?1s?1d").
  Hypothesis MI : ltac2:(zQ "20!ita!ru5@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!ige!ita!rpb!npe@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!hhr9!hhs1@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!ige!np7!hhs1!npe@2$2@2$1?2lo+ro0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!ip0!ige!h9!hhs7!npe@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!ige!np7!hhs1!hht1!npe@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis TP : ltac2:(zQ "50!ip0!ige!hht8!oj8!ij1@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis DLO : ltac2:(zQ "60!np7!hhs1!uua!te!hhte!hhu6@2$3@2$1@2$0@1$4?1d@2$2+h0+hggg0?2lo@2$1@2$0@1$5?1d@2$2+8+ogg0?2lo").
  Hypothesis DCAP : ltac2:(zQ "60!np7!te!hhue!hhva!hhs1!hig3@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis FCH : ltac2:(zQ "d0!ige!npe!tlb!hhh5!hig9!ip0!hih0!te!ita!tm3!hihd!np7!hhs1>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!ip0!ige!oj8!ij1@3$0@1$3@1$1#k0?2a0@1$2?1U").
  (* [comment removed for export] *)
  Hypothesis BLK : ltac2:(zQ "70!nma!nn2!hl6!ita!roc!nu8!hhgb@4$5$3?1m?1U@3$1$0@2$4@1$6?4size?2bs@1$2$0").
  Hypothesis SHB : ltac2:(zQ "90!nv4!te!ip0!ige!h9!hiic!hij3!rv0!ij1@2$1@3$5?1m?1U?3sbs@3$2$4@1$7@2$0@1$8@1$3#8?3sbs@1$6?4size").
  (* [comment removed for export] *)
  Hypothesis QSZ : ltac2:(zQ "50!te!hij9!hhs1!hig3!hht1@2$0@2$2?4size$1@2$3?4size@2$4+2+i0").
  Hypothesis NN : ltac2:(zQ "80!ssf!j4!hl6!te!ip0!hil0!hil6!hig3@2$3@1$5@3$4@1$1$0?1l@1$2$0@2$7?6lcount$6").
  (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. ndestruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let EXT : ch_lo ch <= U - 16 /\ U + round_up size 8 <= ch_end ch /\ U + 8 <= ch_end ch /\ 7430144 <= ch_lo ch /\ ch_end ch <= aceil
            /\ ch_lo ch mod 8 = 0 /\ ch_end ch mod 8 = 0 /\ ch_alloc_beg ch + ch_rz ch = U /\ 16 <= ch_rz ch /\ ch_lo ch <= ch_alloc_beg ch.
  Proof.
    npose (record_ext s OK ch CHIN) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    npose (chunk_geom s OK ch CHIN) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    pose proof (record_band s OK ch CHIN) as RB'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AIMG_TOP, AHI_LO in RB'. unfold AHI_LO in UHI.
    clear - X1 X2 X3 X4 X5 X6 X7 X8 X9 G1 G2 G3 G4 G5 G6 RB' UHI. subst U size. pose proof (aapp_env _ _ UHI ltac:(clear - G3 G5; lia)) as [UE _]. unfold AHI_LO, AIMG_TOP in *. repeat split; try assumption; lia.
  Qed.
  Let LAST := free_last_cells s m ch d R CHIN DPL (proj1 NN).

  (* [comment removed for export] *)
  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 7430144 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 7430144 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 7430144 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7430144 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
            /\ 7430160 <= U /\ U + round_up size 8 <= aceil /\ 1 <= size /\ size <= round_up size 8 /\ round_up size 8 = 8 * nsh size
            /\ 0x10007fff8000 <= LA /\ LA + 8192 <= aceil /\ 1 <= lcount <= 1020
            /\ 2148314624 <= sh U /\ sh U + nsh size <= 0x10007fff8000 /\ U mod 16 = 0 /\ lo + 2944 <= bv_unsigned sp.   (* [comment removed for export] *)
  Proof.
    npose PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & _).
    npose LAST as (_ & _ & _ & _ & _ & CNB & _ & L1 & L2 & _).
    npose PL as (_ & _ & _ & P1 & P2 & P3 & _). npose DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4).
    pose proof (proj2 NN) as NN2.
    apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia]. apply aapp_env in N1; [| clear; lia]. apply aapp_env in N3; [| clear; lia].
    clear - Z1 Z2 Z3 Z4 Z5 Z6 Y1 Y2 Y4 Y5 X1 X2 CNB L1 L2 P2 P3 N1 N2 N3 N4 LO NN2 HI.
    subst U size LA lcount lb l tq TH CTX sb st. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve, kBatchSize, kBatchCount in *.
    ndestruct Z2 as (ZA & _ & ZB). unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in ZA, ZB.   (* [comment removed for export] *)
    assert (SH : 2148314624 <= sh (ch_user_beg ch) /\ sh (ch_user_beg ch) + nsh (ch_used ch) <= 0x10007fff8000).
    { acb. clear - ZA Z3 Z6 Z1 ACEILB. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    clear ZA. repeat match goal with |- _ /\ _ => split end; try lia.
  Qed.

  (* [comment removed for export] *)
  Definition free_app_gmid : ltac2:(zQ "10!hvd>0$0P") := ltac2:(zQ "he1!ige!ij1!ij7!j4!te!h9!ind!hl6!io7!ip0!ip5!hvd!ita!iu3!iv4!jb!jj9!hq0!jo9!jtc!kid!ko1!hrf!ksd!kt6!ku6!kv7!lk3!lo8!lp3&>0@1$1@1$0#k0@1$8@1$1@1$0#8\3ms'$b@2$2$5\2b1$5@2$2$5\4actx$5@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2@1$3@1$1@1$0#8\2jk@1$3@1$1@1$0#8@2$2@1$3@1$1@1$0#k0\4rest@1$3@1$1@1$0#k0@2$2~0\2m'~0@2$4@3$9$b^h4@7$hb@ha$h5?2sp?2gp?2tp?2s7?2s8?2s9?3s10?3s11?1U?4size?2TH$h9^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4?1F@2$hd@1$0#k0+mtlv4?2fc@1$e@1$1@1$0#k0^1@1$hc$c@2$4@h6$h4?2sp?2ra?2s0?2s1?2s2?2s3?2s4?2s5?2s6?1m^1?1W?2lo?1U?4size^h3^h2?2TH?1T?1d^3^2@2$4@5$h1?2s'@1$7$5@1$7$5@2$h0?1U?2LB^1@2$4@3$h7$c?2d'^1@2$2$a\3stX$a@2$2@1$3$6\3ev0@1$3$6@2$2@1$3$6\3ev2@1$3$6@2$4@3$9@1$8@2$f$a@1$3$6@2$h8?2st?1U@5$h2?1U?4size^3^2^1@2$4@2$h3^3@1$h6?2s'@3$9@1$3$d@1$ha^2@1$7$d").

  Theorem free_arep_app_mid : ltac2:(zQ "a0!ige!ita!iv4!lud!mj9!mnc!lk3!lo8!lp3!ij1@3$4$1$3@7$6@hf$5?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$8@1$0#k0+pgrm8?2fc@1$2@1$9@1$0#k0?1m@1$7$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_FreeMid ()) ["HCW"; "FreeAppMid"] "#';Ip'0p'1p'2h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61xi001xh71Hh84__x3h94__p1h:2H0h;2_Hh<4__p2h=6__sat8h>5__p10h?!s-$1h@!s-$2hA!s-$3hB!s-$4hC!s-$5hD4__p3hE4__p4hF4__p5hG4__p6hH4__p7hI4__p8hJ4__p9hK!t8%9hL!s/%7hM8heq_sizehN2HahO5heq_UhP2HxhQ2H1hR2H2hS2H3hT2H4hU!s`%0hV3_H0hW!tY$6hX4__x4hY1EhZ!sH%1h[1zh\2AXh]1ah^7heq_CTXh_6heq_LAh`!s/$THha:heq_lcounthb!s<$sbhc2zhhd3_H1he!sy%3hf4actxhg1bi011bhh2jkhi2m'hj4resthk1yhl1Ahm2H5hn3_H2ho3_H3hp3_H4hq3_H5hr!u'$7hs7!tx%7ht!t/%4hu4__x5hv3a1'hw3a2'hx3a3'hy3a4'hz3a5'h{3a6'h|3a7'h}2b1h~3ev0i021fi031li045lemmai052q0i063stXi073t0'i083t1'i093t2'i0:3t3'i0;3t4'i0<3t5'i0=3t6'i0>1ei0?1ni0@2sci0A2ubi0B2BLi0C2H6i0D2H7i0E2H8i0F3Hubi0G3NEUi0H2SJi0I2SKi0J3STIi0K2UBi0L3_H6i0M3_H7i0N3_H8i0O!v1$8i0P!s/$9i0Q5__p20i0R!s/$1i0S!s/$2i0T!s/$3i0U!s/$4i0V!vh&0i0W!vi%2i0X!s0%5i0Y4__x6i0Z1ci0[2chi0\3ms'i0]1qi0^2q1i0_2q2i0`2q3i0a1ri0b2r0i0c2tpi0d2z0i0e6ACEILBi0f3ACRi0g1Bi0h3BL0i0i3CHRi0j3CNBi0k3CNTi0l4DEP'i0m2E3i0n2E5i0o4ESO'i0p3F4'i0q2FCi0r4FLG'i0s2G1i0t3G10i0u3G11i0v3G12i0w3G13i0x2G2i0y2G3i0z2G4i0{2G5i0|2G6i0}2G7i0~2G8i102G9i112GTi123HD0i133HDRi144HDR'i152Hbi163Hb1i173IA'i183IENi192IMi1:4INSTi1;4INlbi1<2JRi1=2K0i1>2K1i1?2K2i1@2K3i1A2K4i1B3LA1i1C4LA16i1D3LA2i1E4LAD1i1F4LAD2i1G3LATi1H3LAUi1I3LB4i1J3LBci1K3LBsi1L4LCHKi1M5LCHK4i1N2LEi1O2LJi1P3LJ4i1Q3LR'i1R3LSZi1S3MI'i1T2MUi1U2NDi1V3NNfi1W4PFR'i1X3PLUi1Y2POi1Z2Q1i1[2Q2i1\2Q3i1]2QCi1^3QCxi1_3QMxi1`2QRi1a3QSTi1b2RRi1c3SBSi1d3SBXi1e2SCi1f4SHF'i1g3SHui1h3SJ1i1i3SK1i1j3SK8i1k3ST'i1l4TFB'i1m2TQi1n3TQ4i1o4TRB'i1p3TSTi1q4T!sR$r3UNWi1s4UNW'i1t3UW'i1u2V1i1v2V2i1w2WMi1x2X1i1y2X2i1z2X3i1{2X4i1|2X5i1}2Y1i1~2Y2i202Y3i212Y4i222Y5i232Y6i242Z1i252Z2i262Z3i272Z4i282Z5i292Z6i2:2ZTi2;2ZUi2<4_H10i2=4_H11i2>4_H12i2?4_H13i2@4_H14i2A4_H15i2B4_H16i2C4_H17i2D4_H18i2E3_H9i2F!}e%6i2G2a1i2H2a2i2I2a3i2J2a4i2K2a5i2L2a6i2M2a7i2N4cstri2O5cstr0i2P3dN1i2Q3dN3i2R3ev2i2S4junki2T1mi2U5nd_i3i2V1oi2W3pT1i2X3pT2i2Y3pT3i2Z3pX2i2[3pX3i2\3sc'i2]2t0i2^2t1i2_2t2i2`2t3i2a2t4i2b2t5i2c2t6p%0p%1p%2p%3p%4p%5p&0p&1p&2p&3p;1p;2p;3p;4p;8p;Op;7p;6p;5p;<p;9p;:p;Np;@p;Fp;;p;Jp;Wp;Tp;Gp;Ep;Mp;Bg01Z2k13~Tg00OdS00j20Tg00g]j13Tg00c9j1?Tg015BR0j22Tg00hBj18Tg02VAk13`Tg02WEk13HTg01bnj2wTg02XKk13<Tg01``k21rTg01akk11pTg02YQk11;Tg01\Fj2cTg00mMk10ZTg02ZSk20B!s:$kk11LTg01^Hj1aTg028`k10^Tg00eZS01k10>Tg00fYk12:Tg01_Vk10J!tw$gk125Tg009^k10RTg00jok20tTg00P@j2>Tg02Kbk13!t=$;Gk11xTg00Wfk13:Tg00Xnk11vTg02Sok21@Tg02eRk31tTg02[=k435Tg02\Hk334!s0$aR1k11oTg02U6k11nTg00ikj1sTg02MAk12zTg0122k12xTg02NEk1!vU%OJk12uTg03I7k81bTg00BnS02j21Tg03JBmO2qTg03KCk21BTg022Fk11^!s:$ik12iTg03M1k705Tg03N2k3!w$$2]kk11YTg02_5k11XTg02`@k11WTg02aLk11VTg00[Ck12^Tg02dTk30fTg00?1j3ATg00kLj2K!u{$1k31[!s0$ij1dTg01mEj3qTg02POk12O!xM$fj36k11~Tg02QYk12NTg02Rck11eTg03O2k82LTg02gGj4_Tg01h6k12!yd$i?k112Tg01jLk11ATg03P:k32DTg03Q>k20H!s0$^S03j1yTg03R>k41ITg00Ajk3!xQ$0I6k22<Tg00J<k22;Tg00KDk229Tg00LMk228Tg00MWk227Tg00N^k23}!y>$\k33yTg00Qfk33uTg00S0k33oTg00TAk33lTg00UPk12!|C$V]k23iTg00Z8k226!z@$>k10LTg00lnj14Tg00nnk20MTg01kZS04j!tG$3S?k13cTg01]@k13bTg01[7k13aTg03TJk31FTg03UNk4!y%%VOR2k10c!s2$ok416Tg01Xlk13_Tg02mOk209Tg01cKk13!y?$X7k60!t&$Wbk13G!s:$Sk53!t&$Y`k13ETg03Zhk2!~q$3[?k21!s:$[\k11|Tg03\:k4!y+$24Pk20<!s:$]m<1CTg03]Bk2!wY$27ok213Tg029>k23;!s0$_k30sTg01nIk21!{c$0Zk138Tg0218k137!{C$hk2!|G%1ck21!yu$3nk23!sv$4jk232Tg025Vk331Tg0265k42~!tP$dk41kTg008@j6um93=k82@Tg03^Ok22}Tg02LgS05j2J!tO$<k12!uQ$_4k71jTg03`;k51!|b$aHk22{!s0$kk32!z+$bHk40kTg02iPk12vTg02jRk12!~}$k]k12sTg00DUj4`Tg033Ak20h!s0$ik30!t#$0Fk21!x:$4Mk30!tE$bbk72pTg03clk82oTg03e3m92nk83!tq$f8k82mTg02?Dm<2lTg03g=k62!uh%^k21]!y~$Nj3QTg03hHk52!tI$iWk62gTg03j]m:2fm;2VTg03klmN2emO2WTg00afk12dTg03m9j2bTg03nEk2!s0$2fBk31ZTg02hKk12`Tg02lnk20S!z2$lk20UTg02nSk20\Tg02o:k20T!s0$`k20VTg02;Vk20!~f$50m@19Tg03oPk21TTg040[k82!u:$E0k61Sk53NTg041ck42\Tg0434k32[!s0$Sk42YTg044:k11R!s0$_p<1V2XTg045nk11PTg046PmF0CTg047_S06k10gTg048nk32UTg04:1k31OTg04;4k21_Tg04<7k42TTg011Vk40xTg04=?k22S!s0$Vk12aTg04>ck22RTg00kik40|Tg01THk11!u/$?lk32QTg04A3k318Tg00cWk11\!t$$7k32!tq$B:k21`!s0$Tk22jTg00:>k51MTg04C]k21!t<$Dlk51<Tg04F<k20zTg04GQk10}Tg04H_mJ1cTg00=Qk52rTg00>Uk21dTg00?Hk11gTg00@KS07k20!tI$IjmW2M!xm$Kk31fTg00H[k31hTg04K9k32KTg04LHk21!s0$M4k3!|M$4N@k32ITg04O6k430!s0$ik61mTg04P[k30qTg04Q6k12GTg04RAk436Tg04SIk51!u,$Shk32FTg04TZk72ETg04UUk439Tg04V3m;3>Tg04W>k12!x6$XEm92BTg04YLk22A!s0$kk43!sD$[0k53DTg04\4k32?Tg04]Bk13!tx$^Nk73!u4$_Yk12=Tg04`jk13!uR$b>k23LTg005Lk83!wE$cPk43!y5$dZk1!|i$4e8k23!z2$eVk33S!~4$gk23TTg031Pk33!yq$f9m93VTg003Dk63WTg04gMmJ3!zb$hSmT3!{&$iYmG3ZTg04j_mE3{Tg04kdk63!xQ$limM3!zA$momF3wTg0366m<3vTg04o5k83tTg050?m:3qTg00dVk13pTg02cSk43nTg02bQk43mTg051Cm<24!s0$hmB1HTg02@Ik31GTg01o2k23k!s0$^k23jTg02A2k40uTg02B4k617Tg02:kk401!sD$Pk70!s:$BXj7jTg032]k73hTg023Kk31JTg02C<k80Q!sa$Hk33gTg052Nk43r!sX$9k63sTg02<Bk33f!sD$nk322Tg053Km93eTg054ES08k13dTf0R3#3#3p=k%33#8p=R%3!s8$!s$,p>0:!s;'?p=Z%8!sO$n!s-$#8#8p=[!s[3?p=|!s:+p>0vf2R4f1R5'2/03p=;%8!tD$Tg00G:R6?653p=9%33#?p>1>1045/13p=C!sO$#!t@$x!t@%!sx%Kg00\KR79663p=Bf4R8f3R91153,14'1'1p=:!s4&p=L&1\3$3pp=z&0>3#sp=}g015_R:AQ:537Q4p=pg016cR;P9P4!s<$H0|p=O1073p==1>45,19/13p>0=107!to$>0IP;P4P5P3H3np=E!s_$p>1D!s=+0|p=P&0>4#s&0>5#s=Q:35Q:p>0ag03>OR<P6P1P3H0xp>1u!sK,p>10%s5!s1%0~%s4!s4&!sd%m!wy$#8!v-$]1>!ub&!t_-mp>0[10!s?%>1Q!s1$J4p>0E10941053'Jp=F1c53=667p=h10891045'J!wF$vP8P9P4P5C_!s6$Ug00^7R1?A53p=D!w#$!sw$0%43#4p>3]!s/$#4!s3$\!s3+!s$;p>3[!sKD!s$Cp=S20<63p=NP6g055MR=P6P6P2P8Q03P9g055l!v4%N<24p>1{P=!s$$6P6!sY$6YR2Q03!s%%P0g0579R>!ur%g01D?R?P7P3NB1Hp>3@!s`'!sV%f5R@!vG'!t0+z!sH%!s$&0P3P5P4P0P9P8P@f6RAf7RBf8RCf9RD!s~&?1>73p=iA66!w{'41037p=r21w63p>0DB1G653p>02g02Io-3k3p>0;g02ICRE?Q!sB$423j!sU$WP6!zF'up>06P5g006QRFg02C`RGPGg02D@RHP3J17p=H21q63p=lP!sQ$2K;RIP3H01p=mP9PFPGPGPH!sy$!s2'3g02EGRJK07Fjp>0?P8!sB+!sX,6P4g02D`RKP5H01PJK07P3Fjp={P4!sL+5P3K3hp=X21s63p=@!sB-6P5PK!tZ$!sc$p=<!t70!sk0FjFjp=5B1J653p=G!sm2I!sm/~PA!sC+!x5%!u\/3L0QL0Qp=Wg018lS09g02J[S0:7!w#$p12539664p>1l!tr-p>0o!v#84!uq%!t$%p=t!y5$!yS$H0u!wp,nB3g!xV%_!u]2!w@-!sq$L0Qp>0l!uw3p=eP@!s9+!si0Fj!tM'>0811!#6j$>0r!yq%:1G64p>0N!x+/B1J64!wF2\!y:%3GW!y:'>0F!sQ2p>1=!wC>>0`!uv$5P3H3rp=f1245/23p>0d!#8I&3p>0w!{x$#dp=Y1w!sH$9669p=o!vZ&!{K,!v\%{!vD/J3sp>0yB3f!vo%APAP!}f-C`C`p=]!vK0!ye4!vK$2_1045/J3p>0Y1045,J!#8_$1U!yL6p=^!s<0!sv,!{b+>1:!#46-P!#41-P>!ts/!#3#$2Z!#3M%9P8P@PAPBPCPDf:R>g03=?S0;f;R0f<R2f=RJf>RIf?RKf@RLfARMfBRNfCS0<fDS0=fES0>fFS0?fGS0@fHS0ANJ1cp>0@A69!y'%=VB226!{O$Op-0ROQ07g057\!tj093ep>1?1713p=MQ09&3d3Q0:36p=gA61!w<$G!sp$5=!st%X%d3,15p>03!vC9J1!vA&3P!}V0!wj+J17!s`@!v}$5p,3BNDp,5HCEILRF$3~RPp,2loRQ'0S0Bg019LRR#3RS#3S0C#3RT#3S0D#3S0E#3S0F#3RU#3RV#3#kRW#3RX#?RYp,2THRZ'0S0G12ZYS0H/0PS0I%8RS0J#8R[#kS0K#3S0L#8#RS0M#8$0:R\#k#ZR]p,3CTXS0N'0S0OQ0N%8SS0P#3S0Q#3S0R#ZR^'2S0S!s~$T%3XRX#nS0U#[#[S0V#n#[$0:#|S0Wp,2sbS0X'0S0YQ0X%kXR_#3R`$0vS0Z!u1$a#3!s4$[#k#|S0\'2?;YPS0]p,1sRb$3`S0^,0]S0_Q0^%?a;;PS0`p,1dRa$3HRc!sC$aQ0D#?Rd%?`S0b'wS0c,2cS0d!tu$e&3<aR`!sP$f%?TRe%?_S0g'wS0h,2`S0i!sN$j%T\#ZS0kp,1UR\'0S0lp,4sizeR_01reS0m,2\S0n!sU$o%?RRf/0_S0pQ0m,0_S0qQ0m&1p_S0r,we'9S0sQ!v$$LARg'0S0t%?XS0u,2gS0v!sm$wp,6!#yd$S0xQ0x%8[S0y#[S0z#3S0{$1>S0|'05CfS0}%8W#x#R#R$0K#|S0~&1;\S10'0S11Q10Q0rQ0W3;S121c\dS13#BS14Q0P#8S15#8RW#|S16Q0F$0ZR[p,2spRX+0BS175;QS18D:D:S193LS1:3LD:D:D:P6P6&1L[RhP!s$$p,1mRip,2chRj#aRkQ0D$0^S1;'2%?SRl#z%z@&0>7Rm$2:S1<&0JjRn$0>$25Ro%}8&0R:R:3p3pCOS1=%=@P@%?VRV%?URU,c@%8TS1>#?Rp'9H0=RqQ0F#?S1?-0tlRr,>8-0I8Rs&3BbRtQ0Q#8S1@#8Ru#8#T#ZS1A'2Q0J#3S1B#3S1C#3Rv$0K#ZS1D,2tRw5EiS1E%z7S1F01D:S1G9PiwS1HPig058MRwg059R'2g03:US1I#}g03;jS1JQ0;<0a:COS1K!sT$:YS1L,2t&1xbRx$3:Ry$1vS1M-1@<S1N#}Q1M$1u:1t67RzQ1MP7P7P7&0R6S1OH35634<R{$1oR|&1nyRy010:40aCOS1PPi%3u#T#Z,2tRu%s920~3::0m45COR}!tQ$;^,2w&2zbRw#}P!tj$Qg05<i$0>S1Rg01Q7S1S&2xbR~PtPw&2wbS1T&2ubS1UPiL1bS1V'1D:D:Z0`hZ0_hZ0^hZ05hXf6X}6Q06p,2raS1WPXp,2gpS1Xp,2tpS1Yp,2t0S1Zp,2t1S1[p,2t2S1\p,2s0S1]p,2s1S1^p,2a0S1_p,2a1S1`p,2a2S1ap,2a3S1bp,2a4S1cp,2a5S1dp,2a6S1ep,2a7S1fp,2s2S1gp,2s3S1hp,2s4S1ip,2s5S1jp,2s6S1kp,2s7S1lp,2s8S1mp,2s9S1np,3s10S1o!s/$1S1pp,2t3S1qp,2t4S1rp,2t5S1sp,2t6S1tNO2qp,1FS1uQ0C#8S1v#3S1w#kS1x#RS1y$0]#n#R#Z-1B[p,2fcS1z&1^hS1{Pi&2i;S1|K05S1}62c;S1~Q1=PqPsQ1EQ1HQ1KQ1PP}Q1QQ1VQ!sD$%=AR}PAPV1cAU/9pH0=AI}Ar!sX0iPu%s>20~B::0mDCCO!si%PiP|%smS20&1Y{Rm&1X{S21!zr&22%?vS23,2|Rv&1W{Ru$1V60[iS24Q21,weS25,2vg03?ZS26,2|S275EiS28Q1M&2^x$1vS2960f<S2:9A<{S2;Q2121@6uS2<'9S2=Q21,0fS2>Q21g03@gS2?41QS2@Q1N!s@$Ag038BS2B/0|S2CQ27/0PS2D1c|dS2E#BS2F12tYS2G!sH$HQ27<0EtS2IQ271KkdS2J12keR{P|CFS2KQ0dP|Q27PcCFS2LQ0i!s5%`CFS2Mg03B5Q0E#?S2N-0tlS2O'w,2wRv!t-$PQ27g03CC,2v'0S2QQ26/0mS2R%=3S2S?I3rX66S2T>1[6uS2U%Bz#dS2!w{$22Q24Q28Q2;Q2=Q2@Q2AQ2CQ2DQ2FQ2IQ2KQ2LQ2MQ2PQ2QQ2RQ2UQ2V10fnS2WQ2J21rneS2X,2dS2Y5qFS2ZQ2X9qFkS2[g02EgS2\/2dS2]/0kS2^3LS2_Q2X,2kS2`!v\$a1ckdS2b#BS2cQ2X,0nS2dQ2X&1pnS2e!#:;$2f10YtS2gQ2G!s]$h1ctYS2i#BS2j10]~S2k12~^S2l!sF$mQ2lPtQ2GP~CFS2nQ2B/0wS2og039HS2p,2wRzg02H7Ru;;PS2qQ0b,hwS2r!t2$wS2s12zYS2t!x2%uQ2l!s=$vQ!s9$~S2wQ1TQ1T%8WS2x#?S2y!wl%z'0S2{5CuS2|Q1U!s%$T'>+0IS2}&2OxS2~Q1I566S30&2NxQ1J!s3$1&1exS32Q0;!s6$3Q1NQ1N'9S34Q1N#=S35Q32,0yS36%=yS37!x9$WQ2_Q2aQ2cQ2dQ2fQ2gQ2hQ2jQ2kQ2mQ2nQ2oQ2qQ2rQ2uQ2wQ2|Q2}Q30Q31Q33Q34Q35Q36Q37PFPbPiPjPap,1RS38p,4CHINS39p,3DPLS3:L2LQ2GQ2JP{PtQ2l!s0%~Q0d!s0%cQ0i!s0%`CFDvDvDvPtPuPcQ0cC_S3;!s4$`Q0hC_S3<PwQ2p/2uS3=!sI+>PwQ3=!sJ+?P~P^!sC+@!s4$!sB'AQ0^g03DVS3B!sI+CQ0^Q3B!sK+Dg02FlS3EQ3E&2HxS3F7A3S3G&125S3H&1A5S3I!sf$Q3HQ3I!sa&DU[_0@S3JQ0c9qFcS3KQ0eQ0h9qF`S3LQ0jQ1~Q3;Q3<Q3>Q3?Q3@Q3AQ3CQ3DQ3JQ!sW%!sP$p,3SHBp,3sbsS3M:2Di\S3N&0ZT$1LS3OQ3M+0H#yQ0r'9S3P'1Q02Q3NQ3PQ1~P3Q3NQ02%=\S3Q1h\eS3RP;PiQ10Q3MH1IS3S'1S3T!sV%[RTP3Q3QQ3T!sm$RQ3SP!s9$RQ3SQ3PQ38B2>FbiS3U22<FbS3V22;biS3W229biS3X228biS3Y227biS3Z23}biS3[Q2Sg00\i7I3B3ybi5B3u!s+$o!s+$lbi5'13L[`0Z6S3\&23xRx,D3S3]23ii5[`0[1S3^Q1M-26iQ29-26i'1S3_Q3O$0LRTPiP\%4?S3`#4S3a#4R{#4S3b#4S3c#4S3d#4S3e#4S3f00M3P:COS3gZ0ATS3h'7S3iQ3VQ3WQ3XQ3YQ3ZQ3[Q3\Q3^Q3_Pig05=l,KkRyg05??RWP6&3cjRzPlQ0J#?S3jn0110000020000#z%z5Q1<%}3=po:3pCO%=5S3k?I5V1c5U/9p3LXf6,76X}6,76S3l&3bjRp/9dPi&3ajRUQ1C$0K!#<u$T#x$0]#T#n#x!s;$!s>6#?#}210y:CO12UdQ2N,Kp61Fi400S3mPWPOPzP;PiPkPnH21P;Pi&1;kS3nQ2eH21'1RyB1FiknPiPkQ2e$0cg05@JS3oH16'1RV!u^1S3p12knRo&3_jRm/Ko61FiS3qPiPU209p!sh&A_RoH16PiQ2`Q2`,Km009e$0cPoH16Q09PO&3^jg03H[RvPi1KUuQ3f$3]$3\$3[S3r#4#S!s$/S3s!s93#S!su$n0!tp%!tq$13LS3tQ3iQ3lQ3mQ3pQ3qQ3tPWPz!v/$3PyP!uL2Z0ZWP4g05C;p,5ALLOCS3uJ0bPy&3GjRy1K\dS3v'0S3wQ0n/0mS3x12\eRW!s2$y10]yS3z10mPS3{1hye1hme12Up/9\10dp10yUD:S3|!th$wQ3xQ3yQ3zQ3{Q3|!wj$\&0c_Ryp,2bsS3}+0M01D:RUp,3BLKS3~I3F&3EU#y,2\9Ei\p,2lbS40$1XRU#NQ0x/9US41eS42Q41Q40$1oRU#N19gUS43eS44Q43%Nn19_nS45eS46Q45%Nk19\kS47eS48Q47%NwQ0X/9wS49eS4:Q49%N~Q0N/9~S4;eS4<Q4;%Nt19ZtS4=eS4>Q4=12\_RU220y?Rp#yRV,2\Rz'9Ro21E7_R}/27Rs,2\Rq,9U!#NO$~6S4?P3X66S4@Q4?1953$1|Xk6X66PUPU%NUPzPqQ4@!s%%!#h%%DF1253H3A#NZ2T6Z0?6P\P\%N\S4APVPs!sT%%y3S4B#NX6=S4CPpPsPyP}Q4@21E7!tD%DP_P_%N_I1{20<67H3@J1zN:3?N<1C21y7_%i_Ry@14}_%r_%B}400P}P6213\dS4EQ3Q%=dS4FQ13#=S4G[[S4H&0^R-3;6S4I&0D{S4J60s6S4K21w6?S4L+02$0;&0RER?+04&0LERE&0W4S4M&0W9S4N8065S4O&386R{&376R}P}1H}@S4PP}Q0J#lRs%lSRS'mH0?P}P}PS21s67Rp1H}AS4QD{5X}&1^GRGP!sc%BS4R!s/$CS4S!s/$DS4T!s/$>S4U!s/$0S4V!s/$2S4W!s/$JS4X!s/$IS4Y!s/$KS4Z!s/$LS4[!s/$MS4\!s/$NS4]P}Q0<,H}S4^P}Q0k#@21q6RRR5<}S4_P}Q0=!sE$`P}%@fS4a=<}SS4bQ0>!s>$cD5!s$1PG1GRSRV1Gsp,GR5~}FW233}HRHP3P4Q09Q0:+0<23234$0pdB31675H2~Rqb3b4b5X06X16X86X9OX<OXDOXEOXFOXGOXHOXIOXJOX>OX?OX@OXAOXBOXCOXWOXrOB14945%r5<008!#a\&P>P0P2PJPIPKPLPMPNQ0k/05Q0<10f4S4dQ0=!#W#$D:1249S4e128781l4[[^06^16^86^9O^<O^DO^EO^FO^GO^HO^IO^JO^>O^?O^@O^AO^BO^CO^WO^rOP3Q19Q0oQ0jQ0fQ0eQ0aQ0`Q0_Q0]Q0YQ0TQ0OQ0IQ0GQ0B%B4PyP4P_P\P9p+01kOFb2bZc0db:H1kb`b^bbbObMb_baPoP6PzAEi\3X[6P5PUP3EuAEi\U22}e_10e_S4f1>_eS4g'JQ05Q4fQ4gQ3iP3Q4f!#5#$PWPUP9Q46Q45Q48Q47P?PEQ4M&2|6Rz!{D%hP{P}P}%@eRo00oSPGP}1GRoS4i9<}RR!}f$i00oVH0?DtPHP!x;010e5125eS4jQ4j1254S4k'05C5!v}&P3!uk%O3b2bObMK1jAEi\WS4lAEiWUS4m!#B'$4lQ4m!u7&lQ4m!u8&5!u63&0W5S4nP{Py!t[0123e,03^06P3P\O1!t=%S4oI1iPiP\1KW\Ry$0cS4p!#?{'4qZ2STS4r,7TS4sQ04PTQ4r!tU&qPTQ3h!tQ1Q3fQ4p56=S4r21E7yS4t,9eP=P6&1~=Q03Q4?%y5Q4B'9A6=5322{5342yXk=X6=Q3fPe%NeQ4pQ4tQ4@Q4DPyPy%NyI1{!#5J&y%iyS4DQ4t<14y%ryQ4t#B400Q4tP6Q4IQ3`$0DS4t!#5+$?Q4L+02S03$0;004?S4u!xY$P4PzP5PzI0nS4v!xZ%1H}8S4wP}Q0C#lS0C/GoQ0C+0_Ry,mR!#4x&yPpQ4PD{5X}!y'$moRI0l!xo3!~%%Q4j/K5Ry:1443%ry<00919e!xs'!|o%P3%B5S4xQ4DP\P5P4O5b2!{h+ObMQ4rP=Q4pPiP\20M39P:COZ0?=P5Q3fP3EuPiP\Q3f00M4P:COP3c0Fb7H0kY0FZ0ATP5P3O2n20!#?z&12!#?P%S4qc0>W;Y1i!sK7!s/%b]Y1NP3O1Q4gPiPU1KmUS4fPIQ!#=i%4Q43!x|04:Q49Q4<Q4;Q4>Q4=Q4EQ4HQ3a$0DS3a!xR$!wa$4m!#9h$!wd%pPEQ!}2'Q!wR$4PP}Q4QP}Q4RP}Q4SP}Q4TP}Q4UP}Q4VP}Q4WP}Q4XP}Q4YP}Q4ZP}Q4[P}Q4_P}Q4\Q4bQ4]5e}!#7_2A<}pVJ08!x'9!#7-I!#qY2!#6{+Q0k/03S4rPK10f5P!#fr%D:Q4k#=!xr0!#6cI!#6]QP_P\p+01nOBb2bU!#6L0Q0z#8#n#[Ry#3#[#[$0:!#my%z/0P%8y!s;04D,0P1cPYS4y#B&2vFRy,0P12PY,>y3LS4z40rS4{Q0U#R#n#[#R!#nr%&1;PRyQ0V!s8+,0y3CS0V&2tF&2sFC`Q4{Q0V'1RyePy!ymT1?-0hlS4{%ilS0UQ1?#=%ir[S4|[S4}%=lRyQ1?>0il5VvWNS1?%=r\v^NyS4~213PY%=P%=YQ4y#=[[P4g03G1S4y2117l+0<Q0UeS50O1Q4|Q4JQ3aQ4L40N!zx&PE&0W8S51@064zS52Q!#A]$!{0%!{4$0z#@Q0CQ0CQ4D#@5<}D{Q4Q5e!{@$G!sJ%C-0os!s3&!{QQ\P}Q4]P}Q4^P}Q4`Q4_Q4c!{[2!t$$V20_sV%@lS53>0j6[S54C\J08Dt!{r786XX!#@$SQ0zQ4D,097C9@0r8@1098!#@%:<Q0=!|:$4Q0>!#p$&1298S0kQ0k,K@;;r[!#@#-X!#@&SP3Q1:!|EJQ0VQ4zPPPmP_P\PJQ0>p+023S4zOGb2b=c2FbLb=bK!|`1c0e!zl1pPEQ4O!xr%20Fso!xH%B1=SoRPG1GSsS0V-0_RS1:9<}pDt!#?14X861>4e124e!}P$5!v1$4#=!v/-!#?4%mP9P2O5!#?8%2pQ4f,2US4f9EiU!#A#4OP{Q0VQ1:'G9~}R!tG6Q4kQ4k,K361l3!t<4!#@J&Q4f,9mP6Q4fAEiU!#B{%m!#B{%UmP;PiPUPWPmP3!~9S!tx+P}B0`}SoS4fPGP}Q4i=<}sS1:PGQ4i9<}VS4iQ1:5e}FW!vb85eS1:Q4j/09Q4eQ0z'0S4jQ0z<1Q8!vk1!xg%2Q0>!vl$t!xV1!#C2$UWS0zAEiWmR!#C1%0zP!#C0%0!#X-$\!ul$0P5!ulYhP{P}Q!uf%!#;Ug!#3&+bQ4^!#L74P}P}PRPVQ4iD{!vd6!~cS1:!#;a:!~[%Q4dPN!#;[+eQ4j5C!#KH+!~AV!#;c$l!#;fMPMp+026OD!#;h4L2oQ4l!#H?%3Q4oI1iQ4sQ4qc0>c1jX;mY1h!#Am>c0Hb7c0HY11P3O1!sK-!#B^$!s'$c2Vc0Ib7c0IW;Y0nWdY0mWVW;p,3EXTN92nc0JW;Y1<Y0JWVW;P5PjQ39O2L2mW;Y0iWqWpWoWnWd!sE$3N<2lc1bQ3i!#I1$3h!#ee%gP;Q1WPXQ1XQ1YQ1]Q1^Q1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1uQ1zPig05DjPQQ17PZP\P_PaJ2k21]66RmQ17Q1>#3#T$0v$0^'2S1~,fQQ1L,2ZS1LQ23'2Q1LQ2N'2'f12geQ23,2gS23'fQ23Q0x,weRU'2S3hQ2N>0dgUS3i'f&0Rm5Q!s%&3Q40fS3VPQP\P_p+01MS3Wp+01LRUPZQ0;Q1y#x#R#k#Z!td$TQ1UQ0y$1>Q1W-0B[Q1]!s,%7Q1Tp,2CHS0yI2hJ2gS1yPa!uT%p,1kS3Xp,1lS3Y!$#C&S3ZPgp,2tqS3[$1nS3\Q40$1YS3^Q0x!s2$WS40N:2fS3_NN2eQ06Q1}PF!w<0ZQ1[Q1\!wE'_Q1`Q1aQ1bQ1cQ1dQ1eQ1f!w]CqQ1rQ1sQ1t!wi'PQPap,2stS1t$2dQ1SQ0NPZ!u{+Q0XP\P_Q3WPUP5Q1IQ1JQ0;Q3MQ3XQ3ZPgQ3\p,2LOS1s!#41,P}Q16#@>1=RSPGP}PRQ15#3$0K#ZRU#@PSC\!#:V4Q16=;35A;5U4!#RS'Q17PQp,2HIS16O3b2Q17/hdp,3SPA'bQ17Q2z7;!s7%T'bQ1B#8S1B#3$0w$0w#RS1r#8#k#R#ZS1qQ1Y-0B[RUQ2\9;UY3CPhQ1RQ1q20B[3!s>-Z0chP6!sv+8#T!su$#n#T#n#ZRUQ1q123YS1f/0]7C3X[6P?PEPz!uy'q#@%@US1eP}Q1e%@YS1d%@]S1cC\D{!uu,Q1qA;UY]7CUP3b221B[U!z1$4{Q4}Q1?Q4~P5Q50O1S1bQ4|!t5/Pp!xl$eQ5460`}!s~/1>Ur-0I!s{$bZbUbZ-2bUEu!xy$R!u}2eQ1Yp,2TPS1qEu'bQ1r#3$0]#ZS1rQ1SQ1S/2eQ2\Q0N=qF^S1eQ0TB1ZFZYS1aQ0I1hZdS1`'1S1_'1S1\'1S1['1S1Z3C3CS1}Q2r!#wO%0^/huS06!#tt$5qFS3l!s2%;;PS3m1htuS3pB1ZFtuS3qA;tuPS3t1h~eS3wAqF~^S3xQ2mPwQ3=!sa%!s1$PtPu!s/%~P^!s>&tPu!s0&~P^&2`bS3yg03EiRU5qFQ3y?;UP!so%3yPU!sR%!s1$!sa$!s/$~P^!sC%3EQ3GQ3H/hu!#vG$!si$HQ3I'21wluQ3I!s5%!sw&HQ3I!sx'!s=$!sy$!s0$!sz$!sF$3yPUC_DU!s$%3C7CP3L[_0@!t=$!s%%F7A5RU&129S3F&124'Y&128&1A8Q3F&1A9C_[\U[_2\_0@!u~$~P^!#{Q$'1DU3L!t-+!s0+DUS3EQ1rQ0M!}V%R#k#T#ZRu'0RUA;ue]R]Q1Z'1S0M'1!x/-6!#nW1!#l|%2mQ3EPUQ0M!zc'Q1r#@%@uRu5<}!z[,P!zU$P]Q1Z!{5-uPoQ1cC\!sN-]P!~T$eQ1[P4Q0TQ1\P5Q1aQ1_P@Q0IQ1`P820Std%BdR]#dS1`PtPd209tdRu1ctdRUCo[20Utd%idS1_1>Ud-0IU[20\td1>d7S1a1>dU%rU'1[20Ttd%Bu\]20Vtd19Ut\]PuP6PUP620StY%BYRU#dPtPY209tYRuQ2i!t2&Y%iYS1\Q2iQ2i/>Y+0I!t6$Y1>Y7Q2i,>YQ2i#r!t7&Y%Bu\U20VtYQ2i/9t\UPuP6Q2iP6P@Q!#P_$Y+0<Q1\eO1Q2S?I3YPJ!s@&d!s@$_eS1\O1%=CS2i?ICdQ4IQ3c$0DS3c60s6!#Q8&?+0240NQ3d!sB$dQ4K!s>$t!s>&4m$0;S4K+0e+0e!#Q_$Q52P5&0W@S52P9PzI0{!#58&d=~}p-0y}PG!s5$Q0P#l+0A/GS,msI0l!#DQ$A<}pRS0PP}%@dRu-0FRH0?!sB&~}u!si$S4t!sl$0C-0Au/GR!sh,A~}SpPGA~}RpS4?FW!#I#7XX6Xu6g03H>S1[\UP9PYP@P4Co[Q3k?I5dQ1[\]S1eP@PdPAP9Co[%B8RUPU[!#P<2u6P3P8P0PtP9P>PDP5PLQ0@O9b2b:bmc0bc05c0Ec0Dc0CbmbTc0ac0]bSbRbQb:b7F]F]F]W;Y2[Y2ZWqY2YY2XY2W!#BX-p,2PLN@19Q1}e'bQ0HQ0XQ0XQ2p<0dYS2pPZQ0S!s8%Q0NQ0SPZ!sL$N!$,P$S1}Q1w#8S1w#?RU-0hlS06Q0U%=U20tlUS3l#i[S3m[S3pB0ilU5VvXNyS3qQ3l#=S3t!#W}$3wQ1bQ3m!#MW,%@^S3x,GsS3E=<}SQ53Q1w$0Z60j6S1w,GSQ1d'GRU=<}s5X}S1c!xx&,GRS1Z=<}SS1rA<}UR5X}S0M!sE$!st$RQ!sF$s5X}RU!xh%MQ1c=e}UJ2_!xP8124^Q3l,25?;Y4S1c80Y5A;5Y4S0MQ3l>0d4Y<0E5128^A;4Y880Y4129YS1ZP8!sH%8YS3EP912@^RUP8Q3EP@PUP9Q1ZP@!vs%!x{/P3P~PwPtf]S1Zf^S3EfbS3FO6b2b=bLb=Q2s!t#%wYS2sPtQ2vQ2sP~Q2nH1UH1Ue!xJ+PcQ0dPZCFS1}Q0HP`Q0i!s5$2vQ2p!sD$Q0XCFS3GQ2p!sE$!s6%2pQ0S!sF&NCFS3IQ0S!sF&!s6$yQ3KQ3L'1S3H'1S3B'1S0^'1S3='1S3z'1S3{'1RU!$1?IP!sOKQ1}Q3{Q06!#8W&w213kdS3{%=kQ4FQ2b#=S1}[[RU20SkdS3|Q1`PkPd209kdS4gQ2bCo[S0z20UkdS4qQ1_Q1}Q2b;IdS1}[S4s20\kdS4oQ1aQ2b,>dQ2b#r'1[S4l20TkdS19Q4g#B\]S4g20VkdS1:Q2b/9k\]S4jg05EkS4i21TkdS4beS4fQ4bP8Q1\O1S4HQ1}P5PvP>P3P5O2X]yS4EQ3t^]yS3tP0!#B]$0k!|0+!#Ss$1rP}PSQ0b#@-0AuPRC\S0b5X}S4DPGQ4DC^!#Ff4f/05S1fQ0c=;53S4D'JQ0M!s5$45S0c'J!#rS+cPtfiS55O3b2bKb=bcb:Q2G!ya%tCFS56ebT!#3}+!#\V$Q56eQ2vQ3z!wa/Q3{PUQ3|Q0zQ4qQ4sQ4oQ4lQ!vZ$Q1:Q4jQ!v5$Q!v-+Q!u{$Q!un<g!un$o!un%g5X}S3zPGQ3z!un8Q0h!uh$3z!uh&h!uh%h!uh/`PtfhS2v!uh3!|<$tCFS2G!uh72GeQ3GQ3=!uhy!#L4$wQ1d'GPSC\S3=Q!xW$!#5G$w,GRQ1d!s@$1w!s@%!uy63l/2Y=;35S3lQ!xf$1cQ!x_3wfgS3G!uu1sQ0d/0wS2G80Yc!uv8tQ!sC&Q2pQ0^!xgz3=Q!xV$PGQ1w!s1%!u^8Q!xR$1cQ!xK3wffS1c!uT4i/0wS3l80Y`!uT:!sC&Q3IQ3B!xS~3x!xN%x!x4%S0bPGQ0b!u\5A;3^5S0b!x7$A;5^4R^!x;4~feS0!ue2l!}t%~CFS4D!ud74DeQ3yQ3H!x3{x!x$%S3xPGQ3x!x060b!x0%0h,J^!x-/~fdS0h!uG3!}S$~CFR~!uF6P~e!#:>$P9P5C`!#AP+QY0NY2PY0MY0L!#]&0Q3:N@19!#AJ$3vPW!#A?$3vPWQ0NQ0d!s;%cQ0i!s0%!$Gq'fOS0S'bQ1T,0YQ2{Q2}40rQ2y-0hlQ0UQ2y#=Q2z#i[R~[Q2y!#rD%XNyQ2z#=\v^NyQ1bP~!y00A<}pSS2yP}20FSRH0?R~!#d0%}Q1dPRQ53Q2x!#AT%9<}RD{R^PGAe}^~!#@]4!#Ei$3Q2z,059CY510Y4!s4$4%=9S2z?I9440r[!#XY,UQ1Tf[S2xf\S1dO4b2btbebt'bp,3DLOp,4DCAPp,3FCHp,3Ha0Q0m9qF\Q2]/0\Q0oQ14'13LQ2ZQ2[Q2^!s+'aQ2c'1R^'1R~'1!sE/P~PFPkQ2X!s'%5!zE$!v8%nP{A<}R!#lw0103!$+k%kO1S14b2bL!sZ-h!sZ$VV!v-31235R~/0~!ue+2XPkO2S2]b2bLL2]Q2^P^!sp1!}h%PuPSC\R^PGP^!}\8d5A;5d!#\C+PkQ2\P4!{&$L!ur%!s~-OP{!x\$Vs!sy;X8610~4Q4k/09!#DY/P!u+$flS2\O!up,Q!$+s$n!}2$4?PGQ4?!s|2%B3S4uQ4x[!vZ$Q2bfkS2bO2b2bLC`F]Y2:Y2;W;Q2vJ1S'bQ2N-0hlS2Z!{9$N#=Q2O#i[S2[[S2^Q2N!{=,S0mQ2O!{@&S2{Q1bQ2[!x2+P}Q4a=<}RS2lPGP}1H}9S0bQ53Q0E!{6&:0`}RR^5e}PGQ2l=e}^!{:39O10f3S0EQ2O9I45Q4dQ2O7I!#kf%9OP3Q1I,0nS3zPnfmS3xp,3QSZS0g!vK$ec0Wbep+01Fp+01E!zD$^Q0mQ2{!#^J-Q!#^C$8Q50O1!u?1P}Q0[#?R^#@S0[9<}RS50Q0b!}_+0Z#?S0Z#@S0b-0FpQ0b!#^x%H1:!sH$50!sk$Q54+0F!$1:&pQ0K#8#x!s$%!#a?$?S0K!t5$!sT%!#_d$D5!#{Y39OAC3^5Q0Z#iQ0ZPr105^P^PrQ0KQ0K/>r+0IH0=H0=!vG,2O,>nPnQ0g!zd$e!#`N$!v?$Q0;,>7Q0;PrQ3zQ1IPrQ1JQ1J/>r5C7!sp%!$}6$bPiQ38H2\Q2:-1@<Q0L#k$0v#|R^'0P=Q2:-0H<Q4B/0^Z0?=P3Q1M-0H<S4BQ29!s0$2:+20S0LQ1MQ2962[<J0bQ0L#yS29/0^S!tK$Q4B#yS1JQ2:#yS0K'2S0[/0^S50!%-K$0Q4@Q0010!$FX,Q29!s<$[O1!$FX&CQ0LQ0[Q4B!uK%#NQ2:!vH%#NJ2ZJ1zP^P^%N^N<1CP3H2YQ50Q2:$1RQ0K#=Q4B$1RQ1J#=!yK5!#|Q%v!{[$0P!#Vo%9<}p!$&/'%@^61=R!sA%P!|&$,GRS0C!y$+Dt!#7u52S%=4S54Q4e/0^Q2z129f;I!$#m+P3Q0KQ1J!#u6$!$6q$Xbtc0Xc2Oc2Nc0hc0BQ35Q1N/2f;Irec0BPhQ1RP3!#ka'0X!#kd$PiL1bZ0chf}Q1YQ1qEup,2MIp,2STp+01Cp,4FLG4p,3IAXp,3DEPp+01GP3p+01Dp+01BPAp+01AQ!#nL&fvS1qQ2BQ26,2gRr1hgdQ0HPgPrPZCF'17CP7CgQ0W/0|S2BQ0u,2|R^/0PS0HQ2FQ2H@0E^tS2H'1S26'1213|dS1U%=|Q4FQ2E#=S1T[[R^!}m-Q0W#@S0X=<}RS0NPGQ0N!#5w1!tB$3!s+$5!#5z$P|fwS0NO2b2bsQ0HQ26Q1UP^!#CV20u#@S26!#Hi$SPGQ1S!#@~6u=;35!uG$5S1S/0!#8},PP|Q1q!}?$s!u[%!t75Q2yPG!#>d$uPGQ0PFW!yY$4?!yp'X!$C]$Q4!yW93kQ4FQ54[[Q4x!u^$9%B9!yU-P|Q2EP5fuQ0NO5!tZ$1UP^20S|dQ1`P|Pd209|dR^Q2E!#bk$|dQ1_Q1TQ2E;IdS1T[20\|dQ1aQ2E,>dQ2E!#bg&|d%B^\]20V|dQ2E/9|\]Q4i21T|dR^eP^Q4HQ1T!#Oj526PRC\5X}!#;u:Q1fQ1S<0E3Q0M!w$$4<0E!$Eo,|Ptf{Rt!w#$:Q2H!#Dq0sC`F]!$kA-'13Le'bPr!#D#$gCFS2HQ0d!ze$cCFRcQ0i!s3$`CFR`'1RW'1R^Q2HPWfqPcP`fpfoF]P^e'bQ4IQ3a60s6S2HQ!$QE&!#d$%!xK,lQ4w!#bi%RS!u_$}Q4PQ0{#8#?R`#@!#;g$c!#;g,c!#;k$!$>,;Q0E/141954AI@4`10f9P9P`1998H0=[!$$d0P3&0L<S0EQ1M&0R<S2l36#dQ21/0`Q2<Q21fxfyp,2NNS2<O7b2Q2>Q21Q2?Q2=H0=ef|PtQ0v#NQ0v,9rP6PrQ3h=Ei3X[6!sA$P3J0bb7!s<%rep#1V2Xg05FGRt!#~DYQ!#|j-NQ3W!#|c&PaQ3_P3NO2W!%#p$!s$:T&0LhR`Q3O$1P\hR<!tT,!t?0P\P_PZPLPKPIPJP2P0P>PDPCPB!%6P&NI0@!te$B#3#T#T#[#T#T$1>-1B[R[Q1zQ1{P3Q!$x'%B96tNS3_PXQ1W!ui8PiP3!uV0`!$#B%_PZ!uX$P4P5NF0CR^!#~c$!#{|,!#6q'P3N;2V3LXi<Xj`XhTZ2chZ2bhZ2ahZ2`hZ2MhZ2LhZ2KhZ2JhZ2IhZ2HhZ2GhZ2_hZ2^hZ2]h&0g5Q3_P^Q1L!t7%Q3\/2_>0ag:40aR^5P3Q20Q3^/2_#}Q0x/2f010:3pRc9P3gQ23Q40Q1;,2\S1;Q1O5Q660f6$1VRW60[3Q3i=E3r&0gNQ3_Pt!wRAM!wT=!wR&P!w<'5!w<%!w2@4!w20bp+01aS40!w2'8P9NF0CQ1L=P9^AP8gcQ23>0[@W!u,$Ar&0g@[[[[[Z0\t!t9@5!t9+Q40!zs%!t2$9P4!t2+4^AP9!t2'8!t2%@rQ3V@2UiAS3VB1O;iA21_;AQ1~9EAQQ1~PXQ1kP\PZH2TS3i5PAQ17Q0D#8#R!$/2&Rr12rdRWQ1y-0H6Rc#yS0D<0a:S235PAP6PhQ01Q1yH0xS01>0fhB:0[AW20HhBQ3s02ScS3s56=Q17Q1x!$01%x20~X:S1L5PA!tG&F!sA&7!$O4$C!uy$i!v,$g!v9$]Q1W00~:40m!s%%S0FCOPAQ1;Q3j#z!{Y&f#zQ1<&0>_$25S40p+01e#};p:3pCOQ1y$2aRg-2Ra010:S209PA\Q1A,2ZS1AQ1D,2ZR^5EAQ1G9PA^P;PAg017eS1D%zfQ1FQ1<01D:3pS1FH0|&1NAQ0D:2QagRg>18;AP;PAQ10Q3OQ3o$1\Q0r$0c42PS3OH1IQ2TQ1y61[6S1yQ3`01`cQ3r-1`c'1S3r!{3@Q0?Q0>Q0=Q0<PN!{A5!{73A!{7%$0gQ!xx&B21_;C!xx$DQQ1~Q3i5P>Q239P0rQ!x4%J:0[2!x4$IQ!x,&xQ1L5PIPKQ!wj'MQ!wH$L!wH$Wp+020!wC$Q!w<%o!w<,209PM\Q1A=EN^Q0<Q1G7P^P;Q0=Q1DQ!vf$Q0>$1NQ0?:18;gP;Q0@!vb%H1IQ1yQ3rP6!~GBQ3xQ2\Q2bfjS3xQ55Q2vQ3G!#ca$Q0hfcS3OQ3FfaS10f`S1F!vL2Q1Z!vM%Q1B!}N@3p,1WS1Z!}R%!wN$Zp,1TS1D!#6l+p,2s'RgQ1OQ1Op,2LBR^-2j\R:P3I1Mp,2d'S1G>18;3g05GNR=g05HYS1A$0LRW21]=W$1PS20Q1t01a\S1<!t>$4P5P3I1<&1xgS40-0z4g05IdRr$0LS3W&0}5&0RrS1;36'1CVZ2RWS0F,7WX~W'7Z06='7Rr3LRc'1CVXi<,7<Xj`,7`XhT,7TZ0=h,7hZ0<!s,%;!s,%:h,7hX|!s+${!s+$z!s+$y!s+$x!s+$w!s+$v!sW%9!s,%8!s,%7!sA$!$vt&p+02:S3f!xFE!xC$Q!xA7!|r$FQ10Q1Ff_S2\!x@4d!x@JQ!x<'p+02LPMPZQ!x;//1c!vF~!vF:p+029S1d!#@#@P`P<!v`D!v]EQ2\Q3E!v^32x!v^WKp+02J!va:!#?E%0=!vU$Z0;!vO$X|hX{hXzhXyhXxhXwhXv!v7$Z08!v1$fZS1BfYS2xfXS3EfWS2\fVS1FfUS10fTS3FfSS3OfRS0hfQS0cfPS1cQ0SfNS3GfMS2vfLS55fKS3xfJRc!vQA1BQ2xQ3EQ2\Q1!vB$3FQ3OQ0hQ0c!v`$SQ3GQ2v!vQ2Pc!vP%S2bQ2b56tS17!vY@c!vY+Q3fQ1d!vU&Q55Q3xNF0CS1DP!#3M%P:PcI1MS1ZQ!#3@$cS1G/1rS1k'1R;'1!uJA0!uMOJ1c!uM6-0<tQ17eQ1DP;Q0AQ1ZQ1kPF!tp+cI2r21dm:R;AAm3:&1ggS1O9Am3+0PRg^gmRt'1!$DH']PiPbP^PaPQQ0yPjQ3}Q3Mp,2HRS3MQ39Q3uQ3:Q1sQ16Q3~Q2<p,3UHIS3~Pc!vQ%Q0<PNQ4z!#H7/4Q0@!#;u+2NQ2560d|Q275EceNW2MP;Pt21dm^S27AAm3^&1gbRt!ty&^gmR;Q3UQ27/1;Q3M41f41h:2K\^!s=%P;Pg!s0%AAm9:AAm9^Rg&0O9/Y\S2N'1+0PAAm8:AAm8^R:&0O8/Y\R|'1RQP3Q!v5$8RaPa21KOaRXJ1?Y04B2J\^9AAm9tS25-0PgPQAAm8tRt/1|P:PtP3P|P|POQ07!%Vl$K662IOP|H30RtJ1mPaPaP!su&P3P9O1P1Pm%a3S4z&0J3'fRXZ0[1RaQ08>0q1xR:H0xRQ9Am9PaP3O1Rg=6m8R^1D3:R['1X61#M!uG&QRQ/1|A6mg@S1d/1[!sC$Rg/1|PQPg!tm&!tW$1PmPaQ08PbPjp,3tq'S3fQ1t$2GS16H36$23Rt60q1Rg!tP'8RZPZ21KOZ!u8&!sk$P:P9I1}AAm9Q1D3gRQ,1^!td'!v&/f62FOA6mX@R^!tj'S07/1|S1sPZQ1d/1Q!s<$P3K2E!t/,g!t/%6mX8Ra!s`'Q2N'1S1d11^QX61S3}#M[11a!sh%S0yQ1s[!zC$2Q07P|A6mXA!t=$!t2'PmPXPBP[CV!sw%!t>&XPC!s:&&0OC/Y\A6mX>R|!s_'[P311|[Q02%a5S04&0J5'f=6m01D5:&0O2/Y\!sn$IPQ!t&&[P3%a9&0J9!sP$J1D8:&0OK/Y\g05LXp4p710R|Q09\3Ra&0L4RZQ02B0q9439A95AA845P9P4O1$0p'1S1][S1WAA953P4P5!s=&B0q8959A84S1k[S!~d$AA@94P8P9!sJ&[!%^<&H39S1kP5!$V'/!s-%0Y03X65Y02WlS1DQ1W`03Z^65`02a^l|S17P3P1Q08PBPxP4O51DBx%gBS1|'1Q021DCx%gCPmPXQ0=!v#+P31D>xS1{%g0!w4%Q0@!sD&P2%a2S1z&0J2'fQ0?56m1D2gPCQ02Q1WQ1ZQ1]B0q@849A@9[Q1kP3!u37Z03ZX65Z02aXl|S1kQ1Z!u63Z!u6'JPt1DJt%gJPFPbPjPiQ3fQ16Q38Q39PJP420GJjR|P1PjfIS1]96mX1D5xRa%g4Q1[]\]P]YX611fknRZQ0A!u0$jx%gjP0PmPZ20X3\RZXgmQ4AQ3xP4J0bO1W\WPWYPIP3P>P9P4N93=W7%d|eN;3>P5C`O5b7C`H0kW\WP!$Zy=Pb7Y0G!st$!sK<W7X61!$vy<W7!sa?Q0yP1Q3}Q1sP^PQQ07!}?'20X@\+031D5gQ1DQ!y0,9PtP5O51D9t%g9!y,&8t%g8!|,$0!}1+20X>\+03P31DAtQ1|!sP$3t&2CjRg-0G5Q04/Yk800a[Ra20G3gQ3]Q4z/Yk4001D5tRt[20G4g1D4x%a4!s?%\t!xB83N92B!{^9Xk1Pa^k1P3PDP4O220GDg1DDx%aD!sz%Q0520G>gQ1{%a>/9k+0!#3Q$M!uF/L!uF%20G0gP1PgA6mXN%g5!{Y%>!#3|,=00X\+03Ra]\!y\$%ag&0Jg'f=6mM%ggQ09g05M4RgQ09Q09POP3Q1[Pvn011!u7$!u3$Y0>Q4iQ0:P3J0bQ1[22Aa3b7W\WYP2P3P0P8L2@W7P3O11D0x%a0!u4%!w4$2xQ1z/Yk!to%<!uB/N!wb'Ix%aK!sJ+?!sJ&R[#MQ0>$0O/Y\P1P[PL%aL&0JL'fR[Q0>!{t$L:PKQ!}@$!y5'MPx1DMx%gMP4PD!{R-PmP[%dZXgmP3&0O[/Y\eQ0>PKJ0bC`!{N$!zi?!$ca30!$ca&bP!v,$!|WBWPXY^H3CX61P3I3DY2UC`O2O2Q25Q2N'1!#>_$9+0PeO2O2Z1K;Y1UW;Q3MJ1SXgmF]Q1GPrP9!%P'p'13LRmPr!s|g[Q0EQ3YQ!#gO$R;Q0xQ2?'>R1Q2<41hQ2<:1f;142?Q09Q3[$3I;6gQ3v/03Rg125fR1Q0n'0R;PFQ2JQ2YP4Q3!$/<-20_RuR^=<}SR[PGP[!#lk41K3dR[/051K5dRZ!#pf/9Pk!$&d$!$&W,P}Q0CQ0V+0oPGQ0C20_Su1Gus'G5<}!$t\7Q4k9;3f1K4d12d9'2,01!$&t-Q2XPkP9P5O4b2K3JY15WNX]6&2=4$0p\;\g^]6P=PWQ!#UI&kPkPnP5P3Q1A$0RRgI1<36R;Q1t$3K03LjRx-0z5R:Q3W&0}3Q1;36RX3LX~WZ06=PrP;P:PXPr20z4x!sL%4!sL$P=PWPWQ0F!sQ'8P9Pg!tI$!#Ve$!s6$!t?$Q40-0z8Rg!sf%9!t4%x'1P4PgPxP5P3F]L3MY1eY1dXY;I3N!s|&Q1tPj!s'$p,3WFsQ39H3OQ3uP6Q1IQ1t$1e#B#d9Cn3X[6P6Q0;Q3zQ4u+03X[6!$s<%!$&a-1bQ2[Q2HQ4m+02R=!#p6,!x%&1msR!$Ta'sSQ4P!$rB'SQ0b!$UD&D{J08!x98X9O1943AC948Q0Z#BQ1[[9C49!%=|0!$%W%_P_Q1IPnP8Q0gO6!$c+&bMQ3zQ0;=667+03eQ32P9EuQ2~P@EuP6Q3j-0tlR_,ckRsQ4uX[620Sk_%B_RW#dPkP_209k_R;Ps!#vG$k_%i_Rx1>s_-0Is[20\k_1>_71>_s%rs!#vB$k_%B;\W20Vk_19sk\WP;P6PsP620S\dQ1`P\Pd209\dRsQ13!t&%\dQ1_Q4GQ13;Id[20\\dQ1aQ13,>dQ13!#wH&\d%Bs\]20V\dQ13/9\\]PsP6Q13P6P@Q1\!$Z}&d!$Z}'_+0<PxeO1Q2i?IC_!$xfM3j!$;6&3j#=R7Px[Rx[Q3j!$2v+%=_!$;3'xQ4IQ3d60s6RxQ3c<0N=Q3e$0DQ3b$0DR=Q4JQ2H40N80NxQ!$[j0PzPAQ52PA!$[e$AQ4M@06AzP5Q4N!s0%A&0WA!s1&Q51PAPz!sU%n!s%%!#3C&Q#lRxQ1v#8#lRy'm!$zk&!$[d$1@#l-0AuQ1>#lRu'G,mx!$\V'!$'v$53Q0J!$4e%Rx!$\[2x!$]F+0R!sr$x/GR,my!sl,!%/n`P}Q4c!t\%?!s,%@!s,%A!s,$1]!|_$!sH%3x!s,$55!s,$2v!s;%!tT$1mupQ0S,H}H1:H3PK15!s%+!$|u2Q!$^R$!}H9X6Xu6Z0Y!%IcVZ0OOZ0POZ0QOZ0ROZ0SOZ0TOZ0UO1959Q1eP9PdPBP8Co[Q54?I4_Q1[\WPBP_PC!s=$!%18<>Q0?Q0@Q0AQ1]Pc!#_Q/0SQ1c%BAQ0c!$~/&D:D:%B!#ra$!$`;1`0Y!%J\V`0OO`0PO`0QO`0RO`0SO`0TO`0UOP3Q18Q12Q11Q0}Q0wQ0tQ0sQ0qQ0p!$~tPIQ0>PkPJP\Q0=PBQ0<P0Pcp+02oOSb2c0VbKc0V!%#30!$bEIQ3j$3Q-3RkQ3j!$k:'3j#@9<}p!y#,P7P3b263SkEuP3Pk!$CM3^!$CM2[3^06Q14b2bUQ2J/0ke!$@\%p!%FQ$5PzP9!~>%9!$g<,!%,Hd_!|a+aQ15#lR[5<}RRP}A<}[SR[!%,b7Q0C=<}V!%9H9!{bO!%,Z<Q4rPLQ4d1045R7/1M!%B?,!#@C/!%BCR2fQ2BQ0H!$'z%0|'0Q0~Q3nQ3nQ2e'2Q0WQ2cQ18'13C3C40r3LR1'1Q2a!zD7\,2w?;YPRYQ0W/0wRwQ2mQ2kQ2hQ2gQ0BPnQ2XPkp+02VRPOC!xS%`9;kfeO3P3Q2`/KeRp!x`%0323T6eQ4L63U!$mc%+0280N=$0;!$m@,1:06z8!%L[&P8Q4NP8PzI0{!#80+!%3Sd!y6$^P}PRP}P[!s{$1C#l-0Ao,mSQ4`H1:!y7520_VoRo9<}^!%?]h!%3p<Q4rPMQ4d1we9,95=L7!%3|,k/Ke,0Z!%?D\P3P!xf9PYP!xV3Q2e!xY&PP!%3y$!~%$pe!$M_3oQ4aPV!$vy-!#Iw&~e?;f!$NV%Q2]!yA+p!yA$5N93VJ3Wc19c1VX;mY1^Y2DY1_Y2CY2BY2AY2@Y2?Y2>Y2=Y2<Y2EY0N!$UK6p,4PURERmNJ3XF]F]NT3YH0kH0kQ2b$0geW;W;Y1fY0lY17Y0rY1sY1qY1tY14Y0pY1lY1QY1oY0oY1WY1kY1SY1wY1TP8NG3ZY1PY1MY1IY1nY0qQ0<P3EuW7L3|!#pq\P3NE3{Y1YY0\J3zY0K!%Rb@c0KY1cY1gWV!#S,>W;!sD?!sB=b7Y0wY0vY0uY0tY10Y0~Y0}Y0|Y0{Y0zY0yY0xY0s!$YZ%c1XY1AY1@Y1?Y1=Y1\Y1[Y1ZY1vY1uY1|Y1{Y1zY1yY1xY23Y22Y21Y20Y1~Y1}Y29Y28Y27Y26Y25Y24PmNM3xY12Y1`Y1RWVW;Y1FY1EY1HY1GY1CY1DY1BY1>Y0jY0kY1;Y1OY1LY1Jp,4LASTNF3wY18Y1:Y1aY1mY1]Y1rY1pY0fY16Y13N<3v!&4I8!%}:&!#\;$Q3uQ3~L3tN:3qc0go"). Qed.
End FreeAppMid.

(* [comment removed for export] *)
Section FreeNewHitMid.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st : ltac2:(zQ "10!ip5$0") := ltac2:(zQ "10!hrf@1$0?1s").
  Let TH : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!spa@1$0?1s").
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sq2@1$0?2ch").
  Let size : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sr1@1$0?2ch").
  Let tq : ltac2:(zQ "10!src$0") := ltac2:(zQ "10!ss6@1$0?2st").
  Let l : ltac2:(zQ "20!j4!ssf@1$0$1") := ltac2:(zQ "10!st9@1$0?2tq").
  Let k := zlen l.
  Let lb : ltac2:(zQ "10!ssf$0") := ltac2:(zQ "50!hl6!h9!su4!ssf!suc@3$4$3?1l@4$2ZZZ@1$0$1").
  Let LA : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sv3@1$0?2lb").
  Let pc : ltac2:(zQ "10!uv1$0") := ltac2:(zQ "20!uvb!vg5@2$0?2st$1").
  Let cnt : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!vh4@1$0?2pc").
  Let chunks : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "10!vi0@1$0?2pc").
  Let cp : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!h9!vid@3$1$0Z?6chunks").
  Let B : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!vj2!vg5@3$0?2st$1?2cp").
  Let CHI : ltac2:(zQ "30!h9!j4!jb@1$1@2$2$0$0") := ltac2:(zQ "40!ige!npe!tkd!tlb@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "50!ige!tm3!tlb!tq9!npe@6$3+pgsq0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!nv4!h9!rv0@1$2@2$0$1?1T").
  Let d' : ltac2:(zQ "10!tr3$0") := ltac2:(zQ "20!tvd!ugb@3$1?1d@1$0?1T?2nT").
  (* [comment removed for export] *)
  Let tq' : ltac2:(zQ "10!src$0") := ltac2:(zQ "20!vk5!um0@4$0?2tq?1B@1$1?2ch?4size").
  Let cache' : ltac2:(zQ "20!j4!uv1@1$0$1") := ltac2:(zQ "90!h9!uo2!vg5!vkf!uv1!vl7!vm2!vma!vmf@4$5$4@1$1?2st@1$6$2@2$3@2$8?3cnt+1@2$7$0?6chunks").
  Let s' : ltac2:(zQ "10!o0$0") := ltac2:(zQ "40!un0!unb!oje!ok4@7$0?1s?2ch?3tq'?6cache'@1$2?1s@1$3?1s@1$1?1s").
  (* [comment removed for export] *)
  Let Wh : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "30!ige!usc!npe@6$1?2lo@2$2@1$0#k0?2sp?2TH?1U?4size?1d").
  Let Wn : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "30!ige!vr7!npe@5$1?2lo@2$2@1$0#k0?2sp?2TH?1B?2LA").
  Let W : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "20!mv1!mua@3$0$1?2Wh?2Wn").

  Hypothesis HR : ltac2:(zQ "10!hr6@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis CHIN : ltac2:(zQ "30!hhmb!hhn4!v7@3$2$0?2ch@1$1?2st").
  Hypothesis ALLOC : ltac2:(zQ "40!ip0!hho2!hhp0!hhpc@3$0$3@1$2?2ch$1").
  Hypothesis UHI : ltac2:(zQ "60!hhq6!sr1!sq2!hhqd!np7!vmf@3$0?5HCEIL@2$5@1$2?2ch+h0@2$4+h0@2$3@1$1?2ch+8").   (* [comment removed for export] *)
  Hypothesis DEP : ltac2:(zQ "20!ita!ksd@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!pl6@3$0?5HCEIL?1s?1d").
  Hypothesis MI : ltac2:(zQ "20!ita!ru5@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!ige!ita!rpb!npe@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!hhr9!hhs1@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!ige!np7!hhs1!npe@2$2@2$1?2lo+ro0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!ip0!ige!h9!hhs7!npe@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!ige!np7!hhs1!hht1!npe@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis TP : ltac2:(zQ "50!ip0!ige!hht8!oj8!ij1@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis DLO : ltac2:(zQ "60!np7!hhs1!uua!te!hhte!hhu6@2$3@2$1@2$0@1$4?1d@2$2+h0+hggg0?2lo@2$1@2$0@1$5?1d@2$2+8+ogg0?2lo").
  Hypothesis DCAP : ltac2:(zQ "60!np7!te!hhue!hhva!hhs1!hig3@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis FCH : ltac2:(zQ "d0!ige!npe!tlb!hhh5!hig9!ip0!hih0!te!ita!tm3!hihd!np7!hhs1>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!ip0!ige!oj8!ij1@3$0@1$3@1$1#k0?2a0@1$2?1U").
  Hypothesis BLK : ltac2:(zQ "70!nma!nn2!hl6!ita!roc!nu8!hhgb@4$5$3?1m?1U@3$1$0@2$4@1$6?4size?2bs@1$2$0").
  Hypothesis SHB : ltac2:(zQ "90!nv4!te!ip0!ige!h9!hiic!hij3!rv0!ij1@2$1@3$5?1m?1U?3sbs@3$2$4@1$7@2$0@1$8@1$3#8?3sbs@1$6?4size").
  (* [comment removed for export] *)
  Hypothesis QSZ : ltac2:(zQ "50!te!hij9!hhs1!hig3!hht1@2$0@2$2?4size$1@2$3?4size@2$4+2+i0").
  Hypothesis NN : ltac2:(zQ "40!hhh5!hig9!ip0!him5@3$2$0@1$3?2tq$1").
  Hypothesis HIT : ltac2:(zQ "30!ip0!hil0!h9@1$1@3$0$2?3cntZ").
  (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. ndestruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let HC24 : 0 <= kBatchClass < kNumClasses. Proof. unfold kBatchClass, kNumClasses. lia. Qed.
  Let PCS : pc_chunks (get_pc st kBatchClass) = cp :: tl chunks.
  Proof.
    pose proof (co_count _ _ (WF_cache st kBatchClass WFs HC24)) as C1. fold pc cnt chunks in C1.
    unfold cp. fold pc. fold chunks. destruct chunks as [|x r] eqn:E; [| reflexivity]. exfalso. apply HIT. rewrite C1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition free_newhit_gmid : ltac2:(zQ "10!hvd>0$0P") := ltac2:(zQ "he1!ige!ij1!ij7!j4!te!h9!ind!hl6!io7!ip0!ip5!hvd!ita!iu3!iv4!jb!jj9!hq0!jo9!jtc!kid!ko1!hrf!ksd!kt6!ku6!kv7!lk3!lo8!lp3&>0@1$1@1$0#k0@1$8@1$1@1$0#8\3ms'$b@2$2$5\2b1$5@2$2$5\4actx$5@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2@1$3@1$1@1$0#8\2jk@1$3@1$1@1$0#8@2$2@1$3@1$1@1$0#k0\4rest@1$3@1$1@1$0#k0@2$2~0\2m'~0@2$4@3$9$b^h4@7$hb@ha$h5?2sp?2gp?2tp?2s7?2s8?2s9?3s10?3s11?1U?4size?2TH$h9^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4?1F@2$hd@1$0#k0+mtlv4?2fc@1$e@1$1@1$0#k0^1@1$hc$c@2$4@h6$h4?2sp?2ra?2s0?2s1?2s2?2s3?2s4?2s5?2s6?1m^1?1W?2lo?1U?4size^h3^h2?2TH?1T?1d^3^2@2$4@5$h1?2s'@1$7$5@1$7$5@2$h0?1U?2LB^1@2$4@3$h7$c?2d'^1@2$2$a\3stX$a@2$2@1$3$6\3ev0@1$3$6@2$2@1$3$6\3ev2@1$3$6@2$4@3$9@1$8@2$f$a@1$3$6@2$h8?2st?1U@5$h2?1U?4size^3^2^1@2$4@2$h3^3@1$h6?2s'@3$9@1$3$d@1$ha^2@1$7$d").

  Theorem free_arep_newhit_mid : ltac2:(zQ "a0!ige!ita!iv4!mt5!mj9!mnc!lk3!lo8!lp3!ij1@3$4$1$3@7$6@hf$5?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$8@1$0#k0+pgrm8?2fc@1$2@1$9@1$0#k0?1m@1$7$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_FreeMid ()) ["HCW"; "FreeNewHitMid"] "#'aBp'0p'1p'2h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61xi001xh71Hh84__x3h92_Hh:1zh;4__p1h<4__x4h=6__sat8h>!s/%7h?2Hah@2HxhA3_H0hB2H0hC4__x5hD1EhE1li011lhF2AXhG4__p2hH!sd%1hI!s/%3hJ1ahK1bi021bhL8heq_sizehM3_H1hN!sM%4hO4actxhP6heq_THhQ5heq_UhR2jkhS2m'hT4resthU1yhV1AhW2H5hX3K0'hY3PC1hZ3_H2h[7!tO%0h\!s0%27h]!s0%31h^!s0&3h_3a1'h`3a2'ha3a3'hb3a4'hc3a5'hd3a6'he3a7'hf2b1hg4cstrhh1ehi3ev0hj1fhk3j2'hl5lemmahm3ms'hn2q0ho3stXhp3t0'hq3t1'hr3t2'hs3t3'ht3t4'hu3t5'hv3t6'hw2BLhx2H2hy2LAhz1Wh{2Wnh|3_H3h}3_H4h~!vH%0i031ki042lbi051ni061qi072sci082ubi093AB1i0:3AB2i0;2BJi0<3CB2i0=2ELi0>2H1i0?2H3i0@2H4i0A2H6i0B2H7i0C2H8i0D3Hubi0E4LB23i0F3LB3i0G3LBci0H2NEi0I3NEUi0J3PC2i0K3PC3i0L3PC4i0M2SJi0N2SKi0O3STIi0P2UBi0Q2ZTi0R3_H5i0S!uK%2i0T!wt&5i0U!s1&6i0V!s1&8i0W!s1&9i0X!x4&0i0Y!s1&2i0Z!s1&4i0!xs&35i0\!t0%5i0]!s0%9i0^5__x10i0_!s/$1i0`4__x6i0a4__x7i0b4__x8i0c4__x9i0d1ci0e2chi0f5cstr0i0g!zi$LAi0h2j0i0i2j1i0j2j2i0k2j3i0l2l0i0m2q1i0n2q2i0o2q3i0p1ri0q2r0i0r2tpi0s6ACEILBi0t3ACRi0u3BD1i0v3BD2i0w3BL0i0x2BTi0y2BUi0z3CB'i0{2CCi0|3CHRi0}4CNT'i0~3CPSi102CRi113CVBi121Di134DEP'i142E1i152E2i162E3i172E6i182E7i192E8i1:2EBi1;2EPi1<4ESO'i1=3F4'i1>2FCi1?4FLG'i1@4FULLi1A2G1i1B3G10i1C3G11i1D3G12i1E3G13i1F2G2i1G2G3i1H2G4i1I2G5i1J2G6i1K2G7i1L2G8i1M2G9i1N2GTi1O3HDRi1P4HDR'i1Q2Hbi1R3Hb1i1S3IA'i1T3IENi1U2IMi1V3INIi1W4INSTi1X4INlbi1Y2JRi1Z2K0i1[2K1i1\2K2i1]2K3i1^2K4i1_3LA1i1`3LA2i1a3LA4i1b4LAD1i1c4LAD2i1d3LATi1e3LAUi1f3LB1i1g3LBsi1h2LEi1i3LR'i1j3MI'i1k2MUi1l3NB4i1m4NBJ4i1n2NDi1o2NZi1p4PC14i1q4PC34i1r4PC44i1s4PFR'i1t3PLUi1u2POi1v2Q1i1w2Q2i1x2Q3i1y2QCi1z3QSTi1{4QST'i1|2RRi1}2S1i1~3SBSi203SBXi212SCi224SHF'i233SHui243SJ1i253SK1i263SK8i273ST'i283ST4i294TFB'i2:2TQi2;3TQ4i2<4TRB'i2=3TSTi2>4T!sY$?3UNWi2@4UNW'i2A3UW'i2B2V1i2C2V2i2D2W0i2E2WMi2F3WQ'i2G2X1i2H2X2i2I2X3i2J2X4i2K2X5i2L2Y1i2M2Y2i2N2Y3i2O2Y4i2P2Y5i2Q2Y6i2R2Z1i2S2Z2i2T2Z3i2U2Z4i2V2Z5i2W2Z6i2X2ZUi2Y2a1i2Z2a2i2[2a3i2\2a4i2]2a5i2^2a6i2_2a7i2`2cpi2a3ev2i2b5heq_Bi2c7heq_CTXi2d!s1$cnti2e!~o$cpi2f!sO$ki2!#3&$nTi2h!s0$sbi2i4junki2j1mi2k5nd_i4i2l1oi2m3pT1i2n3pT2i2o3pT3i2p3pX2i2q3pX3i2r3sc'i2s2t0i2t2t1i2u2t2i2v2t3i2w2t4i2x2t5i2y2t6i2z2z0i2{2z2p%0p%1p%2p%3p%4p%5p&0p&1p&2p&3p&4p;1p;2p;4p;8p;Op;7p;3p;5p;6p;9p;<p;>p;@p;Bp;;p;Fp;?p;Jp;`p;Tp;Gp;Dp;Ap;Mp;:g00g]j13Tg00mMk10r!s0$kk126Tg01^Hj1jTg028`k10jTg015BR0j20Tg00c9j1@Tg00eZS00j1\Tg00fYk133Tg01_Vk10NTg00hgk10^Tg009^k10iTg00P@j2ITg01\Fj2!s8$hBj1;Tg00jok20xTg02Kbk13?Tg00;Gk12MTg00Wfk11uTg00Xnk11VTg02[=k44dTg02\aR1k11HTg02U6k12KTg02MAk142Tg0122k13}Tg02NEk13!t4$OJk13uTg03I7k82QTg00BnS01j22Tg03JBmO3jTg03KCk21^Tg022Fk12C!s:$ik13]Tg03M1k70@Tg03N2k33OTg00ikj1]Tg00OdS02j21Tg00kLj2JTg01``k22;Tg01mEj3~Tg01Z2k13ETg01akk1!sV$1bnj2PTg02POk11y!vT$fj37k128Tg02QYk1!ty$2Rck11vTg03O2k839Tg02WEk13!sN$XKk137Tg02gGj4lTg02VAk130Tg01h6k11tTg00?1j!w;$1i?k11!wk$jLk11LTg03P:k32tTg03Q>k206!s0$^S03j1QTg02YQk118Tg03R>k417Tg05bSk12mTg05R?k21nTg05Nfk11OTg05cZk12hTg01fik12gTg05SHk11lTg05dfk21NTg02aLk11E!z7$Wk11RTg02mOk20RTg03VOR2k10MTg0117k3!zv%Sok21eTg02e1k3!z`$5e>k11!t4$fPk22XTg05g]k12BTg05hlk24`Tg05MTk31aTg05j9k34WTg044:k111Tg02ZSk20[Tg027ok20!xo$3Ak210!s0$ik30}Tg030Fk21FTg024Pj2S!{k$>S04j!u}$20Zk140Tg0218k1!xq$21ck2!y6$23nk23t!sc$jk23sTg025Vk33rTg0265k43qTg02dTk30JTg03Y`k11DTg05kKk51cTg00H[k41bk34!uu$P1k43!wS$lVk33!w'$_fk23kTg00nNj!zw$5m]k32!w4$8@j6sm94Nk84GTg05n7k63iTg01eck33hTg05oCk63gTg060Wk83fTg061jk23eTg0637k13dTg064Gk32D!s0$am93cTg01Wbk13bTg01Xlk13aTg01[7k13`Tg01]@k13_Tg00Ajk33^Tg00I6k23\Tg00J<k23[Tg00KDk23ZTg00LMk23UTg00MWk23TTg00N^k23!~8$P\k33NTg00Qfk33MTg00S0k33LTg00TAk33KTg00UPk12?Tg00V]k23JTg00Z8k22=Tg00[Ck12<Tg00lnj14!vY$nk20STg01kZS05j!}R$3S?k13ITg03TJk31[Tg03UNk42:!zt$ok41>Tg01cKk13HTg03X7k60K!s0$Sk53FTg03Zhk21XTg03[?k21W!s0$\k125Tg03\:k43D!s0$]m<1UTg03]Bk21!ye$9>k23A!s0$_k30vTg01nIk21}Tg022hk21T!sX$dk41{Tg03^Ok23>Tg02LgS06j!|$$20<k13=Tg03_4k71xTg03`;k51wTg03aHk23<!s0$kk33;Tg03bHk40tTg00E0k61Sk547Tg02iPk136Tg02jRk135Tg02k]k132Tg00DUj4eTg034Mk30z!so$bk731!|]$gk22~Tg031Pk32!u9$;Vk20!s:$clk82!sX$f8k82yTg02?Dm<1sTg03g=k62xTg05^Zk51rTg03hHk52!u7$iWk62vTg0667m>1qm?2aTg03klmO1!y$$afk12uTg03m9k21!uc$nEk22!}N$fBk31fTg02hKk12oTg02lnk21;Tg02eij1gTg02mlk21:Tg02nSk219Tg02o:k2!yZ$2o`k21!xB$50m@1oTg040[k82lTg041ck42jTg0434k32p!s0$Sk42!~c$]kk11mTg02_5k11MTg02`@k12!tc$bQk41!}9$7Fk32!}M$8Xm92{Tg069km92|Tg06;>m92!sN$<MmB2cmA4?Tg04YLk21PTg06=Sm;2bTg06>Xp<1c34Tg06?gS07k10gTg045nk11kTg046PmF0OTg06A9k22`Tg048nk33:Tg04:1k323Tg04;4k21zTg04<7k42_Tg011Vk41=Tg04=?k22^!s0$Vk13@Tg04>ck22]Tg00kik40wTg01THk127Tg04?lk32\Tg04A3k30yTg04B:k21i!s0$Tk22[Tg00:>k51YTg008^k22>Tg04C]k21hTg04Dlk51]Tg04F<k21ATg04GQk11!tP$H_mJ2!s0$`jk12Z!u\$Vk12YTg04Q6k13!vO$Bck12WTg06D3k13R!s0$]k13STg06Eim?2VTg00`Jk13VTg06Fok83!sX$H<k42UTg06INk33XTg00=Qk53!u&$>Uk22TTg00?Hk1!#9T$@KS08k20PTg05ZIk14cTg05[Lk14bTg05\Ok14aTg06JPk44_Tg06Kam`4^!{K$Kk34!ui$K9k34[Tg04LHk22PTg04M4k34XTg04N@k34VTg04O6k44U!s0$ik62FTg04P[k30|Tg04RAk44RTg04SIk52L!s0$hk34QTg04TZk74!t$$UUk44OTg04V3m;4MTg04W>k14!sX$XEm94K!zF$kk44!t2$[0k52ITg04^Nk74BTg04_Yk14ATg06M0k64@Tg005Lk848Tg04cPk444Tg04dZk14!z7$e8k245!s0$Vk346Tg06NDm>41Tg003Dk649Tg04hSmT4!zs$iYmG4;Tg0366m<2HTg04j_mD4<Tg04kdk64=Tg02>4k54>Tg06O[k73!|l$Pmk83{Tg04limM4CTg04o5k83zTg050?m:4DTg00dVk14ETg02cSk43yTg02eRk34HTg02\Hk34ITg06R1k43!{a$o^k24!#>s$Kk312Tg02<Bk33vTg02:kj4wTg02APj7tTg051Cm<2G!s0$hmB1_Tg02@Ik31C!st$2k22N!sW$2k44STg02B4k64T!s0$Xk70{Tg032]k72OTg02C<k80V!t:$Hk34Y!sD$9k64ZTg052nk32RTg053Km93p!s:$Nk43oTg054ES09k13nTf0R3$1R$4Ep>09%\3#]p=kg015_R4f2R5f1R6=O433Op=vg016cR7f3R8P5AO463H0wp=cg00\KR9/13p=5g00G:R:?763p=61256/23p>0:1I63,25p=G%;3#;p=m%;3#3p=b%33#3#3#@p=Z!sB$#3#3p>0cP7P5P6P3H3yp=>!t@$p=f!s<+0wp=9%\6#]=O43p=XP7f4R;P8%]!u'$9O45H0wp>0Ag03>OR<01e3p>0aP<P:P1P3H1=p>2AB4H:93p>1BB4I<63p>0p%]5!sm&5O4p>0>12!u6$,28,2;p>0X!u,$p={%3!uE$`!s-$#;!u1$k!sb&p>1?!s_&p=NA7:39p=C!ug'3p>0`!s3+!s$&@p>0711851163'Bp==g038B/13p>0e1056!w/$<11!vy%=H11;81156'B!s6$aP;P8P5P6Cl!s6$V1i63=7:9p=o!vp,wp>0Q%3!t>$1Q11!tr%>1Zg018lS0:g02J[S0;773p>0m!tG$03p>0h1056=7:3p>011S:3p=AP:!tC'P3Esp>0B1I93p=^24J!sO$021T:3:12:6p>0L!s4$p=DB3v:!w6$CB12:63p=EP5g006QR1g02C`R=P=g02D@R>P:P6g02K;R?P3Cwg02EGR@Ftp=U!tM/J0Kp=}!uG$B5p=y1085/16/B3p=rg00^7RA??63p=F!z?$#3#;p>0=!wm$B5p>0<%43#4p>29!s/$!s$?p>3G!sKD!s$Cp=YP:g055MRBP:P:P2P;Q03P8g055l!uL%N<2Gp>24PB!s$$:P:!sY$6YR2Q03!s%%P0g0579RC!v%%g01D?RDP9P3NB1_p>3C!s`'!sV%f5RE!vV,!t0&0!sH%!s$&0P3P6P5P0P8P;PEf6RFf7RGf8RHf9RI!s~&B1139p>0D21}!x\$2B1C:63g02IoRJ+2Np=qg02ICRK?O!x^$FP:!zH&4Sp=RP6P1P=P=P>P3J4Tp>0u22J:3p=zP:P6P!x`$p>0GP8!sO+5!s[/P@FtK0{p>0HP;!s=+!sS,:P5g02D`RLP6CwP@FtP3!sV%;P5!sL+6P3K2Op=d!s:-:P6PLP3!s[%p=:PF!sA+!v\%!t^/3L0VL0Vp=K106397:5p>1|!sj,p>0dPE!sY+!tx,:P8PLP5!ti&!so%p=p!~f+2p>0IB4Y!|<%l!uZ0!v#4L0Vp>0f!wK%p>0?P:B12:5!tS'=|!vB85!tJ/>03!#72$;#;p=h!#4T23p>0T!vX20{p=W!w:/!tC/!v\%x!tb%:1C:5p>0o!w-1g03GWR!sU,>0\!vK08!t?4!tx$1G!~#'3p>13125601<3p>05A7:63#gp=[1P56/0397:8p>0E22N3Jp>2n!z81Zp>0s!zY$?!#4?$Cwp>16!x/0b!xb6p=LPFP!|\-CeCep=T!sQ0!u1,!z=%2Op>08!sI@0{p>2k!~S/P!~N/PC!tB/!}D%2ig03?ZS0<,03p>0qAOK639OK5p>0_1156,B8/23p>1!yu$/B!#=8$2r1156/B3p>1J%g3,26p>04!~_&!~]$PFPGPHPIf:RCg03=?S0=f;R0f<R2f=R@f>S0>f?S0?f@S0@fAS0AfBS0BfCS0CfDS0DfES0EfFS0FfGS0GfHS0HNJ2@p>0UA78!#:q%_B2R::3p>0Wp-0R1Q08g057\!ud093pp>1`!v3$6P3H3op>0Y18A3p=MQ0:&3n3Q0;37p=uA7A!{p$Z!t#$!#:\&n!#6D$19LRL#3R?#3S0I#3S0J#3RJ#3S0K#3S0L$0rRM$26RNP!s$$p,1mROp,2chRP#jRQ&0jJS0M'0%@?RR$09&09E%\9S0N$33S0O&0NPRS#\$0^S0P%k;&0i4RT3v3vCcS0Q%5EQ0L#3RU#3RV#@RW,IE%@US0R,iEQ0J#;S0S#@RU'640:RX%5;Q0L#@RY-0xRRZ7G;R[p,1sR\$3?R]%;?S0T#3R^#mR_#;#b#ZS0U'0%;LS0V#3S0W#3S0X#3R`$0c#ZS0Y,0]Ra5>OS0Z&099S0[/fTS0\99OaS0]POg058MRag059R'0g03:US0^#kg03;jS0_#\Q0=/XTI0AS0`!sV$:YS0a,0]&2M\Rb$1uRc$1VS0b$0aS0c#kQ0b$2A$1BS0d#\Q0bP9P9P9&0i:S0eH4dS0f+0pS0g$1HRd&2KcRc/XT'X!t4$h%3_!uS%i,0]R_B0>63T:0>85Re59ORf!tU$;^,0a&42\Ra#kPTCcS0jg05<i#\S0kg01Q7S0l&3}\RgP]Pa&3x\S0m&3u\S0nPOL2QS0o'2I0XI0XZ0oNZ0nNZ0mNXnNXO:Xf:Q07p,2raS0pp,2spRhp,2gpS0qp,2tpS0rp,2t0S0sp,2t1S0tp,2t2S0up,2s0S0vp,2s1S0wp,2a0S0xp,2a1S0yp,2a2S0zp,2a3S0{p,2a4S0|p,2a5S0}p,2a6S0~p,2a7S10p,2s2S11p,2s3S12p,2s4S13p,2s5S14p,2s6S15p,2s7S16p,2s8S17p,2s9S18p,3s10S19!s/$1S1:p,2t3S1;p,2t4S1<p,2t5S1=p,2t6S1>NO3jp,1FS1?Q0I#;S1@#3S1A#{S1B#`S1C$0k#m#`#Z-1^Mp,2fcS1D&2CNS1EPO&3]7S1FK0@S1G63O7S1HQ0QPXP[Q0ZQ0]Q0`Q0hPfQ0jQ0oQ!sD$%5FRf1IFWQ0R,iF/6U40:AGfFZ!sZ0OP_%]CPI%]GR_/fT-1?HI0A!sp%%@LRf/1SS1Ip,5HCEILR[%@JRX,JQS1JQ0J#@Ri-2;SS1K,0XS1L3~S1MQ1K9~[QS1Ng02EgS1O/0XS1P/1QS1Q3NS1RQ1K,0QS1S&3E[Rj'1S1T1iQXS1U#CS1VQ1K,1SS1WQ1K&21SS1X,Pi'6S1Y&0`V!~f$k/1]S1Z10]kS1[/1jS1\1i]kS1]#CS1^Q0V#;S1_#{S1`#3S1a#;#`S1b#;#{$0`$07S1c/1gS1d%3^#{R^#3Rl#@Rm,0gS1e!sy$fQ1eP]Q1[PgC=S1g&0eaS1hg039HS1i,0aRng02H7Ro;<jS1j%3VS1k#{RV#3S1l#@S1m,iaRp#CS1nQ1[Pa10nkS1oP]C=S1pQ1ePaQ1o!t/%qQ0m!s%$T#;S1r#;S1s#;S1t#@Rq-0xRS1u'1S1v5HoS1wQ0n#5Q0nQ0m3GS1x&1ybS1yQ0^57:S1z&22bQ0_!s3${&1vbS1|Q0=!s6$}Q0cQ0c'6S1~Q0c#5S20Q1|,1cS21%5cS22Q1HQ1IQ1RQ1TQ1VQ1WQ1YQ1ZQ1\Q1^Q1dQ1fQ1gQ1hQ1jQ1nQ1pQ1qQ1wQ1xQ1zQ1{Q1}Q1~Q20Q21Q22P[P\POPPp,1dRcp,1RS23p,4CHINS24p,3DPLS25L39Q1[Q1J10QiS26P]Q1eQ1JQ26Pg&38cRrQ1m,PXS27'0S28!sB&r&37cRs%@VS29,PiS2:'0S2;!sE&sC=DaDaDaP]PoPrQ27ClS2<!s4$sQ2:ClS2=PaQ1i/0oS2>!sI+?PaQ2>!sJ+@PgPm!sC+A!s4$!sB'B&30\S2Cg03DVS2D!sM+EQ2CQ2D!sO+Fg02FlS2GQ2G&1tbS2H7?3S2I&1I6S2J&1L6S2K!sf$Q2JQ2K!sa&DV[_07S2LQ279~[rS2MQ28/1jS2NQ2:9~[sS2OQ2;!s9$PQ1HQ2<Q2=Q2?Q2@Q2AQ2BQ2EQ2FQ2LQ2MQ2NQ2OQ2Pp,3SHBp,1URVp,3sbsS2Q62tOS2RQ0J$0r$26S2SQ2Q+06Rt#QRup,4sizeRv$21S2T'6S2U'2Q01Q2RQ2UQ1HP3Q2RQ01%5VS2V1oViS2WP7PO&18VS2XQ2QH17S2Y'2S2Z!sZ%[RwP3Q2VQ2Z!sq$WQ2YP!s9$WQ2YQ2U!#?U$PNPO&2m\%@^S2[g03B5R^'P'0Rw21nb^Rx$1OS2\#\$0^&2h^S2]!s2$/fTRyCcS2^10wi&2g^S2_/XTRz59OS2`10wXR{&1lxS2a-1N:$1E60QOS2bQ0I#@S2cQ2\'P,0{Q2[,0w5>OS2dQ0W#;S2e#3S2f#ZS2g,0]R{%3l#ZS2h'0Rl=9OeReQ0K#@S2i!~0$2j,P^Rx,0aS2kQ2a$1BS2l/PX'0R|Q2_,0|R}!t/$m!vU&|Q2SQ1_#;S2n#;S2o#`$1Q$1RQ2_00Ri$0M41j!vt$p!#8@%2\Q2a-1e:'6S2qQ2\,1fS2rQ2\<1ZXS2s%53S2tQ2j7G3Z2`:Q2a61\:S2u11a|S2v11}nS2w&1gbS2x$0mS2y3N!#>5$I0XZ0kNZ0jNZ0iNZ0hN!z5$^Q2`Q2bQ2dPeQ2mQ!t],qQ2sQ2uQ2vQ2wQ2y!sU3OPlP_PFB0>E;TI0A!sdAp,2stR_02X^Rlp,2cpRe/PXR}'0&2BbS2z@0hx}R|,63X::&2B_S2{/0xB013}|X::%A|Pl24`_^I0BB1a_^eS2|B4W_^eI0Bp,1B!t$$sbS2}!ss%}'6RxePx&11tS2~%5uS3020[MhRu00]XS31%5u%5XRt1iuXS32#5[[S33p+01KRxQ0R+0]%5xQ0R#5S34p+01MQ0R'i#5[[Q2i-10RS35%^RS36Q2i#5Q2j#^[S37[S38%5RS39g03H[RxQ2i>0}R6UW?S3:Q39Q2j#5\x]?S3;210RqS3<Q36%5qQ1u!sk$=[S3>Q39B0}Rq6VxW?S3?Q39Q1u!s`'@20]QXS3A%5QQ1U#5S3B\t[S3C20]]kS3D%5]%5kS3EQ1]#5S3F[[S3G210RYS3H!t?$Y%^Z[S3I[S3J!t=&Y!t=&KQ39%5Z!t;%LQ1m-0]aS3M%5aQ1m#5%5p[[S3Np,4HC24S3O119^S3Pg00\iS3Q,I^S3R'2S3SQ01Q3PQ3RQ2[%@`S3T'PR`%;JS3U#`S3V$0`S3W#@RJ,0]601{P3!sW%PGg03G1S3X21F9R'SQ36eS3YO1S3ZQ3IP2Q!s3%[Q3=Q0?!s4&\Q37&0iKR{%nKRK&006S3]&40:Rp&3~:RY22J:LRtQ2g+0LS3^Q2[#DS3_Q3T#DS3`+0C'E20LtJS3a3U23tY>R>P3P5Q0:Q0;'S23s35$0mdB3r:96H3qRqb3b4b5X0:Q2g,03S3b103JS3c801`^0:P3P]O1b2b^b]b\WBW7P6P3O2n20010!s#$12!s/&bJc0Tc0Ub\c0Vc0Wc0Xb]c0Yb^c0Zc0[bgp,2THR`/0JRJ,6wR|eP|Pwp,3cntS3d#\$0^R|/fyR~99O3X::Q0@PJP3D}A9OJ~Pw103iS3e=9Oz!sD+6D}10JiS3f=9Oz!sJ$XS3gp,6chunksS3h!#6v%S3i60QO!s`+5!s`$XS3jQ!s@%PwQ3gQ2cQ3d'PS3k'0Q2[,035>!s[,8D}Q3jQ3k'0S3l!sF$JS3m5>OP}Q2_,03Rw9>!u4&?PlPEI0B!s?$lS3n9>OlP}11a3X::PIPlPFI0B11alS3oP}11wn!s?'GI0BQ3n/1nS3p1f|TR|>0J4y99OJRnA9OJ|S3q&1D|#Q,0J=9OyS3r'2Rw[Pn\wP7POPJP|PyI1cPFH1bPw!{>$qQ3r!#<;$!s1$P_P^p,3WFsS3sQ3OH3m:3l_^Q0:P1&1g_S3t21n_^Rw$1ORyQ2]'1%Cyn!xo'20000P_P^PeQ!sh$%n:RyQ3h-3k:S3u9O:eA?:e3XEy16eeQ3u9?:e%Ae42E&1lwp,3PCSS3vEsRwJ3iQ2|:3h_^P[P\p,2OKS3wP^PlP3J3g10]oS3xPlQ3nP]C=P[P\Q!sF&6PcQ25L3fQ28/1lS3yQ3n;yrS3zQ2;!s8${!s8$sS3|!#?A$3zQ3|!v+&zQ3|!su'PQ24!uH%O23eb^$3d9?:eQ2a9?:e<2DwS3}N93cB1ab^eRwQ2_&3bPS3~&3aPRy/1wCrQ1OQ3~'1S4011yjS41Q3~&3`PS42'1S43Q3~/oiS441oyiS45Q42&3_PS46<01QS47Q1S/1yS48Q46,1XS49Q1IQ1HQ40Q41Q43Q44Q45Q47Q48Q!sD%23B3^[\OS4:23\[\S4;23!s6$<23Z\OS4=23U\OS4>23T\OS4?23Q\OS4@Q2tQ3Q7G3B3N\O6B3M!s+$L!s+$K\O6'23N[`0d:S3Q&2?bRw,F3S4A23JO6[`0eAS4BQ0b-2=O&2<b$1VS4C-2=O'2S4DQ2S#nR|POPV%4DS4E#4Rn#4S4F#4S4G#4S4H#4S4I#4S4J#4S4K00S3PTCcS4LZ08|S4M'8S4NQ4;Q4<Q4=Q4>Q4?Q4@Q3QQ4BQ4DPOg05=l,JQR}g05??RzP:&3IPR~PRQ0V#@S4On011!z},!#\=$6Q0OQ0P1X3TS4P'f3vCc%56S0P?G6!#R`$6/6U3NXO:,8:Xf:,8:S4QQ46/6XPOQ42Q0X$0c!#T7$b$0=$0k#b#m!s0$c!s@:#@#k%\}PTI0AQ42/0XQ46Q2i'J61[O40<S4RPzP1P~!~2$QPSH2:!#CF%QQ1XH2:'2R}B1[OQSPOPQQ1X$0Mg05@JS4SH1>'2S4T!uh1S4U10QSRU1JyU61[OS4V!u8%46!#D#%g05A_RWH1>POQ1SQ1S,Jy!sB&PWH1>!#3%$3HPPx!sa$/JoQ4K#4S4W$29S4X#4$29$3GS4Y#4#Y!s$/S4Z!s93#Y!s|$!#3_/13NS4[Q4NQ4QQ4RQ4UQ4VQ4[PzP~!v2$3P}Q!uR3Z0dzP5g05C;p,5ALLOCS4TJ0KP}!v`$V&0MvR}p,2bsS4\+0S/fTRzp,3BLKS4]I3F&1Dz#Q,0V9>OV&0MSS4^01XDS4_#QS4`,0QS4a,6U21W9SRz/09R~,0QRW,6UP:P:&28:S4bP3X6:S4cQ4b1663$25XU:X6:PUPU%AUQ4aPWQ4c!s%%!#sw%DF1063H3D#AZ2j:Z05:PQPQ%AQS4aQ4`P~!sU%%Q3S4`#AX6BS4dQ4_P~Q4^PzQ4c21W9!tH%^PSPS%ASR~I241S:9S4_H3CJ20N:3BN<1U21~9S%^SRW16zS'2&0DS%Cz40<PzP:&0jL-3A:S4e&02nS4f60v:S4g21}:DS4h'q00F{PK&005S4i&008S4j7R6S4kPpPYPY20uYES4lPYQ0V#zRn%z?R?+0GH0HPYPYP?21T:9RL20uYFS4mI0;5dY&2C=R=PY%DfS4n=:Y?S4oP=1Et?Rz1EnL,Et5UYFKP>P!#@W+X1:X8:X;1XG11656,28&0D6<0<;11f5S4p1058S4q10;981|5[[^0:^1:^8:^;1^G1P3%C6S4rPWP6PSPQP5p+01lS4sO7b2c2{bxH1{10VvRW21X}D!y>$R}'6P}A>OV3X::P6PWP3I0BA>OVW23>iv11ivS4t1IviS4u'BQ06Q4tQ4uQ4NP3Q4t!zY%10ViS4vPWP8P~16vSS4weS4xQ4wQ4a16VQS4aeS4yQ4aP{PKQ4i&3=:S4z7R6R~!w8%%DiR}P?P=PY1Et}S4{9:YtRDPYQ4{00dzH0HEp!vV311i6P6106iS4|Q4|1065S4}H0I!vA&P3PvPVP8O3b2bQbLK1xQ4v9>OVS4~Q4v=>OWS50!#<H$4~Q50!uR&~Q50POPVQ4vP6Q!uC&!u8+3]PpPD!t\0Q3e,13!#EW$VO1!t=%S51I1w!sn&/JVRD$0MS52!#8p'53Z2i|S54,8|S55Q05P|Q54!tS%53P|Q4M!tN1Q4KQ5257BS5421W9DS56,6iPB!}w$BQ03Q4b%Q6Q4`'6A7B6323<6343;XUBX6BQ4KPi%AiQ52Q56!}M$^PDPD%ADI24!|l'D%^DS4^Q56/6D!|o$DQ56#C40<Q56P:Q4eQ4E$02S56!|l%bQ!|g'S03!xS$Q4z7R5!s+$6S57!|h,;S58PYQ0I#zRD/E}00lDS0I-0Gt!|n&Q0IPLQ4l!|e%P=PY20G}tI0f!|H4!|E$Q4|/J6S0I,63,25Q0I$0D<0<816i6!|<'!|9&Q4rQ4^PVP6P5O5b2c2zbBH1{bQbLQ54PBQ52POPV20S38PTCcZ05BP6Q4KP3Es!x:%K00S5PTCcP3c0Db7H0tY0DZ08|!#K36!s0%S53bhW9Y25!#KW>Y1hP3O1Q4uPOPW1JyWS4tPHQ1MQ1NQ1Q%5U!s2+Q4f!x1$h+0?S50!wD&52PKP!|d&Q1c#DS54%DXRU;|tP=PYQ4o!vo%dLzI0fI03!vr3Q1c?<X3Q4pQ4q#!#3u'P3PSPQP6p+022S4^O4b2Y0QWAW9p+01mS0IJ1SQ2o#m#h#hS2o#3#h#h$0T!s%$7S59/1jQ2o#;!s>12o,1j1ijkS5:#C&36[S5;,1jQ5;10jk'I3NS5;40:S5<Q1k#mS5=#`!t5$`!sn&7&18jS5>Q5>Q5=!tN$!sJ$!sD&H0IS5>&35[&32[CeQ5<Q5>'2S5<!s2$3HQ3JQ3KQ3L20]jk%5jQ3EQ5:#5[[P5Q3YO1Q3IQ52!{A$&00;S3E!{B$87R6S4i!w7%PYQ59#DQ0T#zS0TQ0TQ2o#D5:YI0;Q4m5W!{h$G5W!{<$Q0T9:YnP=PYPz20lnz%DRS4m>0z:MS5:Cx!#8z8<!{^'59P8P8Q2oH0I@0:;E118;S2oQ4qQ4q,J;;<Z!#8}-<!{m,5>Q5;PjPy!xD$EfSS5;O8b2b[b=c0]b[c0s!uf%!u_&5!uh$!#;n$j!ue%A|?D!yk$PYPnPDP=1E?nS5>-0ltS599:YLEp!yx6!u:%A<683Q2o108;S5<,J5#5!t{1P3Q1K!tn$yfIS2op+01kO6b2K31Q4t,0WS4t9>OW!#7H34kPp!uY$9'E9UYt!tP6Q4}Q4},J361|3!tD+!#9$%y!#9$&Q4t,6yQ4tA>OW!#;o%y!#;o&WyP7POPWQ4vPyP3Q4F$02S4F!}P%+0?S4t+0?22~:iQ4h62}:S59Q4H!sM$HQ4eQ4G!s2$G60v:Q5640o'q+0~!#@0$Q3E&00!y~-3EPpPYB0\Y?}S5!#;u&DS5@=!y^'YQ0T-0C}S5A-0GD!wd&?PD!~[-Q4{9:YzS5BQ4{=:YnJ1G!wo$!z,<C:1I6iS5CA<6;81PiF,6E11;F11fE10EF10EiS5DQ5DPGH0I[[[!z62C!x<$XQ1K!z1&;fLS5DQ0Ip+01nS5EQ4^O:b2!#=:'WS4^!#=:$yS5F!#=:%^Q5F!#=:%^Q5F!wF$V!wH%0P6P{!#5S&Q!v<%!ug&PYPtPzQ5BI0;!uZ5Q5CQ4pP5!|D%105iS5B!u;$!#5P/Ip+027O4b2L2zQ4~!#>^&3Q51I1wQ55Q53bhc26W9Y24!#\f@Mb7c0MY1NP3O1!sK-!#8}$!s'$c2lc0Nb7c0Nc0OW9Y1YY0OWAW9P6PPQ24O2L2yW9Y0|Y0RW}W|WZWM!sF$3N<1sc1|Q4N!#?:$4M!#V1$4LP7g05FGS1HQ0pPhQ0qQ0rQ0vQ0wQ11Q12Q13Q14Q15Q16Q17Q18Q19Q1:Q1?Q1!#Qa$DjS4Mp,2loS4NPuP`PVPvPcJ2xQ!s6&lp,2LARWI1r40JS4;Q4NPVPvp+01oS4<Q5EP`Q0=Q1C$0=#`#{#ZPuQ0mQ0nQ2n$1QQ0p-0[MQ0v-0[M!sB$p,2CHS2nI2wJ2vS1CPc!tI%p,1kS5Ep,1lS4=!$+g%4>PWp,2tqS4?$2KS4@Q3dQ3hPlfiS3QfhS4BffS4DP3N>1qP6NO1KXkN,8NWmQ07Q1GP[!vB0sQ0tQ0u!vK&0xQ0yQ0zQ0{Q0|Q0}Q0~Q10!vcC;Q1<Q1=Q1>!vo'Q4NPc&2u_Q0lp,3CTXS1>P`!v'+Q2}PVPvQ0IQ4sP6Q0^Q0_Q0=Q2QQ5EQ4>PWQ4@p,2LOS2Q!{i,PYQ1s$07S1s#D=|t?P=Q1r#3!$1O$4s-0Lt=:Y?!#>A7s=<36Q4s=<65!{m,uQ4Np,2HIO3b2Q32#Cp,3SPA+1<Q1u9<uX!s6$T+1<Q2f$13$13#`S2f#;#{#`#ZS32Q0r-0[MS4s'1Q4sQ1O7<kPNQ0kQ3220[M3S4s!s?+3HZ0rNQ2e!#sc$;#b!sy$#m#b#m!u=$Q32P3103kS1sQ1cH0IX::!#8S$z!u}&32#DQ4s#DS0IPYQ0I%DkS2nQ54CxI0;!ut,Q32Q!tK&c!tK$P3b2Q4s-1^M!zL$4s!#>j-P6!#j+$1=Q3I!tA0PLQ0IQ0IQ5:60\Y!t314s#5Q4s;GZP3b2bHb~bH+2sI0BQ32Q0k!v=&!uz-eQ0rp,2TPS32Es405Q2f#3$0k#ZS2fQ0lQ0l/0iQ1OQ1>=~[mS4sQ1>/0mS0I/1jS1<B1f[`kS1;10`kS10/1jS0~1o`XS0}'2S0|'2S0{'2S0z'2S0y3H3HS0xQ1n!$$r%2C/ooS0u!#}b$5~[S0t!s2%;<jS0s1o]oS1GB1f[]oS07Q3x/1jS3x1ogiS4QA~[gmS4RQ1fPaQ2>!sb%!s1$P]Po!s/%gPm!s>&]Po!s0&gPm&2o\S4Ug03EiS4V5~[!#YO$;<j!sr%!s4$!sV%!s2%!sf$!s0%gPm!sF'GQ2IQ2J/oo!$#=$5~[!s/%'01PRoQ2K!s5%!to&J!s7$!s{$!s=%!tc$!s0$!tw$!sF$!t%$ClDV!s$%3H7Hj3N[_07!t>$!s%%H7?6S2HQ2H&1I8!$$x$5'[&1I;&1L;Q2I&1L8Cl[[[_2r_07!v1$gPm!$,$$'2DV3N!t1+!s0+DV!s{$fQ1b!~7%`#{#b#ZS1b'1S2IQ1b!{1$iS1cQ0y'2S2K'2!xB,0uQ0tQ0sQ1GQ!wx$!#]L%1fQ2H!vJ$K!{>+Q2f#DQ1b#DS1b5:Y!{8-2I!|7$!t2$!{n-Q1bP}!|t$!sR-1c!|c&Q0zP5Q1<Q0{P6Q1;Q0|PEQ0~Q0}P;21;]X%CXS0}#gS0~P]PX20R]XS0|1i]XS1;H0E[21:]X%^XS0{Q1;#5Q1;;GX[219]X1IX9S1<Q1;,IXQ1;$0D'2[214]XQ0}Q0|#C[215!s4%1;/6][Q0|P:Q1;P:21;]k%CkS1;#gP]Pk20R]kS0|Q1]!tG'k%^kS0zQ3FQ1];Gk!tE$k1Ik9Q1],IkQ1]!tB,k!uX%!tB&!s4$1]!tB-]P:PEQ!#w+$k'SQ0zeO1Q2t?G3kP@!s?&X'SQ0{eS0zO1%5HS1]?GHXQ4eQ4H!#T6$HQ!#EU$4b+0?40oQ4I$02!sH$F!sH%eQ4t40oQ50$2n+0~!#ED%S4tPKQ!#E7$PYQ2n=UYL-0s!#Ko$2nQ0T+0C>16n?I0f!#B3$A:YLtS4IPY20btUH0H!s>&UYU!sb$S4b!#P{$CUD>16nt!sa+20G?LP=AUYtLS0|I03S3FCL!#EW=Q1;g03H>S4s[P8PkPEP5H0E[Q0P?G6!x3$4s[S1;PEPXPFP8H0E[%C;S1cQ1c[S54!#Ei6P;P0P]P8PCPIP6Q0@Q0GO9b2bBbWc0qbnc0Cc0Bc0AbWc0@c0pc06c0?bxc0>bBb7FTFTFTW9Y2qY2pY0RY2oY2nY2m!#Bp-p,2PLN@1oQ0xe+1<Q10Q2}Q2}Q1i'0S1i/0kS0xP`C=Q0IQ2}Q0xQ1>Q0IP`Q10Q1>C=DaQ1A#;S1A#@S0u-10RS0tQ36Q0u#5Q0u-0xRS0s#^[S1G[S07Q39Q0u>0}R!$#Y$0u!s8$s!$$p&xQ1=Q1G!#MH'!#Qy$%DmS4Q,EnS4R00d?Q4mQ1A$0r60z:S1A,E?Q2n'ES2H=:YnH08S1b!y<&,EtS0y=:Y?S2IQ!sG$t5dYS2!y0&PYQ!s{$tQ!sL$!sc$0y!sc%HQ1bQ0y5WYJ1G!xw8P5PmP6Q0s,06?<k5S0yCrA<6k5S1bQ0s>0h5k;y6P;PmP5105kS2H/1;Cr108kS4RP;!sc$;S2f/0kS2KP810EmS4VP;Q2KPEQ4VP8Q4RPE!$;5$!yI/P3PgPaP]p+01QS4Rp+01!s'$VO6b2b=b>b=!$=\&g3Ne405Q10PrQ28P`C=S4VQ10PsQ2;!s5$2KQ0x!sD$Q2}C=S4UQ0x!sE$!s6%0xQ0I!sF%1>C=S2JQ0I!sF%!s6%DQ2MQ2O'2S2C'2S2>'2S4['2S4u'2S4^'2S5FQ4VQ5FQ0tQ07Q0uQ!xb/!#M@%2IPYP?Q1m#D-0CUS5FPtCxS4V5dYS53P=Q53CL!#DQ5/16S1sQ27,06S53/13S55'BQ1bQ27=<56S51'B!#Dl+r!vZ%FS4~O3!vP,[!vA%]C=eQ2KQ4^!t|G29!t|$}S29!t|%^!y}$KP=Q2K!t|8Q2:,06S2K!tv$C!tv&:!tv$4o!tv/s!tv%ES5?!tv1!x&$!tv$4UQ4u!tv?PYPtQ1A!|7$P?CxS4uQ!vp$!{R$1A,EtQ2n!s@%U!s@%!u+60s/0k=<36S5GQ!vz$0yQ!vs2Q2zp+01DS5H!t|/o!vt%aC=eQ0xQ4[!vt@4uQ!v`$P=!uQ$^!t]95GQ!vW$0yQ!vP2!tS&CS0y!tS1!vQ$!tS$2JQ2>!vQD4Q!v2%Q!v2%S4VP=Q4V!t[5A<3m6S4V!v5$A<6m5Rm!v93Pgp+01BS51!tc/e!v8%g!tc$DQ2C!v8AQ!v,%S4QP=Q4Q!v564V!v5%4o,Bm!y]/!tM$A!tJ1!v/$!tJ%MQ2OfxS1efvCe!#9>$!#3:$1JVXS4oQ4v!#8_&!s3$Q1>Q28!s2%PrQ2;!s1&!$Hi%Q0y405Q0mQ1v5HkQ1xQ3<Q3>Q3?Q3@Q1=Q3=!w4/A:YL?S1vPY20b?tH0HS0I!#7M'2nPtQ4mQ1t!#8H%9:YtI0;RmP=Q0I9WYm!#Y@50P?G63PkP6P6Q1uH0I11k5Q1u,15%58S1u?G8540:!#YR+!$NA$p+01OS!#[S$PS1tO4b2bNbIbN405p,3DLOp,4DCAPp,3FCHp,3Ha022;viRm9~[VQ1P10VmS4V1oVX7Hj7HV!#jI+!s+&TQ1V'2S1P'2Rm'2!sF/PmP[PQQ1K!s'%6Q3AQ3C!#rM'A:Yt!#a|0113!#rN%QO1S5Cb2b>!s[,P~!sZ$zz!vA31036!{E$Q'1!uy+1KPQO2S4^b2b>L2l!ta$P!st1PY1EtUS1P=:Y?RmP=Pm!zJ63g/16A<6X!#Td,QQ1OP5!zE$>!uz%!uS-!#>6$A:Yzn!s{;X8:Q4Q/15Q4}/18!#;X/j!u2$p+01`!wy$!uy&Q03!vW&PYQ0|P=Q0|!t#2%C3S03Q4r[!vd$Q1Up+01_S1OO2b2b>CeFTY0QY2X!#mw$\S1MJ1S405Q35Q38Q3:Q3;!{=$7!wm+PYQ4n=:YtS1N!#EP$uY8S1QQ4mQ0K!{0&:0\YtRm5WYP=Q1N=!{16;111f3S0KQ2j9G56Q4pQ2j7G!#ho%;1P3Q0^,1SS4pPSp+01aS2Cp,3QSZS2D!v%$Ic0Sb!{7$fp+01e!u,0!#VD,!u9$IP;!#m|%!uC01l$0`S1l#3$07Rm#DS3Y9:YtS55Q1Q!#m]%!}f$!$X~$l#DS2>-0bLQ2>!#V{%H2kPYQ55PYQ3YQ5:+0b!$$V&LQ1`#;$0=!s%,13#`#@S1`!t:$!sX%!#Wi%!#Bx$!vG3AH3m6Q1l#^Q1l/IZ116m1ImZQ1`#5Q1`;GZ40:40:!vX,2j,ISPSQ2D!zS$I!#XQ$!vM$Q0=,I9Q0=/IZQ4pQ0^/IZQ0_Q0_/IZ5H9!sr%eQ4B!$X_$Q23H2jQ0bQ4C60J<S0_$0aQ1a!$]@&Rm'1PBQ0_-06<Q4`/1mZ05BP3Q0b-06<S4`Q4C!s0$1a+1XS1`!st&2p<J0KQ1`#QS4C/1mS0b!sA$`#QS0bQ1a#QS3Y'0S55/1mS2J!${M$2Q4cQ021163S02!$/h'Q4CQ4cQ55O1!$/g&dQ1`Q55Q4!tA$0b#AQ1aQ!w=$#AJ2iJ20PmPm%AmN<1UP3H2qQ2JQ1a$11Q3Y#5Q4`$11Q0b#5!yi5!#qu$!#|i$Q4IP=!~F$L!#m&%Q5@%Dm!#jC$I!|F$,EtS5@!y8+Ep!#8/52t%55Q4q/1mQ1u108f;GZ[!#7t,3YQ0b!$r6$O5b2c0\bNc0\c0fbgc0wbwQ20Q0c/0f;GZebwPNQ0kP3Q0lQ1>P`Q2}!#d#$POL2QZ0rNp+01^S0nQ0rQ32Esp,2MIp,2STp+01cp,4FLG4p,3IAXp,3DEPp+01gP3p+01dp+01bQ3QQ2C!#f}'gS2CQ4DfeS32fdS0mQ2}$0e!$]Q$Q2}Q1m'o7Hj!$`&''2Q4R!$`5&tQ0IFT405fZS0IQ0:Q2xQ0:Q0:P!{B$\Q2]'1RoQ2\#C!$Db0WKQ0FQ0;fUS2]J0KPoQ2a-06:Ro$11%QoRo#5Q4GQ4g!#sF$!$3q&!#?r%1v!wu%m9:YtR!x&$AUYt?S!s?&0|!#T_$!#5''!#=87116R1658S2a%C8Q4s[11f;S2x@1Z;R[!x;-PoQ2\P6P5f]S1tp,3HITS4RO6b2bgQ!$XP&Rec0<fXS2rfTS2\&0el&0qlS1mQ10PlQ1mP`C=7Hj!#BF4Q4FQ50'qRo!ul$f!$$[$'qRmB0_mo{40_PKQ!#ye&!#W=$|ntQ1k#@Rm#DS1k,EtRo=:YnS4jH08S1G!#H0'DS1A9:Y!#r`&DP!#zJ%!#Hf$;|?!{o'=#m!#~h&S5=#DS1APDP=Q1A=:YtS2nA:Yo!#S6$G5WY5WYEpI03!|/7!#WU$Q2HP3103mS2HP5C=106mS1GQ2f'111E5Q0s,0F?<k;Q5=/1GQ5=10EmS0sPGPkPEQ0s/1GCr7HF7HE!#vK3P3Q2zP]PjQ2l:1ab^RbQ0HfPS2lfQS2fp+01!|+$UO9!#A}&&0eb&0qbS0u/1jQ1[PbQ0uP]C=!#Qa&m!#D}%lC=Q3yQ1mPrQ3{Q1m;ysH1p!wh$FQ4f40oS4GQ59Q4X$02S4XQ4K$02RkQ4H!zv%!#ze&S4HQ!s%,XQ4W$02Q4J$02!sO%80ok'qRkB0_kk{80_k40_!xd$&00H&0007R;&00F7R5&00IQ4z7RE&00C!s0$G!#{^$!y5&UQ0X#zS0X!xF&0W#zRkQ1@#zS1@5!x^+1r#zS1rQ0X'E00G!s='0J#zS0JQ1r!#<C'0J-0doQ1@=:YtH08!s?+29=|DtA:YoD!z3$@!s@+5F!z`$!zK%4j!zK%_#z-0C}9UYk!t;'TP!s1'4nQ0T!#^T&l?US1_-0doPYP?P}PtCxH08S0JQ4jQ1@!z='EpFKFK!zE$!zH$!#^u;Z0`:Z0a:Z0b:Z0c:Z0^:Z0_:11XCA<5FIB0102811C2P;PmP0112;CrPHQ2:!zG&H!s5%7PFA<FmHCr1Pi@,62112@11f@10CmRo1J0XA<0iCQ27=<2CPoP2P@Q2:PC11o@CrH1pH2r[!s#+!#_r1`0`:`0a:`0b:`0c:`0^:`0_:P3Q46Q42PyQ3~!$#$%SPsPrPQPb!%+i$P2Q0?Q0@Q0Ap+01YS3~p+01ZQ0nOEb2Q0u!$o'%bQ28!{^%rQ2;!s0%!#MT%!{j$5E#CS0n#gS42%n<RyQ4=&0i<Ro37S46P6PyPo&0a3S0s#CXEyQ4_Q4=P3EsQ0neO1Y0=Q46#gS4jeQ4jPOPdQ0N#]S0NQ0g$1mS1@#\!s1$MS1r!%$d&XP7POQ3T,0dRkQ0g$2fS0W$1EH1dS4HQ1r,Pi,0k&0qdRk5>OS4XQ0gQ0_5?<S0_Q1rQ0W!$hq%0gPfQ1rQ1rg03@gS1rH0IS56Q0c,1fS4J&0edS4W11kjS4F1odXS4fQ1[/1dS1[?yk]S3{!vP%/1dS2661JkS3yQ28/1dS07?ykrS0tQ2;!sY$i?yksS0lQ2kQ2kg03CC'0Q0<Q1@!#i7$ZX6:S0kQ0W61\:Q0d#C+043H5Hk7HdS2kQ0N/fTS1@99OWS0d10WXS0WQ!v@$S0b59OS3Y'2S1u&0eW&0qWRZ/1jQ10PWPZP`Q1m!s/$lPZ!#4t%WQ28!s9$!xX$WPZ!$tp+Da3NS2;'2S28Q0X!#4J%0_Q0gQ56Q4JQ4W!#je%3{Q3yQ0tQ!uT%4?p,2NNS4vQ0?42eQ1rQ4?$1VQ0f+0p$1M'1!$Z>,fWS!sX$lbRZP2!s?'ZP^PeP2Q3OQ3}N92{N92|&1HZS3}$0qPlQ3nQ3}C=Q1@&1mZ#kS3n&1MZS10/XTS5:'fS5760J4!vM$4`Q0dQ1@$1D#Q,0WRZQ5759OS1a'2S2J[Q2JQ4`[!$3r%1@Q57I1cQ0@H1bQ2JQ01!sg$aQ28P3!s1&3n/fTS3nQ5:!t7&ZS2JQ3n!s0$57Q3n!t>&ZQ5:!t<$@'2R4[Q2J\4!t9$ZQ!se$I1cP3H1bP4Q01Q57!y+$8P3!s1%!#R<+A:Yt?S5:P=PYQ58A:Y?tS3n!#Nd%v!#<Y5;111361156S1v,28Q2a!#3\';1P3Q10,1fQ10Q1rP2Q0FO5b2!|$$057:P:Q10Q4K#QR4>0hW4R4Q4P59OX::P6Q1r!~4%b99O4Q1uQ2;Q0dQ3YPHQ3}#AQ3},6WS3}eS3YQ3}!#Nt'Q4{/E}Q1P5UY!$IY2Q3g801i!#V5$WO1b2c0gB0hWiiR4Q0W'6P4!tA%!$8y$Q0WP3D}b7CeQ5=/1d10dmR4/1jRZQ1[?y4]S1[PbPmPd114bCr!|D$JQ!}j$4S26Q07?y4rS07Q1i?y4sS1i'2S0b'2S3g'2S3e'2R4'2!#Q+-2nP=Q2n!#T_1!tP$3!s+$6!#Tb$PdQ0FO2b2PZP4!x8,Q3xP=Q3x!#WE52H/16S2nQ1G/15R4!#EA+jPdQ0EO3b2Q1[Q3e!#ho5kPtCxRj5dYRZP=PZ!#fe81G/13RZ'BQ1bA<5m6Rm!#aK-dP]Q0C!t6$0WQ3g!u,09dYj!u1$=dYj!u57n,BZ1B4m!sv/bP@!su$26Q0b!su-0JP=Q0J!u|81J6XS2HQ4|P3C=Q1G1J5XS1GQ5BP6C=!t,,QPdQ0B!t}%7Q1i!#d]/!#?T$t?PjH08R4P=P4!t<5P3Q27P6PZCrQ53@1J5!u40rQ0AO3b2!t#229!t#,jP=Pj!t#9:!t#&2K!t#4sQ0!v6$!#c_$!#6Q%3{Q0uPdPkPb!#E<$0tQ0l3NI0XeCec0Fb7Y0FW9!$;C<c0EY0EY1f!sI?GQ28ebwc1@W9Y1cY1bY1eY1dWZY1`Y1_WMY0zY0}Y1XWAW9Y0G!%0+&PcQ23Q24Q25P3N92dRkNB2cc0HY1oQ0nQ4=PyQ04P<Q0sP:Q0f-0p6P<&1H3RdP:!$:_'P3I1rRsQ4M#nRmQ4Mp,2Wh<0J3RZPmQ1cA7yFoRj%gj'B]Xbzb{byc04c03P3&0ao!t''oP<PdP:PsPmP!s`+o!s`%1Syo42EW!se0AO<63$0aP:AO<56!#:9$!sk5O<GF=7yoRm%gmRZPyAO<HG!uQ$P1P3Q4sPxn1011!v~$2!#Qy%000Xhyg05EkS04PoP3J0K!$5J$01P3bBX7mPZe42D!tc1Z0lyZ06<!w|&!s~1106101P6O1c0lQ46Q4j!$[u%6Q4j%CWR<P3Q46PyPo!v3%3$1H!#B_1P<eY0=!$R\$j!#=mO'2!z?$RyQ4s!s_8!#_x/N!#Sq%P=Q1Q!#an4Q0KQ4rP8!#a_,4sQ0cP5P2O4b2X9yY1[!$BL/kN;2b-1P<Y0H!$CU30!$CU'12WXQ0H%A]16`]R]eS0nP]!tj+Q3a/E}Q3V#;#ZR<-0Lt!#9x4c103<!#9y+`O1Rkb2bPQ3f10`<R<'6Q3fPOP3Q0<!%Ej$X::fRS0<P<!#:%$Q!tD5UQ3U#;#{!tFEX^0:P!t@$RyQ3j!tB'RoQ3jQ3i:0Q!$y>$2f!t='!xb$3jQ3k,03Q0S#3#b$0`!%K?$o,0`Ry!$zK&!tf2Q3_!$~_$o!t^6Q2[103o401!t`+Q3m/6yQ3mQ3l=>!tV+y!tV&!uu:^Q2h+0LQ0i!up9bQ2hQ0i,03!t:02gQ2h60h`Rk!sD$`S0i'6Pk!wA$3Q#]Q4BQ2CQ4D<0>TI0AX::f`S!sr$!tW&1OfNRkp#1c34Q1HQ!$H`[Q!$H,-20RoQ4<!$H+&!$GI&!$DX,!#_-'jS1O!#_A$!$G%$RZ!$G'0P3O1PN!tcdP!t^2ZP5!t4&&0g6!%:+'!s$7|%nNRZQ2S$1k\NR!%Hq$C!t]+!tH1!t:$`Q0@Q0?Q0>P@P2P0PCPIPHPG!%Y?&NI0UQ1?Q2e#3#b#b#h#b#b$1Q-1^MRMQ1DQ1EP3Q!%JU$2e37S4<PhQ0p!us8!x]$!wE0AS2gp+02@P`!ue%5P6NF0ORm!wO={S3bfzS3^Q1eQ0AP3N?2a3NXSoXTZXR|Z2yNZ2xNZ2wNZ2vNZ2_NZ2^NZ2]NZ2\NZ2[NZ2ZNZ2YNZ2uNZ2tNZ2sN&0g5Q4<PmQ0a!za$aQ5E/0fQ0:P:Q5E02`9PlQ4!$tp00%klRmQ4@&0qvRs'0#k;vT'X'XS4@593Q421fmTRm996W[Q0N%ksQ0M,0VS0M/XT,Xf3vRs993lQ2i,0lRdQ1m5>3Q3d/JfRj!%?,'r993JQ3u!%-l%R4:0Q3<Q2c/Pj,0<Rj=>3yP3Q0iQ3b#]Q3^Q0AQ1e!|a&Q0C$0gQ4<Q1H!y&BA!y,@!y'&P!xm'6!xm%!s}&!xh<5!xh1Cp+02BS1e!xh';P8NF0OQ0aQ4@598Q42A9EWm[A9ElsQ1m9>FdA9GJrB0QH<4A>IjyPCQ0iQ4~#]Q5?#]S4~fKS!ut$0y01?T3vCc&0gI!#Y}'Wm!ts@6!ts,Q1eQ2g!tl'8P5!tl/5!tl$;!tl$;!tl&EdA9F!tl$G<4A>HjyPI!tl%Q5HfJRjQ51!wR'4;@3:OCS51B237OC21z7CQ4NQ0S$0j,0uRy5>CPhQ15PVP`H2_S0S99CyQ3W!sG&4104XS3WQ1C-06:R<#QRr/XT'XS5H59CP7PCQ3WP:PNQ00Q1CH1=S00>0JN0H1d206N0Q4Z02^<S4Z57BQ1B!t%%S1B21?hTS4~59CPCQ0L!s?&0L!$l=$2!vO$3!v[$1Q0w!vm$p01?T40>!s%%S0iCcPCQ0MQ4O$09S1mp+02K$09Q0O%\v$0^RJp+02J!|@$3vCcQ1C$3@Rd-2]cS42/XTRs99CVQ0U,0`RmQ0Y,0`RW5>CQ0\99CWP7PCg017eS0Y&09fQ0[Q0O/fT3vS0[H0w&27CB2\cdrRd>0y7!v5%2XQ2SQ4S$1RQ2T!%FC$RrH17Q0kQ1C61\:S0kQ4E01i<Q4Y-1i<'2S4Y!|G@PjQ2oQ0HQ0GQ0FQ0EQ0DQ0CQ0B!|a1!|O3C!|O%$0gQ!x~&021z72Q4N=>@yQ0>Q0S79yQ0?Q5H794P7Q0@Q3WQ00Q0A60JNH1dQ0B-06NQ!x:%0BQ1BQ4~39!tP$LQ4KQ0E+0SQ0iCc!tg$MQ!wY%U!wY%p+02TS1m#k=vJ!wU%0E?9VsQ0F?>mW!uL$\79WP7!uZ$YQ!w#$Q2o$27B0y7djP7Q3bQ2XP!vi'4YP:!#3uBfqfpS2XfoS0[fnS0YfmS0\flS0OfkS0MQ!#<e$!#>_&Q32Q0m!va2faS0i!vd%Q2e!~@@3p,1WS4K!~D'!wc$P`p,1TRr!#9w+p,2s'RdQ0eQ0ep,2LBRW-2[VRmP3I1Yp,2d'Rs>0y73g05GNRJg05HYS0L#nRT22>JT$1kS4~21h_VS1B!uc$5P6P3I1]&2MdS4Z-1A5g05IdRB#nR4&1@6&0iBRB37'2C_Z2aTS00,8TXiT'8XoJ'8Ry3NR<'2C_XSo,8oXTZ,8ZXR|,8|XvN,8NXu!s+$t!s+$s!s+$e!s+$d!s+$c!s+$b!s+$a!s+$`!s+$_!s+$r!s+$q!s+$p!s+$!%4y&p+02_S3W!x?EQ2X!}=$YQ0\Q0OQ!x1:fcS2X!x62Q2h!x4JQ!x0+p+031!x2$P!x--/2<!vA~!vA3p+02^S2h!#B}@PZPo!v[D!vXFQ2Xfb!{h3_!vWX0p+02o!vY9!#B+$XvNXuNXtNXsNXeNXdNXcNXbNXaNX`NX_NXrNXqNXpNf^S2eQ1tf\S2Xf[S0mQ0IfYS32Q2rQ4?fVR<Q2]Q2\Q5;Q0<Q2fQ2lfOS4DPk!ykEeQ1t!yq$mQ0IQ!s{'P!sy3!v62Pk!#Es&CQ2C37S4B!v>@k!v>,Q3WQ2h!v:%Q2lQ4DNF0!t|$!~u&PmPkI1YB0y7sk;NyS2h'2!u?D1l!uBMJ2@!uB6'SQ4BeQ4DQ2hQ5D&2Z_RkP_Q2{#Ag06S3#n&2Y_'SQ0:Q3t'Sg05aH#n&3P_'S&2W_#AQ2G#n&1t_'S&3RA&3S_!sN$`=RM&1u!sN$<_,SM&1y_#A&22_#A&1v_S2G#AQ3sN?2V&3VkPkPPP3Q24Q4TPeQ3uQ3vL3W!s=$eQ3uH2US3t!vO%43X!vZ,Q2lI1YQ2l:0y7sS2{/2yP[!sF'Q2lI3Y22>::Rs02TmR7A?s3m&2SdS0e9?s3+0PRd^KsRk'!%fm%Q2lPc!#]&$PQ4\!tN$&4c\&4b\&4a\p+02ap+02`Q42Q1Mp+01[Q0iQ3~!#^F%4Tp,3UHIS3~Q25Q2QQ3vQ4]Q4;!t+$Q0EH4_Q0Dp+02Z!#G?/;fMQ5DQ3b!#>D0P3N`4^P7Pk22TsWRkA?s3W&2S\R7!u;&^KsRjQ4:12kjp,2HRS5D44]44\:4[VWQ4:PkPjPdQ4:A?s8mA?s8WRd&0W8/[VS2l'2+0PA?s;mA?s;WRm&0W;/[VRu'2RcP3Q!vN$;RMPM22P1MR<J1`WlB4XVW8A?s87S4;-0PdPcA?s;7R7/2uPmP7P3PuPuP1Q08!%~=$K664V1PuH4UR7J2FPMPMP!st%P3P8O1PAPs%j3S4]&0N3+0YR<Z0eARMQ09>0|AwRmH1=Rc9?s8PMP3O1Rd=7s;RW1F3mR`'2X6A#M!uF&cRc/2uA7sdES2Q/2`!sC$Rd/2uPcPd!tm&!tW$APsPMQ09P\PPp,3tq'S0ip,6cache'S1MH4R$2?R760|ARd!tS';RhPh22P1h!u;%!sm$PmP8I2LA?s8c1F3dRc,2W!tf'!v+/f64Q1A7s<ERW!tl'S08/2uS42PhQ2Q/2c!s<$P3K4P!t-+d!t-%7s<;RM!s_'Q2l'2S2Q12WcX6AS4\#M[12M!sg%S4NQ42[Q2QQ01Q08PuA7s<F!t<$!t1'PsP<PGP`C_!sw%05!t>$<PH!s:&&0WH/[VA7s<CRu!s_'[P312u`Q01%j6S05&0N6+0Y=7s01F6m&0W2/[VPsP<Q0>Pc!t+&[P3%j8&0N8!sR%@1F;mQ0?$0W/[Vg05LXp4p710RuQ0:\3RM%n5RhQ01B0|8539?86A?;56P8P5O1$0m'2S2h[S4DA?863P5P6!s=&B0|;869?;5S4B[S1FQ4BA?E85P;P8!sJ&[!&,j&H4OS4BP6!#jI/!s-%0WEX66WjWVS1EQ4D^Eh^66^jM^VuS1DP3PAQ09PGPwP5O51FGw%uGS1?'2Q011FHw%uH!u}%D!u}+P31FCwS2f%u0!w4%Q0G!sD&P2%j2S0G&0N2+0YQ0F57s1F2dPHQ01Q4DQ1FQ2hB0|E;59?E8[Q4BP3!u07XEhX66XjMXVuS4BQ1F!u31F!u3'@P71F@7%u@P[P\PPPOQ0iQ1M!#56$P@P520Z@PRuPAPPQ2o97s<1F6wRM%u5Q4s]F]@]DX6A20YQSRhQ0H!u'$Pw%uPP0PsPh20n3VRhXKs%AVQ3bP5J0KO1WFW@WDQ0>P3PCP8P5N94NW7%gueN;4MP6CeO5b7CeH0tWFW@!%'x=@b7Y0IW@WD!sK=W7X6A!%>?<!%bh>W7Q4NPAQ4\Q42PWPcQ08!}<'20nEV+041F6dQ1EQ!y,,8P7P6O51F87%u8!y&&;7%u;!|r$0!}-+20nCV+04P31FF7Q1?!sP$37&4LPRd-0Z6Q05/[Q80<M[RM20Z3dQ4AQ4]/[Q40<1F67R7[20Z5d1F5w%j5!s?%\7!xB83N94K!{W9XUAPM^UAP3PIP5O220ZId1FIw%jI!sz%Q0620ZCdQ2f%jC/6Q+04!{+%A!#3O,@00n!uI%20Z0dPAPdQ0B97s<%u6!sU%E!sU-D!sU&RC]F!yc$%jd&0Nd!{k$A57s%udQ0:g05M4!$D;,4sPxn01102!$D1'hQ04Q0;!#q-&21PC3b7WFWDP2P3P0P;L4GW7P3O11F0w%j0!u9%!w9$2wQ0G/[Q!to%C!to-B!uF+Q0>/FwQ0?#j!sP+F!sP&R`#MQ0E!#5$$PA!#d\%@#jQ0@$0N+0YR`Q0E57sQ0@/FmQ0?Q!}R$!yI&Q0APwQ0A!t/$A#uP5PI!{k-PsP`%ghXKsP3&0W`/[VeQ0EQ0?J0KCe!{h$!{'?!#pK<b@!vB$!|qBW@XDWH4FX6AP3I2IY2kCeO2O2Q4;Q2l'2!#>v$8+0P!s=$Z1gjZ1nkW9Q5DJ1SXKsFTQ2{PyPEQ4o/13Rs106fRkQ4V'1RjP[Q1JQ1LP5Q3~!#|`+20ltURA=:Y?RWP=PW!#|[41J3XRW/16Q2H/1!$Z;,8PQ!$Z:$!$q</Q5@Q5>P=Q5@Q1_1EUn'E5:Y!$=~7Q4}9<3fQ1G10X8'0,1k!$ZA-Q1KPQP8P6O4b2K4BY1QW?XJ:&4A5$0m\j\s^J:!$4d,Q3^J4@Q3oQ3pQ2_#^'2Rs!%gc%oPsPyP3Q3oPJPTQ!#Uc$QPQPSP6P3Q0L$0iRjI1]37RkQ3t-1A6R`&1@3=74BRh3NXiTXoJPyPkP`PhPy!sK%5&1@5=74BPJPTPTQ00!sN&;P8PjQ4~Q!#Vn%!s6$!t-$Q4Z-1A;Rj&1@8!t+$B'2P5PjPBP6P3FTL48Y21Y20XDkI47!sw&_PPP_PPQ3sQ24H44Q4TP:Q0^Q2G#C#g9HS3X::P:Q0=Q4pQ03+04X::!%DP%!$\h3Q4gQ!%MR&!x--20Gnt!$Sw%n?R_Q4l!%I&&5:Q2>!$|K&J1G!%F^9;116531185RJ/2;Q1l#CQ4s[9H58!%Z`0!$YG%vPvQ0^PSP;Q2DO6!%2w&bL!u=$==7:9+04eQ1|Q1eEsQ1yp+02DEsQ4O-0xRRv,iQR1Q03X::21;Qv%CvRT#gPQPv20RQvRkP1!%%2%Qv%^vRB%51?G1v[219Qv1Iv91Iv1&0D1!%%'$Qv%Ck\T215Qv161Q\TPkP:P1P!t-$XQ0~PQPX20RQXR1Q1U!t''XQ0{Q3BQ1U!%'S%QXQ1<Q1U,IXQ1U!%&3'QXQ0}%C1[215!s2$Q1U/6Q[P1P:Q1UP:PEQ0z!%%}&X!%%}'v'SPBeO1Q1]?GHvQ4O-10RQ36Q4O#5R9PB[RB[Q39Q4O!$|+'Q39%5v\x]?Q1=PBQ!%%f0!%$w$!%Gb$U!%%\0!$YU%mQ0V!$b_%RU-0bt!%%e4!%%b5Q!%%LDP8PX!%%C0vQ4s\TPEPv!%%>&Q!%%49GQ0>PQPFP@!&Z~$Cp+02hO9b2b[c0]b[!%%>KQ4O$43-45QQ4O!%2R+4O#D9:Y!#5f,P9P3b2646QI0BPEPQ!$k&-A!$k&2W3^0:Q5Cb2Q1J/1Qe!%SJ%!|v%_!w;$4n=:YnRnP=Q5@=:Yz!vN8Q1v11f8Q4q9<5f!$}n0S!$lf%mp+02XRW!$>g$S9<QfeO3PEQ1S/JiREQ4e!$WI$Q59Q4G!%N%-!%Tq&Q5A-!$Pb&!tm$PnP=20lz}R}9:YAFK!%R/;1Pi8,66Q2x1J8XQ5</Ji'1[\J!%R33X!u$&p+02SQ1mPWO7!v@&E!$<$,P}Q4nPz!%6=-!$ta&Q/JiQ4Q7<f!t&%Q4^!ui&E!ui$eQ3uQ4vQ3vQ4RQ!%[[+Q3n!$YV%=:Y?P=B0\YLt!$\V62Q5=/15%^!%[H,Q2zPbP5p+02LO4b2%^beN>41J49X9sY1}!#=v=7c1UFTc2Fc2DFTNT4:H0tH0tQ2C$0geW9W9Y22Y13Y1SY1?Y2@Y2>Y2AY1PY1=Y29Y1iY2<Y1<Y1sY27Y1jY2EY1kPHNG4;Y28Y1rY1qY1pY1mY1lY1aY2;Y1>Q0DP3EsW7N<2H!#a}UND4<XkN!#?y$1uWmJ4=Y0P!%`~@c0PW9Y19Y18Y17WAW9Y16Y15Y14!%}I-I4>N<1sc0yY0vY0u!v_@0xc11c0<W9WY!sO>Yc0:c09c0;c0Lc0Kc0JbYc1;c1:Y1VY0:Y09Y0~Y10Y0{!$4r$Y0;Y1{Y0LY0KY0JWYNA4?!&:52!$kw'P^206:rRr#QR|#Ap,2nT/6|RZePZQ2|#AQ2|,6lRlePlQ3h$1BRl#A16e!s9%p,2pc$1ORl#AQ3d/!sP+YQ3}Q4=$0a!sA$5E!sA+!%Z~,%AaQ2}/6aRaePa%AgQ1>/6gRgePgQ0nP]&11r%5|Q2~Q30Q31Q33Q0y!&9$$Q0y#5Q34Q5?!&8{+!$|T-!$rB/AQ3CQ3DQ3G!$kc/3MQ3NQ3OQ!&66-3TQ3TQ2i'I5HfR|!&5u&Q3ZQ3IQ3[Q37Q3\!$}Y%!%Ka+4nQ3`Q3`Q2i#D!%JI3P|P3!&4:hc0fbgbPc2cc2hbQbLc2fc0gc2dc2ec2bc2gQ3R9Hf^eQ4RK3|L3{Y1~Y23WA!#Ii>!$Cq>!t~@7Y1EY1DY1CY1BY1MY1LY1KY1JY1IY1HY1GY1FY1AQ25N@1oc1tY1^Y1]Y1\Y1ZY1xY1wY1vY2CY2BY2KY2JY2IY2HY2GY2QY2PY2OY2NY2MY2LY2WY2VY2UY2TY2SY2Rp,4PURENM4CY1TY1WY1zY2:Y1yY2?Y2=Y0tY1RY1ON<2H!&Z97!$EI&!#f#'Q3~L3zN:4Do"). Qed.
End FreeNewHitMid.

(* [comment removed for export] *)
Section FreeRefillMid.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st : ltac2:(zQ "10!ip5$0") := ltac2:(zQ "10!hrf@1$0?1s").
  Let TH : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!spa@1$0?1s").
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sq2@1$0?2ch").
  Let size : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sr1@1$0?2ch").
  Let tq : ltac2:(zQ "10!src$0") := ltac2:(zQ "10!ss6@1$0?2st").
  Let l : ltac2:(zQ "20!j4!ssf@1$0$1") := ltac2:(zQ "10!st9@1$0?2tq").
  Let k := zlen l.
  Let lb : ltac2:(zQ "10!ssf$0") := ltac2:(zQ "50!hl6!h9!su4!ssf!suc@3$4$3?1l@4$2ZZZ@1$0$1").
  Let LA : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sv3@1$0?2lb").
  (* [comment removed for export] *)
  Let c : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!vg5$0").
  Let CA : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!np7@2$0?2TH+t0").
  Let P : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!np7!uua@2$0?2CA@2$1+l0?1c").
  Let RI : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!vs4!np7!uua@2$1@1$0?1s@2$2+o0?1c").
  Let r : ltac2:(zQ "10!vsb$0") := ltac2:(zQ "10!vt5@2$0?2st?1c").
  Let nf : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!vu3@1$0?1r"). Let mfa : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!vv3@1$0?1r"). Let au : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!hggc@1$0?1r"). Let mu : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!hgi2@1$0?1r"). Let fl : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "10!hgj4@1$0?1r").
  Let n : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!hgo5@1$0?1c").
  Let mu' : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!hgoe@4$0?1c?2nf?2au?2mu"). Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!hgp9@5$0?1c?2nf?3mfa?2au?2mu").
  Let au' := rf_au' c nf au mu. Let fl1 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "10!hgq5@5$0?1c?2nf?2au?2mu?2fl").
  Let st2 : ltac2:(zQ "10!ip5$0") := ltac2:(zQ "10!hgv4@2$0?2st?1c").
  Let chunks2 : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!hhg1!h9!hhgb@3$0$1@1$2?1n?3fl1").
  Let cp : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!h9!vid@3$1$0Z?7chunks2").
  Let B : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!vj2@3$0?3st2?1c?2cp").
  (* [comment removed for export] *)
  Let CHI : ltac2:(zQ "30!h9!j4!jb@1$1@2$2$0$0") := ltac2:(zQ "40!ige!npe!tkd!tlb@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "50!ige!tm3!tlb!tq9!npe@6$3+pgsq0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!nv4!h9!rv0@1$2@2$0$1?1T").
  Let d' : ltac2:(zQ "10!tr3$0") := ltac2:(zQ "20!tvd!ugb@3$1?1d@1$0?1T?2nT").
  (* [comment removed for export] *)
  Let L2 : ltac2:(zQ "40!ige!ij1!j4!jb@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b5!hhh5!ige!np7!ij1!hhhc!oje!j4!jb!hhi1!hhj2!hhj9&@2$7@1$3@1$1#k0@1$3@1$1#k0&@1$6~0&\0$0~1&@3$8@1$5?1s@2$2@2$4?1s?1c?2mu@2$2@2$4?1s?1c?3mu'&M0~2@2$9?2mu?3mu'~3@1$5?1sM0~2@2$9?3mfa?4mfa'@3$8~4@2$2@2$a?1s?1c?3mfa@2$2@2$a?1s?1c?4mfa'~4").
  Let S2 : ltac2:(zQ "40!ige!ij1!j4!jb@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "h24!ige!ij1!jb!hhh5!hl6!oj8!mv1!nn2!j4!utb!hhje!np7!hhk3!hhj2!vmf!hhj9!hhhc!ok4&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$8~0&\0$3~1&@1$4~0@3$6~0M3~2@2$d?3mfa?4mfa'@3$7~0@4$9@1$1@1$0#k0@1$1@1$0#k0@1$5@1$a@2$b@2$f?1s?1c?3mfa@1$5@2$c@2$e?4mfa'?3mfa+8~3~3@3$6~0M3~2@2$d?2mu?3mu'@3$7~0@4$9@1$1@1$0#k0@1$1@1$0#k0@1$5@1$a@2$b@2$h0?1s?1c?2mu@1$5@2$c@2$e?3mu'?2mu+8~3~3@1$h1?1s").
  Let AL' : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!unb@1$0?1s").   (* [comment removed for export] *)
  Let sR : ltac2:(zQ "10!o0$0") := ltac2:(zQ "70!pv9!tm3!hhka!hhl2!spa!tlb!hhla@a$6?3st2@1$4?1s@1$2?1s@1$3?1s?2L2?2S2@1$0?1s?3AL'@1$5?1s@1$1?1s").
  Let tq' : ltac2:(zQ "10!src$0") := ltac2:(zQ "20!vk5!um0@4$0?2tq?1B@1$1?2ch?4size").
  Let cache' : ltac2:(zQ "20!j4!uv1@1$0$1") := ltac2:(zQ "80!h9!uo2!vkf!uv1!vl7!vm2!vma!vmf@4$4$3@1$1?3st2@1$5?1c@2$2@2$7?1n+1@2$6$0?7chunks2").
  Let sF : ltac2:(zQ "10!o0$0") := ltac2:(zQ "10!un0@7$0?2sR?2ch?3tq'?6cache'?2L2?2S2?3AL'").
  (* [comment removed for export] *)
  Let Wh : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "30!ige!usc!npe@6$1?2lo@2$2@1$0#k0?2sp?2TH?1U?4size?1d").
  Let WR : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "a0!h9!nn2!utb!jb!ige!np7!npe!hhm2!hhj9!hhhc@3$1@2$3$0$0@4$2$0$0?2lo@2$6@1$4#k0?2sp@3$1@2$3$0$0@4$2$0$0@2$5?2TH+sm0@2$5?2TH+sm1@d$7?2lo@2$6@1$4#k0?2sp?1P?2RI@2$8?1s?1c@2$9?1s?1c?2TH?2CA?2nf?3mfa?2mu?4mfa'?3mu'").
  Let Wn : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "30!ige!vr7!npe@5$1?2lo@2$2@1$0#k0?2sp?2TH?1B?2LA").
  Definition fr_W : ltac2:(zQ "20!j4!mua@1$0$1") := ltac2:(zQ "20!mv1!mua@3$0$1?2WR@3$0$1?2Wh?2Wn").

  Hypothesis HR : ltac2:(zQ "10!hr6@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis CHIN : ltac2:(zQ "30!hhmb!hhn4!v7@3$2$0?2ch@1$1?2st").
  Hypothesis ALLOC : ltac2:(zQ "40!ip0!hho2!hhp0!hhpc@3$0$3@1$2?2ch$1").
  Hypothesis UHI : ltac2:(zQ "60!hhq6!sr1!sq2!hhqd!np7!vmf@3$0?5HCEIL@2$5@1$2?2ch+h0@2$4+h0@2$3@1$1?2ch+8").   (* [comment removed for export] *)
  Hypothesis AX : ltac2:(zQ "30!te!qka!qm3@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!qjf@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!ita!ksd@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!pl6@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!ql6@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!ita!ru5@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!ige!ita!rpb!npe@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!hhr9!hhs1@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!ige!np7!hhs1!npe@2$2@2$1?2lo+ro0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!ip0!ige!h9!hhs7!npe@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!ige!np7!hhs1!hht1!npe@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis TP : ltac2:(zQ "50!ip0!ige!hht8!oj8!ij1@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis DLO : ltac2:(zQ "60!np7!hhs1!uua!te!hhte!hhu6@2$3@2$1@2$0@1$4?1d@2$2+h0+hggg0?2lo@2$1@2$0@1$5?1d@2$2+8+ogg0?2lo").
  Hypothesis DCAP : ltac2:(zQ "60!np7!te!hhue!hhva!hhs1!hig3@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis FCH : ltac2:(zQ "d0!ige!npe!tlb!hhh5!hig9!ip0!hih0!te!ita!tm3!hihd!np7!hhs1>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!ip0!ige!oj8!ij1@3$0@1$3@1$1#k0?2a0@1$2?1U").
  Hypothesis BLK : ltac2:(zQ "70!nma!nn2!hl6!ita!roc!nu8!hhgb@4$5$3?1m?1U@3$1$0@2$4@1$6?4size?2bs@1$2$0").
  Hypothesis SHB : ltac2:(zQ "90!nv4!te!ip0!ige!h9!hiic!hij3!rv0!ij1@2$1@3$5?1m?1U?3sbs@3$2$4@1$7@2$0@1$8@1$3#8?3sbs@1$6?4size").
  (* [comment removed for export] *)
  Hypothesis QSZ : ltac2:(zQ "50!te!hij9!hhs1!hig3!hht1@2$0@2$2?4size$1@2$3?4size@2$4+2+i0").
  Hypothesis NN : ltac2:(zQ "40!hhh5!hig9!ip0!him5@3$2$0@1$3?2tq$1").
  Hypothesis MISS : ltac2:(zQ "40!ip0!h9!uvb!vh4@3$0$1@1$3@2$2?2st?1cZ").
  (* [comment removed for export] *)
  Hypothesis PROOM : ltac2:(zQ "50!hir4!hjg3!hjge!np7!hhs1@2$4@2$3@1$2?2st$0$1").   (* [comment removed for export] *)
  Hypothesis ROOM : ltac2:(zQ "50!hjh9!hjie!np7!hhs1!uua@2$3@2$2?2mu@2$4+2$1$0").
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis OK : ltac2:(zQ "60!or3!ita!oje!ok4!pv9!rk0@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "d0!ige!iv4!ip0!hvd!ita!oje!ok4!qvb!mnc!lk3!lo8!lp3!ij1@3$2$3@3$7@1$5?1s@1$6?1s?3msF@7$9@hf$8?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$b@1$0#k0+pgrm8?2fc@1$1@1$c@1$0#k0?1m@1$a$4").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_refill_gmid : ltac2:(zQ "20!hvd!ni5>4msF'$0>3mo'$1P") := ltac2:(zQ "k11!ige!ij1!te!ij7!nma!nn2!ita!j4!nn9!np7!npe!hl6!h9!ind!ip0!nu8!nv4!ip5!oj8!hvd!oje!ok4!s4!iu3!iv4!mv1!oka!io7!jb!om2!oo0!or3!ni5!jj9!hq0!pge!jo9!pl6!jtc!pq7!ko1!puc!pv9!hrf!qjf!qka!ql6!qm3!ksd!qqe!kt6!ku6!kv7!qvb!rk0!ro2!roc!rp2!rpb!rq2!lk3!ru5!lo8!rv0!lp3&@2$9@2$9@2$a@1$0#k0?2sp-ol0+h0\4msF'$h3\3mo'$i0@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3@1$7@1$1@1$0#8\2jk@1$7@1$1@1$0#8@2$3@1$7@1$1@1$0#k0\4rest@1$7@1$1@1$0#k0@2$3$h6\2m'$h6@2$2@5$j6$6@1$h4?2sF@1$h5?2sF@1$ia?2sF@2$hf^h3^h2@2$2@3$e$h3@3$j5@1$h4?2sF@1$h5?2sF^h3@7$jc@ha$i8?2sp?2gp?2tp?2s7?2s8?2s9?3s10?3s11?1U?4size?2TH$j3^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4?1F@2$k0@1$0#k0+mtlv4?2fc@1$h8@1$1@1$0#k0^1@1$je$6@2$2@5$i2?2sF@1$b$c@1$b$c@2$i1?1U?2LB^1@2$2@2$id?2sF^1@2$2@1$if^1@2$2@3$ic?5HCEIL?2sF^h2@2$2@2$j1?2mo^h2@2$2@4$i7?1s?2sF?2mo^h2@2$2@3$j0$6?2d'^1@2$2@3$i5?5HCEIL?2sF?2d'@2$2@2$ie?2d'^h2@2$2@2$jd$6^1@2$2@4$ja$6^1?2lo@2$9@2$a@1$0#k0?2sp-oq0@2$2@4$f$6^1@2$9@2$a@1$0#k0?2sp-oq0@4$i9?2sp?2s6?1U?2TH@2$2@4$f$6^1@2$9@2$a@1$0#k0?2sp-ol0@3$5$4@1$8@1$h2~0@3$5$4@1$8@1$h2@1$jf@2$h0$c?1T@1$b$4@2$2@4$j7$6^1~0@3$h9@1$1@1$0#k0@4$he$c@1$1@1$0#k0$h2?1T^2@2$2@3$e$ha@2$h0@1$1@1$0#k0^2@2$hdNvf@2$h0$c?1T@2$2@4$f$6^1@2$9@2$a@1$0#k0?2sp-k8@3$5$4@1$8?2sp@1$b$4@2$2@4$f$6^1@2$9@2$a@1$0#k0?2sp-k0@3$5$4@2$j8N8^3@3$5$4@1$8?2s5@3$5$4@1$8?2s4@3$5$4@1$8?2s3@3$5$4@1$8?2s2@3$5$4@1$8?2s1@3$5$4@1$8?2s0@3$5$4@1$8?2ra@1$b$4@2$2@3$j9$i3?1m^1@2$2@3$jb$6?1m^1@2$3$h1\3stX$h1@2$3@1$7$d\3ev0@1$7$d@2$3@1$7$d\3ev2@1$7$d@2$2@3$e@1$hb@2$hc$h1@1$7$d@2$j2?2st?1U@5$i4?1U?4size^3^2^1@2$2@2$i6^3@1$ib?2sF@3$e@1$7$h7@1$j4^2@1$b$h7").

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Let HC : 1 <= c <= 30. Proof. unfold c, kBatchClass. lia. Qed.
  (* [comment removed for export] *)
  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. ndestruct RR as (_ & _ & FL & _).
    ndestruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. ndestruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let RPURE := refill_pure s m c R HC MISS.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PCc := rfd_pc_c st c WFs HC ROOM.

  Theorem free_arep_refill_mid : ltac2:(zQ "70!or3!ita!sj3!sn4!hvd!ni5!so5>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
  Proof.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay that
       destructured amaps_in_ledger at its PRE-RESTATEMENT shape; its first error was As:349 /
       Bs:350 "Illegal application: and_elimF6" over the old six-conjunct body, whose first
       conjunct this series guards by a non-zero ledger-word size (As//Bs AllocRep.v).  Written
       out as plain text; the STATEMENT IS UNCHANGED (still the encoded one above).  Shape from
       a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/
       AG_FreeMid.v:620-931, the same theorem in a section whose signature is identical name for
       name.  The amaps_in_ledger destructure binds its first conjunct and never reads it, so the
       restatement costs nothing here.
       RULE 17 -- NOT ONE DONOR NUMBER IS CARRIED ACROSS.  The donor's tree-specific literals are
       either eliminated or taken from this tree:
         * the donor's four ZH_lo bounds are gone: ZI is now `pose proof (ZH_lo ...)`, so the
           bounds are this tree's own (As/AG_Free7.v:249-250, Bs the same line);
         * the donor's 0x1a0544 / 0x1c4394 / 0x1c4404 and its `unfold put_frame` are gone: FR2,
           PFR2, ESO2, TRB2, TFB2 and F42 restate whatever free_head_refill actually produced,
           by `match type of <H> with rw_cells _ _ ?BASE ?CELLS => ... end`;
         * the donor's 0x1a06a4 (its refill return address) is gone: the two application sites
           take `_` under eapply and the ret_pc rewrite reads the address out of VIS2;
         * the CTX floor is this tree's AIMG_TOP, the same number this file's own FreeAppMid BND
           and As//Bs AG_CacheDealloc3 BND already carry.
       The numbers that remain are frame and allocator geometry shared by both trees and already
       written in this file: 2944 (FreeAppMid BND), 2128 = 208 + 80 * 24, 2272, 2208, -72, -64,
       c = kBatchClass = 24 (AsanAllocModel.v:47), 0x10007fff8000, 137438953472. *)
    intros K.
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK].
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof (proj1 (proj2 HR)) as ND. pose proof (proj2 (proj2 HR)) as LBs.
    (* [comment removed for export] *)
    destruct (free_cells s m ch R CHIN ALLOC UHI) as (b1 & actx & q0 & q1 & q2 & q3 & HDR & Hb1 & ACR & TST & UNW & QC & TQ & QST & INST & IEN).
    pose proof PURE as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & X1 & X2 & X3 & X4 & X5 & V1 & V2 & Q1 & Q2 & Q3 & K0 & K2 & K3 & K4).
    pose proof (free_plu s m ch d R CHIN DPL) as PLU.
    pose proof SHB as [[_ [_ SHu]] SBS].
    pose proof RPURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    fold st in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10. fold r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10.
    fold nf mfa au mu fl in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10.
    destruct (refill_cells_of_arep s m c R HC MISS) as (p0 & p1 & p2 & p3 & PC1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REN).
    unfold a_cache, OT_CACHE, PCLASS_SIZE in PC1. fold st TH in PC1. fold CA in PC1. fold P in PC1.
    apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in PC1. destruct PC1 as [PC1 _].
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ sb mod 65536 = 0 /\ 7430144 <= CTX /\ CTX + 160 <= aceil /\ aceil <= lo /\ lo + 2944 <= bv_unsigned sp
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384 /\ c = 24).
    { assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
      assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
      clear - Y1 Y2 Y3 Y4 Y5 X1 X2 X3 LO HI E1 E2. zlets. unfold a_ri, a_sb, AHI_LO, kSpaceSize, kPageSize, kBatchClass in *. repeat split; lia. }
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ n = 1).
    { pose proof RF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
      pose proof (rf_mfa_delta st c WFs HC ROOM) as FD.
      fold st r in F7, F12, FD. fold nf mfa au mu fl n in F7, F12, FD. fold mu' mfa' in F7, F12, FD.
      unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *. clear - U1 U2 U4 U5 F7 F12 FD. repeat split; first [lia | reflexivity]. }
    (* [comment removed for export] *)
    assert (UB : exists ub, rw_cells asegs m U [CB 8 ub]).
    { pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _). pose proof (CHR ch CHIN) as (_ & _ & STI & JR & _).
      rewrite ALLOC in STI. fold U size in JR.
      pose proof (record_ext s OKs ch CHIN) as (E1 & E2 & E3 & _ & _ & E6 & E7 & E8 & _).
      pose proof (stk_of_rw_cells asegs _ _ _ BLK) as SK. cbn [cells_size csize Nat.add] in SK.
      replace (U + Z.of_nat (Z.to_nat size + 0)) with (U + size) in SK by (clear - Z1; zlets; lia).
      destruct (Z.le_gt_cases 8 size) as [LE|GT].
      - destruct (stk_split asegs _ _ (U + 8) _ SK ltac:(clear - LE; lia)) as [SK1 _]. destruct (stk_cells _ _ _ SK1 ltac:(clear - LE; lia)) as [ub Hub].
        exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - LE; lia). exact Hub.
      - pose proof (junk_stk' _ _ _ JR ltac:(clear - Z1 Z2; zlets; destruct Z2 as (_ & _ & ZT); unfold AIMG_TOP in ZT; lia) ltac:(clear - E2 E7 Z1 Z5; zlets; acb; lia) ltac:(clear - GT E7 Z5 Z6; zlets; lia)) as SJ.
        replace (U + size + (ch_end ch - (U + size))) with (ch_end ch) in SJ by (clear - GT; lia).
        destruct (stk_split asegs _ _ (U + 8) _ SJ ltac:(clear - GT E7 Z1 Z5 Z6; zlets; lia)) as [SJ1 _].
        pose proof (stk_merge asegs _ _ _ _ SK SJ1 ltac:(clear - GT Z1; zlets; lia)) as SK8.
        destruct (stk_cells _ _ _ SK8 ltac:(clear - GT; lia)) as [ub Hub]. exists ub. replace (Z.to_nat (U + 8 - U)) with 8%nat in Hub by (clear - GT; lia). exact Hub. }
    destruct UB as [ub UB].
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@free_head_refill _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo d (as_internal_init st)
                ATSD CTX TH (a_top s) (a_bot s) CH sb U size b1 actx ub kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize sbs
                k (hd 0 (map qb_addr l)) LA (qc_bytes tq)).
      - exact LO.
      - first [exact HI | clear - HI; lia].
      - constructor. exact SPA.
      - constructor. exact SPT.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT1, pT2, pT3. fold CTX in pX2, pX3.
        unfold kPageSize in pT1, pT2, pT3. split; [clear; lia|]. split; [clear; lia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2|]. split; [exact pT3|].
        clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. lia.
      - constructor. repeat match goal with |- _ /\ _ => split end; try exact G10; try exact G12;   (* [comment removed for export] *)
          clear - G1 G2 G3 G4 G5 G6; zlets; unfold a_sb, kSpaceSize, kPageSize, disj in *; lia.
      - constructor. exact PLU.
      - constructor. clear - V1 V2. unfold kPageSize in V1. lia.
      - exact DLO.
      - exact DCAP.
      - exact FCH.
      - exact Ha0.
      - constructor. clear - Z1 Z2 Z3 Z4 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - clear - Z1 QSZ. zlets. lia.
      - exact Hb1.
      - exact ACR.
      - clear - QSZ. zlets. unfold kMaxCacheSize, kQuarantineMaxSize, kQuarantineMinSize in *. lia.
      - exact SBS.
      - pose proof (batches_len_bound s m R) as BL. clear - BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - rewrite TP. exact IEN.
      - exact MI.
      - exact ST.
      - exact UNW.
      - exact FLG4.
      - exact IAX.
      - exact DEP.
      - exact HDR.
      - exact UB.
      - exact TST.
      - exact QC.
      - exact SHu.
      - exact TQ.
      - replace (TH + 2128) with P by (clear - BND; try unfold kBatchClass in *; lia). exact PC1.
      - (* [comment removed for export] *)
        intros NZ. assert (NE : l <> []) by (intros EL; apply NZ; unfold k; rewrite EL; reflexivity).
        pose proof (free_last_cells s m ch d R CHIN DPL NE) as (LBc & _ & _ & INlb & CNT' & CB' & _ & LA1 & LA2 & _ & LAT & LAU & LAD1 & LAD2 & _).
        pose proof (need_new_true_full tq NN NE) as FULL. fold l lb in FULL.
        fold st tq l lb LA in LBc, LA1, LA2, LAT, LAU, LAD1, LAD2, CB', FULL |- *.
        apply (proj1 (rw_cells_app asegs _ _ [_] [_; _])) in LBc. destruct LBc as [LB1 LB23]. apply (proj1 (rw_cells_app asegs _ _ [_] [_])) in LB23. destruct LB23 as [_ LB3].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LB3.
        replace (qb_count lb) with kBatchCount in LB3 by (clear - CB' FULL; lia).
        split; [split; [exact LB1| replace (LA + 16) with (LA + 8 + 8) by (clear; lia); exact LB3]|].
        clear - LA1 LA2 LAT LAU LAD1 LAD2. zlets. unfold kBatchSize, AHI_LO in *. repeat split; lia. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & jk & jke & rest & m1 & VIS1 & MU1 & WM1 & MI1 & ENV1 & ST1 & FR1 & PFR1 & ESO1 & TRB1 & LR & TFB1 & F41
                     & TRNG & NR1 & HDR1 & UW1 & TST1 & UNW1 & FLG1 & IA1 & DEP1 & SHF1 & TQ1 & PC11 & LC1).
    pose proof (munch_agree _ _ _ MU1) as AG1.
    (* [comment removed for export] *)
    destruct (refill_cells_at1 s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO MISS ROOM QSZ m1 MU1 WM1)
      as (q0' & q1' & q2' & q3' & PC1' & PCJ1 & FAM1 & QST1 & RIC1 & RIJ1 & EXH1 & RST1 & FARR1 & FAJ1 & USJ1 & I1 & I2 & I3 & _).
    (* [comment removed for export] *)
    pose proof (ZH_lo s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ) as ZI.
    assert (ZC : forall a, CTX <= a < CTX + 160 -> outside Wh a).
    { intros a Ha. pose proof (rec_vs_ctx s m ch R CHIN) as RC. pose proof (record_ext s OKs ch CHIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
      pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & pX2 & _). pose proof (aapp_lit _ _ pX2) as BC. fold CTX in BC.   (* [comment removed for export] *)
      apply (ZH_hi s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ a);
        [clear - Ha Y4 Y5 BC| clear - Ha RC E3 E6 E7 E8 Z1 Z5 Z6| clear - Ha RC E3 E6 E7 E8 Z1 Z5 Z6| clear - Ha Y6| clear - Ha G5| clear - Ha G6];
        zlets; unfold AHI_LO, AIMG_TOP, ALOWSH_LO, disj, kPageSize in *; lia. }
    assert (REN1 : RENV tp ATSD CTX TH sb (a_ri s) m1).
    { rewrite TP. destruct REN as [SE I1' I2' I3']. open_senv SE.
      constructor; [constructor| exact I1| exact I2| exact I3].
      all: eapply (rw_cells_transport_pt _ _ _ AG1 WM1); [eassumption|]; unfold AGOT_VALS;
           cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length map];
           let Ha := fresh in intros ? Ha;
           first [ apply ZC; clear - Ha; zlets; lia
                 | apply ZI; unfold AIMG_TOP, AIAINIT, AIAINST, wz, ATP, ATSD, AGOT_VALS, AINST in *; rewrite ?unsigned_lit in Ha by (clear; lia); clear - Ha; lia ]. }
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof AMX1 as AMX1'. destruct AMX1' as [AM1 AK1].
    pose proof AM1 as AM1'. destruct AM1' as (AIL1 & ASV1 & AB1). destruct AIL1 as (_ & _ & _ & NOV1 & NW1 & NWA1). destruct AB1 as [AB1a AB1b].
    (* [comment removed for export] *)
    replace (wz (TH + 2128)) with (wz (TH + OT_CACHE + PCLASS_SIZE * c)) in VIS1 by (unfold OT_CACHE, PCLASS_SIZE, c, kBatchClass; f_equal; clear; lia).
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q _ (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0_1 t1_1 t2_1
              (wz (TH + OT_CACHE + PCLASS_SIZE * c)) (wz (TH + OT_CACHE)) (wz size) (wz AINST) a6_1 a7_1
              (wz (U + -16)) (wz (TH + OT_TQ)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz size) (wz kMaxCacheSize) s7 s8 s9 s10 s11 t3_1 t4_1 t5_1 t6_1
              F fc m1 lo sb c (TH + OT_CACHE) TH CTX ATSD nf mfa au mu fl (as_cache_inited st)).
    { exact LO. }
    { rewrite unsigned_lit by (clear - SPR BND; acb; lia). clear - BND; try unfold kBatchClass in *; lia. }
    { rewrite unsigned_lit by (clear - SPR BND; acb; lia). clear - SPT; lia. }
    { constructor. rewrite unsigned_lit by (clear - SPR BND; acb; lia). clear - SPA. Z.div_mod_to_equations. lia. }
    { exact HC. }
    { reflexivity. }
    { clear - X1 X2. zlets. split; assumption. }
    { constructor. exact X3. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { unfold ATSD, AIMG_TOP. pose proof PL as (_ & _ & _ & _ & _ & _ & _ & pT2 & pT3 & _ & pX2 & pX3 & _). fold TH in pT2, pT3. fold CTX in pX2, pX3. unfold kPageSize in pT2, pT3.
      split; [clear; lia|]. split; [clear; lia|]. split; [exact pX2|]. split; [exact pX3|]. split; [exact pT2| exact pT3]. }
    { constructor. clear - Y3. zlets. Z.div_mod_to_equations. lia. }
    { constructor. unfold kSpaceSize. clear - X4 X5 Y6. zlets. unfold kSpaceSize in *. lia. }
    { unfold kFreeArraySize. clear - BR. lia. }
    { constructor. exact U3. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - BR. lia. }
    { constructor. exact U6. }
    { exact U7. }
    { exact OK1. }
    { exact VIS1. }
    { exact MI1. }
    { rewrite unsigned_lit by (clear - SPR BND; acb; lia). exact ST1. }
    { exact REN1. }
    { exact U8. }
    { exact PC1'. }
    { exact PCJ1. }
    { exact FAM1. }
    { exact QST1. }
    { exact TST1. }
    { exact RIC1. }
    { exact RIJ1. }
    { exact EXH1. }
    { exact RST1. }
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - BND; try unfold kBatchClass in *; lia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - BND; try unfold kBatchClass in *; lia).
    { exact FARR1. }
    { exact FAJ1. }
    { exact USJ1. }
    { intros a kk Ha Hmc. exact (ak_resf_hi s mo1 AK1 a kk Ha Hmc). }
    { intros a kk Ha Hk. apply (ak_prim s mo1 AK1 a kk c); [unfold kNumClasses; clear - HC; lia| exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW1. }
    { exact NWA1. }
    { exact NOV1. }
    { intros x Hx. apply (ak_zr_sb s mo1 AK1). unfold kSpaceSize, kPageSize. clear - Hx BND. unfold sb in *. try unfold AHI_LO in *. lia. }
    { exact (ak_zrsh s mo1 AK1). }
    { exact (ak_lsh s mo1 AK1). }
    { intros x Hx. apply WM1. exact (AWV x Hx). }
    { unfold ABUDGET, aPhi in AB1b. change (a_st s) with st in AB1b. unfold COLD_COST in PROOM. unfold page_size in AB1b. clear - AB1a AB1b PROOM. lia. }   (* [comment removed for export] *)
    { exact U9. }
    { exact U10. }
    { exact (ak_atop s mo1 AK1). }
    cbv beta. intros msF2 mo2 RD.
    destruct RD as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & j0 & j1 & j2 & j3 & m2 & L' & S' & RD).
    lazy zeta in RD.
    destruct RD as (OK2 & VIS2 & EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG & MU2 & WM2 & MI2 & ST2 & PCN & FAM2 & CHA & CHJ
                    & RI2 & RIJ2 & EXH2 & RST2 & FARR2 & FAJ2 & USJ2 & POIu & POIf & QST2 & TST2).
    fold mu' nnew nf1 mfa' au' fl1 n in VIS2, EL, ES, VMN, EAG, MU2, PCN, CHA, CHJ, RI2, FARR2, FAJ2, USJ2, POIu, POIf.
    rewrite unsigned_lit in MU2, ST2 by (clear - SPR BND; acb; lia).
    subst L' S'. fold L2 in OK2, VIS2. fold S2 in OK2, VIS2.
    fold chunks2 in CHA.
    (* [comment removed for export] *)
    pose proof (after_refill_bundle s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3
                  MU1 WM1 MU2 WM2 MI MI2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1
                  b1 actx (d_putid d (depot_hash T)) (hd 0 (map qb_addr l)) (qc_bytes tq) HDR1 UW1 FLG1 IA1 SHF1 TQ1 LC1 INST) as ARB.
    destruct ARB as ((R2 & MIR' & WM0R' & AG0R' & FXR2) & (EB & A1 & A2 & BT & BUx & BD1 & BD2 & BPOS & BLA) & (N1 & CC & TK & CPS) & LAX
                     & BJ2 & HDR2 & UW2 & FLG2 & IA2 & SHF2 & TQ2 & LC2 & INST2 & PC12 & PC22 & PC32 & PC42 & UNW2).
    (* [comment removed for export] *)
    assert (ZK : forall a, bv_unsigned sp + -2272 <= a ->
                 outside (rf_W lo (bv_unsigned sp + -2272) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a)
      by (intros a Ha; exact (ZR_stack s m d lo (bv_unsigned sp) ch R DPL LO HI MISS ROOM a Ha)).
    assert (AG2 : agree_on (outside (rf_W lo (bv_unsigned sp + -2272) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu')) m1 m2) by exact (munch_agree _ _ _ MU2).
    (* [comment removed for export] *)
    match type of FR1 with rw_cells _ _ ?BASE ?CELLS =>
      assert (FR2 : rw_cells asegs m2 BASE CELLS) by (trp rw_cells_transport_pt AG2 WM2 FR1 ZK SPR) end.
    match type of PFR1 with rw_cells _ _ ?BASE ?CELLS =>
      assert (PFR2 : rw_cells asegs m2 BASE CELLS) by (trp rw_cells_transport_pt AG2 WM2 PFR1 ZK SPR) end.
    match type of ESO1 with rw_cells _ _ ?BASE ?CELLS =>
      assert (ESO2 : rw_cells asegs m2 BASE CELLS) by (trp rw_cells_transport_pt AG2 WM2 ESO1 ZK SPR) end.
    match type of TRB1 with u64arr _ _ ?BASE ?VS =>
      assert (TRB2 : u64arr asegs m2 BASE VS)
        by (eapply (u64arr_transport_pt _ _ _ AG2 WM2); [exact TRB1|]; intros a Ha; apply ZK; clear - Ha; lia) end.
    match type of TFB1 with rw_cells _ _ ?BASE ?CELLS =>
      assert (TFB2 : rw_cells asegs m2 BASE CELLS) by (trp rw_cells_transport_pt AG2 WM2 TFB1 ZK SPR) end.
    match type of F41 with rw_cells _ _ ?BASE ?CELLS =>
      assert (F42 : rw_cells asegs m2 BASE CELLS) by (trp rw_cells_transport_pt AG2 WM2 F41 ZK SPR) end.
    (* [comment removed for export] *)
    replace (wz (TH + OT_CACHE + PCLASS_SIZE * c)) with (wz (TH + 2128)) in VIS2 by (unfold OT_CACHE, PCLASS_SIZE, c, kBatchClass; f_equal; clear; lia).
    match type of VIS2 with context[ret_pc (wz ?RA)] =>
      change (ret_pc (wz RA)) with (ret_pc (Z_to_bv 64 RA)) in VIS2; rewrite (ret_pc_even RA) in VIS2 by (clear; lia) end.
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (@free_tail_refill_mid _ sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc
                t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 _ m2
                lo T rest jk jke U size TH kMaxCacheSize sb k (hd 0 (map qb_addr l)) LA (qc_bytes tq) n chunks2 B j0 j1 j2 j3).
      - exact LO.
      - first [exact HI | clear - HI; lia].
      - constructor. exact SPT.
      - constructor. clear - Z1 Z2 Z3 Z5 Z6. zlets. destruct Z2 as (_ & ZU & ZT). repeat match goal with |- _ /\ _ => split end; [apply (aapp_sub _ _ _ _ ZU); lia| lia..].   (* [comment removed for export] *)
      - constructor. pose proof PL as (_ & _ & _ & _ & _ & _ & pT1 & pT2 & pT3 & _). fold TH in pT1, pT2, pT3. unfold kPageSize in pT1, pT2, pT3.
        split; [exact pT2|]. split; [exact pT3|]. clear - pT1. zlets. Z.div_mod_to_equations. lia.
      - constructor. clear - X1 X2 X3. zlets. repeat split; assumption.
      - exact CC.
      - clear - N1. zlets. rewrite N1. clear. lia.
      - exact CPS.
      - exact EB.
      - constructor. split; [exact A1| split; [exact A2| exact BT]].
      - pose proof (batches_len_bound s m R) as BL. clear - BL. zlets. unfold zlen in *. rewrite length_app in BL. lia.
      - intros NZ. split; [exact (LC2 NZ)|].
        destruct LAX as [(_ & _ & KZ)|(_ & _ & L1 & L2' & L3 & L4 & _)]; [exfalso; exact (NZ KZ)|].
        split; [exact L1|]. split; [exact L2'|]. split; [exact L3|]. split; [exact (BLA NZ)| exact L4].
      - intros KZ. destruct LAX as [(_ & LA0 & _)|(_ & K1 & _)]; [exact LA0| exfalso; clear - KZ K1; zlets; lia].
      - exact LR.
      - exact NR1.
      - exact MI2.
      - exact ST2.
      - first [exact FR2 | unfold put_frame in FR2; exact FR2].
      - exact TQ2.
      - exact PC12.
      - exact PC22.
      - exact PC32.
      - exact PC42.
      - exact QST2.
      - exact INST2.
      - exact BJ2.
      - first [exact PFR2 | unfold put_frame in PFR2; exact PFR2].
      - exact ESO2.
      - exact TRB2.
      - exact TFB2.
      - exact F42. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j2' & m3 & VIS3 & MU3 & WM3 & MI3 & ST3
                     & PFR3 & ESO3 & TRB3 & TFB3 & F43 & TQ3 & LA3 & NB3 & NBJ3 & PC13 & PC33 & PC43 & STATS3).
    (* [comment removed for export] *)
    pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3) as WM03.
    destruct (head_cells3 s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3
                MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3
                b1 actx (d_putid d (depot_hash T)) HDR2 UW2 FLG2 IA2 SHF2 UNW2) as (HDR3 & UW3 & FLG3 & IA3 & SHF3 & TST3 & UNW3 & DAV).
    pose proof (arepq_after_refill_new s m d lo (bv_unsigned sp) ch bs L2 S2 AL' R CHIN ALLOC UHI DPL LO MISS ROOM QSZ BLK m1 m2 j0 j1 j2 j3
                  MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3
                  b1 actx (d_putid d (depot_hash T)) j0 j1 j2' j3 Hb1 HDR3 UW3 TST3 UNW3 FLG3 IA3 SHF3 TQ3 LA3 NB3 NBJ3 PC13 PC33 PC43 STATS3 WM03) as AQ.
    apply K. unfold free_refill_gmid.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', jk, rest, m3.
    split; [exact OK3|]. split; [exact VIS3|].
    split. { split; [exact AQ|]. split; [apply lb_remove_nodup; exact ND|].
             exact (alb_after_refill_new s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM QSZ m1 m2 j0 j1 j2 j3
                      MU1 WM1 MU2 WM2 PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 LB LBs). }
    split. { intros x Hx. apply (win3 s m d lo ch R DPL LO MISS ROOM m2 POIu POIf m3 WM3 (a_S s) x Hx). intros Hx'. apply WM03. exact (AWV x Hx'). }
    split. { exact (flagsx3 s m d lo (bv_unsigned sp) ch L2 S2 AL' R CHIN UHI DPL LO MISS ROOM NN QSZ m1 m2 j0 j1 j2 j3 MU1 WM1 MU2 WM2
                      PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW1 m3 MU3 WM3 WM03 (FXR2 FXR)). }
    split. { assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).   (* [comment removed for export] *)
             pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 AL' AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK))
                           eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.   (* [comment removed for export] *)
             exact (amodelx_free sR mo3 ch tq' cache' (AMODELX_mat sR mo2 mo3 AMX2 SBM3)). }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM1) (nonvm_same_trans _ _ _ NVS (nonvm_same_mat _ _ SBM3)))|].
    split. { apply avmx_same; [| reflexivity]. rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). reflexivity. }
    split. { assert (DEP2 : DEPOT asegs d' m2).
             { eapply (DEPOT_transport asegs d' m1 m2 _ DEP1 MU2 WM2). unfold d', depot_avoid. rewrite d_nb_put, d_sb_put.
               exact (ZR_depot s m d lo (bv_unsigned sp) ch R CHIN DPL LO MISS ROOM). }
             eapply (DEPOT_transport asegs d' m2 m3 _ DEP2 MU3 WM3). unfold d', depot_avoid. rewrite d_nb_put, d_sb_put. exact DAV. }
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split. { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
             rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI3|]. split; [exact ST3|].
    split; [exact PFR3|]. split; [exact ESO3|]. split; [exact TRB3|]. split; [exact LR|]. split; [exact TFB3|]. split; [exact F43|].
    split. { intros x Hx. unfold fr_W in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2].
             pose proof (AG0R' (bv_unsigned x) Hx1 (bv_unsigned_in_range _ x)) as E1.
             pose proof (AGR3 s m d lo (bv_unsigned sp) ch m2 m3 MU3 (bv_unsigned x) Hx2 (bv_unsigned_in_range _ x)) as E2.
             unfold wa in E1, E2. rewrite Z_to_bv_bv_unsigned in E1, E2. rewrite E2. exact E1. }
    split; [exact WM03|].
    (* [comment removed for export] *)
    assert (IM : forall a, U - 16 <= a -> a + 1 <= U + round_up size 8 -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply (aim_of_aapp _ _ a UHI); clear - Ha Hb; zlets; lia. }   (* [comment removed for export] *)
    assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
    { change (as_space_beg st) with sb. unfold kHighMemBeg, kHighMemEnd, kSpaceSize. clear - BND. acb. Z.div_mod_to_equations. lia. }
    destruct (am_free_refill_gen st ch (free_find st ch WFs CHIN) ALLOC ltac:(rewrite Q1, Q3; unfold kMaxCacheSize; clear - QSZ; lia)
                ltac:(change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); clear - Z4; zlets; Z.div_mod_to_equations; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5; zlets; unfold AHI_LO in *; lia)
                ltac:(apply IM; clear - Z1 Z2 Z3 Z5 Z6; zlets; unfold AHI_LO in *; lia)
                cp (tl chunks2) WFs NN MISS ROOM HM TK BPOS) as (stX & ev0 & ev2 & E & SBS' & SC0).
    exists stX, ev0, ev2. split; [exact E|]. split; [| exact SC0].
    unfold free_new_state in SBS'. change (get_pc (refilled (set_internal_init st) kBatchClass) kBatchClass) with (get_pc st2 c) in SBS'.
    rewrite PCc in SBS'. cbn [pc_count refill_pc] in SBS'. exact SBS'.
  Qed.
End FreeRefillMid.
End HCW.
(* [comment removed for export] *)
