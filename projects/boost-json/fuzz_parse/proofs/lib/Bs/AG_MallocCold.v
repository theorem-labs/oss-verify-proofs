(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_InitCache AW_Efs AW_Populate
     AW_Refill AW_MallocHead AW_MallocTail AG_WFHit AG_MallocModel AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2 AG_WriteSet
     AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 SecLazy AllocWalkKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_MallocCold () := KReplay.lz_vm "#'%<C46Stdlib9micromega5Tauto5eKindK!sE;8GFormula08K47Corelib7Numbers7BinNums8positive02!sKG1!sK=1Z02C5!tZ&6ZArith6BinInt1Z3addI!sa+4Init9Datatypes4prod00!sc=mulK!sc<list!tf/!sF82I!sFA0!vd66VarMap1t!v9#!sD>3I!sD?0!sD6=RingM!s4'7!wm'!tS77Env!sT#5PExpr!wk/!u>26option02!yE<8B!t7&!sj25Logic2eq01!sb6:Z!tw+=Z!sn$CheckerI!sl;0C!v-<4find!t3AC!t30_sou!{I#!t9'5Lists7!s+#Def6Forall!xl/!sG9!vU=3nat02C89OSSVerify6Proofs:boost_json:fuzz_parse3lib2Bs<AW_!sn#Cache8icW_fromC13~~~I!tZB0!t;`3icW!t6%!smS=AW_DepotFrame6avoids!sq&!}0;2le!xU9or!xU#!vr;s!xS#!sC;fstK!~hA1!{nE!sIF3K!}/L1!#6BE4!sJF6!tdE5I!#6?>0!u&D3Op203!#4|<uni!#4|8!tz%4kind!#6+>!sf$1!#8YF!#5M6!}~-;!ya%!zW$00!u#=bool!u##!sF@!#9m@1!~<A!sc?N02I45stdpp9bitvector;definitions2bv00I!}hVAllocBase4AENV00!}kY8!sm$Rep8agree_on!snV3Lib5!~T$5wmono!~SDt!}t<6length!sF23Nat3add!sy<6of_natC!w1@;bv_unsigned!uVT4TacX2b8!uR%K!v=TCells4cell04!sjf5!wmZ!u=%wz!tQf2!sj&!|H?3!x7,!#:K03map!tL`1!uw&!t-:6repeat!#Cy<pow!tN`3!tN3!~x3app!wdT3Arr6u64arr!t,'!#5Y3;ZifyClasses6eq_iff!tS2!#<1$8iff_refl!~q\Erw_!ub#s_transport_pt!xd'!#9>A5Psatz!#FX7!#7k:!#G+@1!#>g73and!#D?7!vE/9and_morph!x~34Znat5Nat2Z9is_nonneg!uRK7!sOK5!tnB;rew_!wu%v!sQ+!{6%4!s+#:!#5k$_map!xY9!xu#nd_r!sc?!zNS!xx/C!zR%!xv7!#:Xd1!#4yZStep8!zb'!|>H3inj!sIB5mk!vH#!}-B!sK$2!sqErel!sKB7!xj&!#D+E5C!#4_X:!}{%size!}sQ6I!#5x^!#?xY5ASegs5aseg!xC=8!v`#Inst7Inj_Z_ZI!#C$?!#FuI5!~}+5!~|$8PeanoNa!#?f;!#3E,7inj_!sI#!|rTsShadow3mem!vP_7AIMG_LO!sj_8!sj$TOP!skY!#36'9AGOT_VALS!z/<!#8S:1!x8<!#W#&0!w%\8poisoned!uU[!sn&2sh!sh&!#Ef;modulo!t0\<!tx%_bytes!#5vY3Arr5u8!#?2+!sgTMem8!tP$_at!sj^5wr!sga2wa!~h2!#:~,=!#Cp$_!#JW7!#;f$6!#;f$!#D;<sub!sC<>pow_po!#>[&!sN<:!sN#!sJ&!{U59SatDivModCZ_mod!sP&!#?X<!#U,14!#LI@7Z_to_bv!v}T6MStateC!sf&_!#M9-!wwY2Nd:and_elimF!#GL'ELinuxProcessSemantics?!s<2>Riscv!sE+5wview!xA83not!#D?74True!#8?J1C7!uTN<LazyRestrict:in_rangesb!uZ&!sq]z!sr'!sq'!#:k;orb!t6]?!u%,_con!#<L24Bool!s'$;orb_false_r!|C=leb!sC>tb!u<<4andb!{YE7!{3[<!{$'_lit!vpB9!tZ#_prop!#7r<leb_le!sF>tb_lt!#\PA2!{,89F!w+$ind!{385!sE$!#]T3!{P/1!tf<5ldiff!u,=shiftr!sFBl!xQ=div!sC<7div_mo!#6q<=mod!#6T#boun!sMBneg!sM25!#D3$PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL&!z>>3P!#aH$!sG4!#GK7!#f6F7!uW<?!wL%_!u6#pow2!sOBl_mul!sOA4ones!sD<<!y'$_!sJ#!~:>4lnot!sD>a!wy>:!t0%!sJ$!#A5Q9!#Dn&X7AMODELX!}t%I!#E^Z3ast!#KN&I!#9zI5!#3J#5Model00I!#6lN>Asan!tJ$!sd$5chunk!#epc4AREP!u:'!{A'!#A6+5NoDup!#XR,!sB-2InC!vZ]l!#:,8!#<o%!#\f:5proj1!tE\6ast_ok!vRb8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!uMgregion!spgpclas!w1gA!tb&s!#M`#!swf?!sw&junk!suf4a_s!#?}&!#3d]:!#3d#_list!{Kc!sp%!uP,!#5J^as_tq!sne7qc!uQg;batches!uSmg!uSf;kNum!#a6%!x&cplaced!#60[7!so$Wf2WF!sg&!#7z;2!t&[=rz!#b[#_facts!y2f!sv&!wOfcompute_re!xEf5rq_rz!sne9rq_need!#T1'!#3+^rq_primary!w?gq!w?/!#J8;eq!#P$<7eqb_neq!ycS;As!$2{#Hash:d!s0#_ha!#_n'!ssR:!ss&Inv7d_puti!w1f?!yc#act_to_add!#wh2!#Bu-hd!u$US_Refill16rf_au'!up[!sn+7rf_mfa!soe!t_#nf1!t_hnnew!t_hm!v@f4!t_#!y/e>rg_mapped_user!sweArg_a!s4#at!szlD!ts,free_arra!#39e<rg_num!sz$!#k=[l!#Ao'ri!#5ie!#E?$!#98h8!ss%!#3F'!#5j;max!t6`round_u!#ESb5a_ctx!wOe!#c|'!tW^thr!vTB8max_spec!#jpBdiv!#jp0!#lv;symK!wN^3r!$KM#!u,$!#_|7!$,g#!#R]P3Lib9LiaTuning9zify_don!#}C<!#v::3!#\yE3!zD`kMaxS!|G,!u\S!#m2/7!yXZCidBits2=!}1'_le30!~%e9!z'#coun!#K;Y7!tg&=!#3f+_ge!srZ!te$WfF!sr-tabl!#Gj0!wE`4!thY9AW!#;e%?!vN+!tc0!#al;even!sD=E!sD?9!sb#!~g$!$U'9x!$Z<=!#hZ$ul!#3l=ul_commc!v&R=AG_M!#<w#ColdAm!s1$_cold_gpo!#Qs\!#~C%5aceil!#7Rdpa!tWb4aap!#9odkobj!uCcdisj!tWd_f!#wZW!#3516as_sec!soe:sc_map_beg!sse;!ss&s!#7KX!#=82o!#?Vebo!$Cz'!#kHH3Run6config0!#goS!#OA,4d_n!#@5Y!sl1!#@{Z!#o6+8awin_vis!soc:!#h_#x!#g#f!#pq$!t_c7akerne!#4Ub?amaps_in_ledger!sud!#f|%visibl!{qc7ABUDGET!}Ve7as!}V#!#^Dfmp_kin!#K?%!#FR^5m!$_[#3!spl4!uTibase!spi!#5d,!#xTO8m_vm!wu$!s]P7vm_!s\U;vm_noac!s;#!zh\3a_L!vRV:LazyL!}0$9nooverlap!sna>entries_nowrap!#3nZ!#B@&<ienv_of_a!#5Q'!#~UR=AW!ss&!$PK#I!$c}-!yw^4zle!#[l&!#`{54last!#N3_qc!$CN[!#As/jun!#|Fb7a_cach!#Of];!#KG'11!sl]!#L5+5!x/e?as!uL%_init!#k<gget_!#y+$!w7b2FA!t]e=rg!#`c4!t`\RB!}5Y!#e/-R!}2/!#NV:6to!$k[#!#Hs^!wO#p!#Hse9pc_!#{m#!#=Pe<as_space!#Iih!$&b&!ss,!xIXKit=!sp,_!#ugf?!z3,!#=c-!tm[B!su2!tr,!{2[9!#QK#_env!sob8aapp!sn-!vSO8HeapCeil5h!#UF^!#TZ%;!#V3#!#[m[!#IR/@sh_!st#ing!$Io$!w5i!$G|+!w5a!sn+!$gkT!sn#WalkKit6hidden!#fS&I!srg!$=Ib3a_S!sib4a_Z!#M\Y!#A^0:icpt_chai!#:j[sUnwind6utrace!tccHead@!#_R%hea!$I}#!$[dZ!%#\$3mkR!sgZ8PropExec7seg_!%5z'!snT!$Q1%2MS!v=g;!v=-!#4@U!$UL/Esame_but_materializ!#AZW6!s|#SR8hid_!sz#!tgc8r!s/&!xj`5munch!siZ3Mem7mem_i!#8H'!#hn0!$lg#sub!#i,2!$m/#2le!%;sXA!}R'6afr!vh,!spR>!#31&Facts2;!v#$_!%1=#!vp`7outsid!#8{b@stk!$~w7!#lo9!#vrT2Nd9ex!#Je$2!t|bCu32!${$9!#w:D1!w0Z=disjoint!%B|,!u8S!#Hd,>renv!u8,!svY!#>|+;!$T2%_ma!#>-b4a_AL!#36b:eager_use!#5jc;pages_tota!#qVdPh!$-S&!#]2Pvm_limi!%9kAD!$kX,_!$f?&!sYA:b!$_b#ulus!xl]:ak_resf_!uTY<map_contain!tT^7ak!$@M#!{2c8ak_zr!#lwe7!so$!$?^Z!sn,6ak_l!sm[;!#97$udget6pusa!#IPZ!uN1a!#s5[!$=[1!$-{+!so^6rf_fl!#\RZ!#Bn%6r!#V>-!{$P=!#o7#subtract!u?S7SecLazy:nonvm!#Af-!#gzSreserved!}7Rvm_m!#z5#ase!saQ6vm_brk!x&^4rf_!%U\&!#>-'!%B?1firstn!t3^8rf!#7h^>AG!sp&!#Zs$!$G4$_delt!%#T2!#>8+!%6x-8or!%>S%!u:]<icW_!#>D&!{QZ!#?2$B!%BK4!sv`;!%NH#!ss%!soZ3Mem;wa!%#72!#D/68eq!t9&!vjT!x4'2Aarep_after_r!s9$!y/h8!sr%!u5'!#WRR!#Uj,st0!$M;[!u\+C!$##%!u^6!#O3U;lzok!$~S%!slV9!sl#NodesFlazy!so&_okb!#s<_!#6;&?!#6;+!#:;_!v['3Dam!xA#x!y<wfd_pc_c!sth9!th%!#ipg8!td#!$@d\!#wh+Ahit!#3i%!#wm/C!{xXKitB!$Y#1!#g6[!%g`0;!$[d$!%gf#!sv%!$=n`:icW_!%h\/!tm`?DEPOT!#Neb!~p-?!#T^%_!%lU#a!#ak%!#Sn8or01!$@taa!#Ps/!#S,'!#8lS!#C$%;!#C$$_!$DL#!v%Z!$`[,!xi$W!sod5!$aL#!x]]!#eU+!#`Y&!#ck,!$Uz<in!t;]TailB!t;&from!#54_!#]</5b1!$mv[!so0<!tl%!$7A$!#3C^!$:]#RHEAP!|L]!vT%2<!yI%!$pU$!stearhea!#?l%!stY>!st+!#8Y$hit_s!%BB#!tkc9new_bloc!$+t[!#tR'ddressa!$<H[!#Q/+9!wF%co!#wiY;AG_WriteSet4avmx!w<h?!#jS'!zk0!#\_[>!%Aq,!$Mb+!%Ap4<orb_true_iff!#7O`=!tA-if!t@%!#;Obn_window1!#4x8!%Wu$Z2Nat2id!t;a@!%Sr&!$CI0!s{a;!#D-&h!#zaZ!#Eq&>!#Eq,!#dN[!ss'@!ss-!#N/Z!#?N38d_sb!#:d`!ss0n!ss/!{o\L!#t<7!$BD&!}qZl!#on/!#AE&!$WZ[!#3Y-9avmx!#Z]-!#3^U!#IO-WF!#=-_!#Gb'<carved!$<|[!sr/6!sr%!~29!$74+divid!%L5<:mod_!sJ%!%FyJ3!%GkB!&4fUG_!~G#!w3$;in_mem_high!zvV!$Cm2rq!$x['!vB<ltb_ge!$8k_!$fj$oo_bi!$7vY!u{0:land7_mod8!#6@g!su#_lnot7'!tlf>am_!$de,!wle;!sw,!#@tV!$E{&ex_introF15!sl]!$E{+8!tY^!$GV+!sl^:!#{n'!$L_V!#[s%Bevt_sreach_!#[5#!%ek[!uN1!w%^!#~>'4!tXg31!w$g!%//c4=!#[E%!w2%!z?g6!woh7!v=f!x\_!tY-3!w'[!#<}&1D!w'&!#]hb!tj42!w3&!%UQO6SR!xZ#6!xa%!$?#W!#l&+3st!#5S&!$W753rev!vVS!#S}'5w!%G|Y3!&3e'!$07#!vAW!#44$4lzo!%Xc[!#[%-!#_n#!vE=2tl!$d9_!%Z[$!%+Y8!%z341!#AAB!%'>_>!#e5#i!$j~#!%~e+!swO4Scfg=hunspell_scf!$Qpe@kPtrArrayR!#{&$!sye9kPage!%,y+I!%s@X=machine!#Yp$00!xx_6c!sk%1!{ZV!sq3a!t^&!{dY!#Yl,ASSPGUARD!spY!#[Q'6AHI!&+c+!uQ^:kSpaceS!$zVd8AFS_SIZE!w6fs!%eY/!sq_7mapping!srg!$pu%!sp&!$qge2!spl6!spl8!xub3AT!&3Mb4ATSD!sjb<OT_SWITCHING!srb5OT_TQ!{=fq!%]m#!$ocf7qb!%Qc-!}j\OT_CACHE!snb;!sk$_STATS!taf!sng!xo#UNWIND!xoe;PCLAS!#54-!sq\?REGIONINFO!su/!#?K^kFree!#=e#S!%M2gA!sw,Map!szi<kUser!sul@!tq,Offse!$LWb5AINS!#Ek'!$<cN9page!%$w$!uF^;kR!$lq#!#<u\!$E2/B_PRIM!#4_e!%r;$!#A-Z!#y{/>k!s1%egMagi!$0/%!#^S`4mc!$#Z&!u\`effect!#CdfLIBCPGSZ!spc8!&Go#SS!#<8b7ACFLAG!#6J%!&&%P6VmMaps!$^iQ!#Rl,ivl!~He;kHighMemB!%BEg!st'E!%7#&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc2le37Corelib4Init5Logicjf2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAW_DepotFrame~~~~~~l86avoids79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAW_InitCache~~~~~~q43icWjf3and04Nposhc2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~vd8AIMG_TOP35stdpp9bitvectorbdefinitionshk32bv37Corelib4Init9Datatypeshm66lengthhm64list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAW_AllocBase~~~~~~hp04AENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~hta3memhk3bbv_unsigned37Corelib4Init3Natiie3addvd7AIMG_LOvd5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~il98agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~iq35wmonohc3mulhc6of_nathm66optionhta2shhm64Nonehm63natjf2eqjf3not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsji15wviewhta8poisonedhm64prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jn52wzhm64boolhm64conshm63nilhm64pairhm64true69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~jtdain_rangesbhc3powhc4landhc4lnothc6modulohc3sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~kkd7AMODELX3h5LinuxProcessSemanticsfLinuxProcessSem5Statekp75Model69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~kse5chunk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_MallocModel~~~~~~lh89hit_stateil94a_ALil93a_Lil93a_Sil94a_Zril95a_botil95a_ctxil95a_fsbil94a_stil95a_thril95a_topil93astil95mkAstiq33ivlhm63appji1dmachine_statejf2exkse6astatekse6effect79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mg44cellhm64Some3h5LinuxProcessSemanticsfLinuxProcessSem3Runml05mkCfgksebam_malloc_k79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAG_Malloc2~~~~~~mp4cdepot_placed99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAG_MallocCold4HCW2eMallocColdGlue~~~~~~mu44mc_Wlh8fsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAG_WriteSet~~~~~~nl64avmxil96ARHEAPkkd8awin_viskkd9depot_covkkdaflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~nt05DEPOThtabaddressable79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~oi8anonvm_samejtd8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~onf4lzokmg42CBiq33mkRiq35munchiq33stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~otd2MSotd6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~pia7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~pmf7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~pr98rw_cellshc6to_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~qg96sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~qkcdhunspell_scfgmu4h1malloc_cold_gpostkse7rz_sizekse8round_uphc3maxkse8class_idkseaclass_sizehc3divil94a_rikse6regionkseaget_regionksecrg_num_freedkseh4rg_mapped_free_arraykseh1rg_allocated_userkseerg_mapped_userksedrg_free_array79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAS_Refill1~~~~~~rm94rf_nrm96rf_mu'rm97rf_mfa'rm96rf_fl179OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAG_RefillModel~~~~~~rt08refilled37Corelib5Lists7ListDefsi06firstn36Stdlib5Lists4Listsk12hdksefcompact_to_addr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAW_MallocBase~~~~~~smdaicpt_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsUnwind~~~~~~sre6utracent05depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsDepotHash~~~~~~tgfadepot_hashnt05d_putil92RBkp7dmaps_subtracthc3ltbil92FAkseaCAllocatedkse7mkChunksk12tlrm94rf_Wnt07depot_Whta5aceilkse8kMaxSizekse6get_pckse8pc_countil93ATPnt08d_framesnt05d_idssre9goodframesrebframe_chainmu49COLD_COST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAllocBudget~~~~~~uic6B_PRIMuic6pusagekseh0kFreeArrayOffsetkseckUserMapSizehk37Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma icW_avoids : ltac2:(zQ "60!h9!j4!ja!l3!pb!u6>2CA$0>1a$0>1b$0>0@2$3@2$2^1@2$1^3+l4@2$2@2$1^3+ps0^2@3$4@1$5^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_MallocCold ()) ["HCW"] "##j%h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with72CAh81Hh91ah:1bh;2ivp%0p;1p;2p;3p;4p;6p;7p;8g0000R0p4p711g000OR1p4p73101p8g0013j1ATg001Xj1BTg002=j1=!s/$[j20Tg0038j2W!s/$Xj29Tg0045j1H!s/$Uj3:Tg0055j1g!s/$Uj2LTg0063j4a!s/$Qj1]!s/$oj1[Tg007Zj2GTg008=j1U!s/$_j2TTg009Aj2S!s/$[j2RTg00:Gj3Q!s/$aj3PTg00;@j4OTg00<2j2N!s/$Sj63Tg00=4j1;!s/$Sj3fTg00>_j3eTg00?@j1dTg00@Gj3cTg00ARj2@!s/$nj2FTg00BHj3`!s/$ej3_Tg00CBj4^!s/$bj2\Tg00DEj3C!s/$hj4ETg00ESj7DTg00F7j7K!s/$[j3bTP1j8ZTf0R1#A#Ap=>f2R2f1R3'0/@1p=J1@23/F1p=Ig00G>R4f3R57`4/@2A_441,@3'Fp=2P4P410521031C^p=51\41p=?P4P2g00G\R6AC431CEp=YP5P0g00HCR7P7g00HcR8P4AC423P6P1CEg00ICR9FDp=XP5P0P7P7P8P2!s0+3P9FDP1FKp=VAb4319C42p=7!t2$p=1!s[-4P2P!tJ'P!sy$6f7!sD'f6f5R:f4R;!sV+!s`2P3!s]%P1FKGZp=410:;/@51031,@2'Fp=8%;1#;p=M!s-$#;#;p=<g00IcR:#AR9#B#AR6#B#>#=R0,02%A9R<#B!s$$>!s$$=R==J235I11W44R>P1P5P2P1C2X;>R?%A6!sK$6%=:R@'9RA,05RB%=<RCPB%><#=R<C5RB10@@RD,96RE,05RFPCPFP<C5RF10D!s@&G,05RHPCPH!s@$H!s@,I,05RJPCPJ!s@$J!s@,K,05RLPCPL!s@$L!s@,M,05RNPCPN!s@$N!s@,O,05RPPCPP!s@$P!s@,Q,05RRPCPR!s@$R!s@,S,05RTPCPT!s@$T!s@,U,05RVPCPV!s@$V!s@,W,05RXPCPX!s@$X!s@,Y,05RZPCPZ!s@$Z!s@,[,05R\PCP\!s@$\!s@,],05R^PCP^!s@$^!s@,_,05R`PCP`!s@$`!s@,a,05RbPCPb!s@$b!s@,c,05RdPCPd!s@$d!s@,e,05RfPCPf!s@$f!s@+S00,05RgPCPg!sA$g!sA-1,05RhPCPh!sA$h!sA-2,05RiPCPi!sA$i!sA-3,05RjPCPj!sA$j!sA-4,05RkPCPk!sA$k!sA-5,05RlPCPl!sA$l!sA-6,05RmPCPm!sA$m!sA-7,05RnPCPn!sA$n!sA-8,05RoPCPo!sA$o!sA-9,05RpPCPp!sA$p!sA-:,05RqPCPq!sA$q!sA-;,05RrPCPr!sA$r10D@!s?$<,05RDPCPD!s?$D%H>S0=5:>S0>!s+$?!s+$@!s+$A!s+$B!s+$C!s+$D!s+$E!s+$F!s+$G!s+$H!s+$I!s+$J!s+$K!s+$L!s+$M!s+$N!s+$O!s+$P!s+$Q!s+$R!s+$S!s+$T!s+$U!s+$V!s+$W!s+$X!s+$Y!s+$Z5:>g00JHRs#HRt%gsRsP41L42P31L45CaRu%]4Rv%[4RwPwPw%B:,G4Rx1G4:R:%?03YPwP:%?=1G49R9CXCVRy%U7R7!sU$?6R6%?@Rz57:R{%?<R|'1P9PwPxP{%?CR{C6G41Tw8R8P1P2g00K4R}g00KTR~'S1R12=Q}~dg00L4=P43COR~b4b5b6X04X14X241010AJ1=35I2R=103ARAP<P2P5PAPCE8[^04^14^24P1!s<$;P3O4R;b3PBP2P3PBC2eP>P?PFQ0ZPtPsPuPvPwPyP!u<$11zzRB97:6R1/1|!u5&1P!u2$P8P!t^53ERE!tP&EPCE8\=!tQ,;b3PF!tE$F!tE'HQ0Y!tE7B!tE'F!tE,F!tE?GRG!tE&G!tE7H!tE$H!tE'JQ0X!tE@H!tE,H!tE?IRI!tE&I!tE7J!tE$J!tE'LQ0W!tE@J!tE,J!tE?KRK!tE&K!tE7L!tE$L!tE'NQ0V!tE@L!tE,L!tE?MRM!tE&M!tE7N!tE$N!tE'PQ0U!tE@N!tE,N!tE?ORO!tE&O!tE7P!tE$P!tE'RQ0T!tE@P!tE,P!tE?QRQ!tE&Q!tE7R!tE$R!tE'TQ0S!tE@R!tE,R!tE?SRS!tE&S!tE7T!tE$T!tE'VQ0R!tE@T!tE,T!tE?URU!tE&U!tE7V!tE$V!tE'XQ0Q!tE@V!tE,V!tE?WRW!tE&W!tE7X!tE$X!tE'ZQ0P!tE@X!tE,X!tE?YRY!tE&Y!tE7Z!tE$Z!tE'\Q0O!tE@Z!tE,Z!tE?[R[!tE&[!tE7\!tE$\!tE'^Q0N!tE@\!tE,\!tE?]R]!tE&]!tE7^!tE$^!tE'`Q0M!tE@^!tE,^!tE?_R_!tE&_!tE7`!tE$`!tE'bQ0L!tE@`!tE,`!tE?aRa!tE&a!tE7b!tE$b!tE'dQ0K!tE@b!tE,b!tE?cRc!tE&c!tE7d!tE$d!tE'fQ0J!tE@d!tE,d!tE?eRe!tE&e!tE7f!tE$f!tE'gQ0I!tE@f!tE,f!tE<Q00,03Rf!tG&f!tG7g!tG$g!tG'hQ0H!tG@g!tG,g!tG>1,03Rg!tG&g!tG7h!tG$h!tG'iQ0G!tG@h!tG,h!tG>2,03Rh!tG&h!tG7i!tG$i!tG'jQ0F!tG@i!tG,i!tG>3,03Ri!tG&i!tG7j!tG$j!tG'kQ0E!tG@j!tG,j!tG>4,03Rj!tG&j!tG7k!tG$k!tG'lQ0D!tG@k!tG,k!tG>5,03Rk!tG&k!tG7l!tG$l!tG'mQ0C!tG@l!tG,l!tG>6,03Rl!tG&l!tG7m!tG$m!tG'nQ0B!tG@m!tG,m!tG>7,03Rm!tG&m!tG7n!tG$n!tG'oQ0A!tG@n!tG,n!tG>8,03Rn!tG&n!tG7o!tG$o!tG'pQ0@!tG@o!tG,o!tG>9,03Ro!tG&o!tG7p!tG$p!tG'qQ0?!tG@p!tG,p!tG>:,03Rp!tG&p!tG7q!tG$q!tG'rQ0>!tG@q!tG,q!tG>;,03Rq!tG&q!tG7r!tG$r!tG'DQ0=!tG9!tE$6!tE,6!tE><,03R~!tE&~!tE7D!tE$DC2e1N>?E3!s$_g00LR#;#M#<!s$/9f5@9e>?e%d5?c23eW8X:4X94X74o"). Qed.

(* [comment removed for export] *)
Lemma aenv_transport_pt : ltac2:(zQ "h40!h9!ja!uc!j4!v2!v8!hj8!hm0!hne!ho8!ht2!ih8!ihf!ik0!ik7!il1!ip7!itf!iu8!iue>2Pr>0$0P>2tp@1$7@1$4#k0>3TSD$0>3CTX$0>2TH$0>2sb$0>2SO$0>1T@1$9$0>4rest@1$9@1$7@1$4#k0>1m$b>2m'$b>0@9$a^a^9^8^7^6^5^4^3^2>0@3$h0^c^3^2>0@3$h1$f^4^3>0>1a$0>0@2$2@2$1$e^1@2$5^1$6@1^h0^2>0>1a$0>0@2$2@2$1^d^1@2$5^1@2$3^d+q0@1^h1^2>0>1a$0>0@2$2@2$1^d^1@2$5^1@2$3^d+8@1^h2^2>0>1a$0>0@2$2@2$1^c^1@2$5^1@2$3@2$3^c+h0@2$h2+8@1$h3@2$d@2$8$0^b@2$8@1$7@1$4#k0^a@1^h3^2>0@2$2@2$1+mpvgs8@2$c@1$4#k0^h1@2$1@2$3@2$c@1$4#k0^h1+hgg0$6>0@2$2@2$1+mpvgn0^h1@2$1@2$3^h1+8$6@9$a^h3^h2^h1^h0^f^e^d^c^a").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_MallocCold ()) ["HCW"] "#$P_p'0h01ah14__x1h27__arithh34__ffh48__varmaph55__with61Hh72H0h84__x2h94__x3h:4__x4h;1nh<1mh=1xh>4cstrh?5cstr0h@2AGhA3CTXhB1EhC4EaflhD4EcanhE4EctxhF5EfillhG4EgothH5Egot2hI4EhmehJ6EhookshK5EinithL6Einst1hM!s/%2hN5ElsanhO5EparthP4ErmshQ4EshbhR3EsohS4EthrhT7EthreshhU4EtidhV3EtphW3EtrhX4EtsdhY5EtsdihZ2Hah[3Ha0h\2Prh]2SOh^1Th_2THh`3TPRha3TSDhb3TSRhc2WMhd2ZChe2ZIhf2ZShg2ZThh2m'hi4resthj2sbhk2tphl1vhm1yi005e_afli015e_cani025e_ctxi036e_filli045e_goti056!s/$2i065e_hmei077e_!vB$i086e_initi097e_!vF$i0:!s1&2i0;6e_lsani0<6e_parti0=5e_rmsi0>5e_shbi0?4e_soi0@5e_thri0A8!s/$eshi0B5e_tidi0C4e_tpi0D4e_tri0E5e_tsdi0F6!s/%p%0p&0p;1p;9p;3p;2p;4p;6p;Pp;<p;Bp;7p;8g0013j13Tg00M1k10;!s0$Ok10!s:$55k101Tg00N2R0l9}Tg00O<k30\Tg00PDk30ZTg00QGR1j25Tg00ARj2!sY$1Xj12Tg002=j1E!s/$[R2j20!sW$cj2VTg00RCj2h!s/$ZR3j18Tg003XR4j2NTg00S:j2]!s/$dk10!t/$Tck104Tg00=4j16Tg0045j1r!s/$Uj3LTg00Ugk20KTg00VkS00j1[Tg00Wjj1|Tg00Xnk10dTg00YLj4t!s/$hj1sTg00Zlk30^Tg00[Kk20!tL$[hk10?Tg00\lk30>Tg00]Ik40!s}$^Kj3JTg00_1j1U!vW$Uj2qTg006Qk10Y!s0$ok10XTg007Zj2pTg008=k10W!s0$_k20STg009Aj2n!s/$[k20RTg00:Gk307!s0$ak30PTg00;@k40O!tB$Ol9@Tg00`dj2gTg00aMj2zTg00b9k10!ve$63j4m!s9$Wj2QTg00c2k60!v[$c[k10!wo$d@k20I!s0$ik30!wR$Cbj2{Tg00F[k30HTg00eRk409Tg00f=k40!ug$f\k60FTg00g:k30j!s0$Ym90iTg00hlmP0!xT$j6k40!tt$k;k40f!s0$^m<0DTg00lCmB0!y6$lim<0cTg00mNk40bTg00DEj3u!s/$hj4!vr$ESj7!zH$n5j7kTg000Oj8~!s8$Yk10!z4$oak30eTf0R5#3#3p=Mf2R6f1R7'1/Q5p=S%3!s@&l%35#Ep=ef3R81075,56'Qp=9g00G>R9/V5p=^f4R:/1!sF/T%25#2#2#2p=c!st&#3p=R%2!s2%2p=W!s>'Ep=B!sV'3p=a!sJ$p=I!s:$p=Dg010JR;?L75p=oAL;759L;6p=bg011NR<P6P7P5H0gp=A%[7#s=L;5p=C%s7!s0$>0!sz$2!tR$>0`%3!t#$O%[5#sp>0_!t|+!s$'p=d!tx'3p>0C%65#6#6#6p>0B!s3$p>0A1575,Q6p=4p-0R=/n5p=GB07=75p=K1n95p=7P9P9g012PP5H0fp>0=g0134R>P9!s$$3P3f5R?P:P8!u>%N<0Dp>0<!sF&!s$%2P5P7P6P2P8P:P?f6R@f7RAf8S01f9S02NB00p=!s[%1PAP1P@P!s{1cp=;!s;%158!s;$J06p=?1Q:!sK&H0bp==1{95p=:P8g0000R1g00HCRBPBg00HcRCP9P6g013SRDAu975CYg00ICREF\p=HP9P7g00G\RFP5CYp>0VP6P1PBPBPCP9P7PDP5CYP!sT$_P8!sA+!sK,7PEF\P5Fkp>0T!uA$!s>%@!s0+?!sw-:PFP8!sw%P6FkP7P5G~p=>&0E5#8,07,56,Q8p=FB0e975p=`1{959u97p=X!tj2F!tj,j!uS$p=i!so%p=yP9P6P!uj'p>0M!u407!s2+5PEF\!u4$@P!xT-!wU,1n9!xT%=Z!v0,p>0L!sw2!u?$x!z:+!s$'p=w!s:4!s$3p=f%37#3#E=L95p=PAL9759L96p=vP>!s$$9!zY&4:!tm$3P2g014Z!yM0B00p>0J!zJ04!zJ&4!zJ%P@PAQ01Q!zB&>0:!x:0!x6%Q!x6::!wE-8PDP6!wE%!x6+>0GP=\9g00IcR=#3RE#3S03#3RD#3R1#MR4$0;R2$03R3&019&013g015=S04Q04Q02Q01PA!{t/M9}f;S05@0\67B0Z<86g016@g017DRF,557S5f?S06P7O1[^09f<S07/15RGP5Q07%2ERH#lRI#3S08#eS09C9f@RJ!sV'P!sN&EDRGC9fAS0:!sA'Q05P5P5Q05%E1R1'0f:S0;#^Q02,V3'h#8,NGDTfBS0<!sZ'%2=RK#3S0=#2RL#MRM#2#c#RRN#2#W#BS0>1]2JRO%34#RR4#3RP#ERQ,0O/1F3S%3N#a#BS0?10JG/1F7SJP0Q0<Q0:PJQ06f>S0@f=S0AQ07Q05Q0;fCS0B!sI-Q0@Q!sE&;M9}Q01fQ%2LRL#2R0#IRF#3#W#D!ta$M#BRO%E=RR$05$04RSg00LRS0C#6S0D#6S0E#6RT&0;D$03RUg00L4RV$05RW%rU9LUW9LUW3L+0KRU%[VRX#|RY%r;RZ'oR[3bS0F3AfRfZR\,]2%2HRH#l$0dR]'0fYR^/CZR_3AfS?A\_fTQ03#2R`#2#BRa,0\;A_fUf]R_,]2/01;A[fV%3LRL#3#IRb#2#D#a#D#BRc%[1Rd00aZS0G3AfWf\Re1C_Z3AfXf^Rf/0G;A[%2FRF#D#WRg#3!s_$h1oSZRi5A^%2D#c#W#D$0`#BRD&04WRW1oWZ7bSS0H5A\f[!wj%eRN;Ai%3b#O#I#I!so$bP9P;&0_5Xl9S0Ig018ICtS0J5Ae%lF#I#c#BRF%2KRe#2S0K#c#dR\#R!s$$B/CZS0L5A_%2gS0M#3S0N#3#BRg%2\#D#c#d#d!sW$E%sXRX?bXZ'CS0O5Aff_%M`#DS0P#2#O#IR`#W!xL$f%2\!s^$E!t,$Q3Af`%2L#R#DS0R#2S0S#3S0T#l#BRL%OM#M#c#O#M!t^&U3Afa%30R0#I#WRM#2R\!sE$I#eR_%[Q#|%2H#D#e#[#|/oZ7bYS0V3AfbS0W%2\#M#D#O#ER\;AifcS0X%3`S0Y#3$0C#BR`%6TS0Z$0BRY$0AS0[:0^;XS0\3AfdRX%30!sg$W!w%$0fhRH/CZ3AfeRW%3MS0]#O!sA$M%EE%EI+0]&0?d%E4#[$0?AbSUZ3b'CS0^3AfffiRU10U1%^H#8/CZ'C3AP<fgR<fjRS/01P9P3Q00PUCt>0>3HH0[fpR4foRdfnRIfmR^flRjfkRkPSPUP<fqRlPHP<PWPXPOQ0FfFS0_11O5Rm%8YRn,0ORo745PWP711O7Rp157oRq10OGRr94p7RsPpPqPpP7P5X=9RqPGO1Rt,0ORu%Gp1Kppe9JppPq1575#UXm9X=9RpP7P7%77RvPoPuPqPqPq1075$0=#7X<9X;9RuPOPO%7OPnPtPqPq%85#7X=>RoPYPG%7GS0`J0<RYM:<G;F?P5D=Psg00JHRs#rRw&01sRx1q97Ry&0Y9Rz&0X9R{P{P{%:OR|1p9=R=P{P=P|%:GR|CH&0WBRB!sH$3P#BS0a#:00V=%le#W#I!{U%Re#:S0b9_{=H0TRPG>20S{CRCP5P6g00K4R}g00KTR~'n20R56>07}~dB0P9V7H0OR~b3b4b5X19A4m5rQ0a157e7S7Rr[^19P5P8P7O2R}b2b7O2W6X09PmP5!wl$CFfsS0FP7O1RO[^09RmePmeM9@P!x=+1]24S0c/0]1CdZS0dfES0e1]2lS0f/0]S0g/15S0hP5Q0gPnC9PWP7frS0i,]2S0j/0]Rm/17S0k10mnS0l,57S0mQ0kP7PmPGC9S0nQ0kQ!s:&10mt!sF%#U!y$&7PvQ0lQ0m!xO%PuPmPm%7m!x@$!w}/Q0nQ0Z,g!sy%E,g9Q0C,g9Rm'`'`g019RS0C'z1g9TS0EQ0D,g9/`mS0m'`Q0C'z=Lsw5LsS0lPxP91q96S0kP7&0N9S0oCmS0pPzP!xi$1p9ERE/X]RmP!xk%mP|CHP!xd$P{Q0>#:PE1XEQQ0b5j{PBPPG>S0qG>PCP!x$,X89107]R]P5P5P]PGDTQ0>106Q/1e7S6!xC$6e7S6S0a[S0>[^19^89P5ftS0r,]2P8P7Q0XO4S0s!xW-Q!w\&1C4ZCFP!xQ%2eP2!xQ1Pd1CIZS0gfDS0h1145S0tP5P4!x<'11l7R210lnRQ,57R]P2P7PlPGC9RmP2P!s6$10ltR]%U2!wz,PQP]!wx+lPl%7l!wx4PmQ!w1%Q0oP7Q0kCm!v~-KRmP=1im|R]9_{=!vy,?#:PmQ0b9j{]!vv%!vs8GS0b,559S75Q0?106G!vq+[!vd+Q0F!v_%WO4!v\0!u{$Q0d#yS0dC9!v_&eePe!|220Ia1C^ZS0tQ0B10daRe!{{$FP5Pe!vd$XP7104aR]/17RQ10]nS0a,57R2PQP7P]!{m%?PQP!s7$10]tR2%UQ!{g/aP2!vl+]P]%7]!{f6?PwPxQ!zc-X=aR]PEP{PEP]!z^'Aj{=ES0?P{Q09#::0ME=H0@S0a!ve75aRa!tS$aPGDT117!{z$6P7Q09C9S09!vi+P8Q0iP7O3S0i!vi0!v$$Q0g!zE+!vd5Q0c/01P[Q0<Q0f/01S0f!vd$cP5Q0fQ0Z#8Re!zP%Q0j/01Ra/17R]10aeS0j!vl%]P7PaQ03#ERQC9S0F!z\$]P7PqPQO1R2,0aS0u%U]!vy/jQ0u!vz+aPa%7aPe!w5&oQ0ZPQPQEZS0Z!w20F!zy$!w3-%:1S0l,iERa!~p&a%:QS0FCHPBQ!~W:1S0q!#H4$qPQ!~Y$!vm&Q!~'2!u~%%y[S0f!zL+aePa!~,2cQ0GQ0:11c5S0c10cnRa!#<j'c7R]157aS0s10cGS0>94]7S0uP]Q0sP]P710ctS0s%G]1K]]e9J]!vI-PaQ0s!vH+cPc%7c!zD6uPwPxPy!v6,c!v0,!zB&P!v'2Q0cQ0>745P!#:X$}!ur3!uN$!yV+cePc!un2^Q0gPJ11I5S0gP5PIPnC9Q0XP711d7Rc10dnS0X,57Ra10dGR]94c7S0GPcPaPcP710dtRa%Uc!y1/XPa!uf+dPd%7d!uf6G!}+0Q0?P{1i=|S0G-0LEH0@RaPBPaCx!|k6GRa,579S57Q0kQ0b746!|^-PlP7O3!v&0!uR$Q!#4@,!v&510IGP[Q0611]5S0dP5P]Pe!#46'GR[/1!v0$[eS0g,57S0bPcP7P[P!|D$!y[$!s8$10[2S0b!v32gQ0b!v4+[P[%7[PeP2Q!|/2X!#4;1Q0G!#48$!z`$!{|&!#3y5P!#3u&!{v$9!{v+!#3Z0!uL$Q!{r-]eP]!y&2hPiQ0@11h5R]Q0D#8RQ,0h!{v-h7R2157aRe10hRR[9427S0fP2!~^$7PqPRO1Re,0hRc%G21K22e9J2!#;+-aPc!v&+hPh%7hPQPe!#3B&DPRPREZS0D!v90f!|03hRc!|0&c%:RS0f!|48A4]5[!|06P]P5Ph%yiRh!v,?DQ0HQ0A11D5R]%8TS0d,0DR[!v,+D7Rc157[Ra%EKRK,0DR2!|4%i!|4'PqPKO1S09,0DRa%Gc1Kcce9Jc!y8-P[!|D-DPD%7DQ0dQ09!v4%PTPKPKE!yC1i!v03DRTP=1XTK!#>9%!v&72!v&;DQ0H!#33'DePD!v$2NPiQ0711N5RD10NQR]!uz+N!y%%]RT10NRRK9427RaP2PT!#@v$NeRT!xy:]PT!um+NPN%7NPQPeQ!xj0Pa!u_3N!#5s+Q!xf<D5K!ub7DP5PNP!xc,NePN!ua2bQ0JQ0511b5RNQ0[$0ARD$0BRK#wRa#w#f#f#fRT!s0%S0[#8S0H,0b!v2-b!v2&S0iQ0K#BR[,0bRc!|<%KP2Q0i!|=&[O1S0i,0bS09!vD;!xw'qPuPbPb%7b!zV$i!|B'[P[P[!y52K!vT3bR]P=1X][!y5<N5c!vQ7NP5PbP9P;Q0IQ0P#M#D#RR;$0CQ0T#DRc#IQ0Y#IR]#I#IQ0]#2#aQ0N#2#BQ0M#2#MQ0R#O#a%McQ0S#2#M#I%3]#a#e%O;#I%r9'P5vR'P'P'P9vgL'P5vF!s5%'PCt!zX'e!t[%Q0J!s8+!x&1FQ0LQ0;11F5Rb10FnRN!wZ+F7R;157NR]10FGRc94;7R[P;P]P;P710FtR]%G;1K;;e9J;;!wH-N!#Hg,FPF%7F!#Hg4[!w73FR[!ze&[!#=Z9A4b!w99bP5!uA$!}H+FePF!ua2gQ0OQ0211g5RF%8aS0L,0gRb!uf+g!#4J$bR[Q0=#3R]#eRN,0gR;!#4P$=PcP[!#4P%NO1R[,0gR2!#4O9b!#Gs,gPg%7gQ0LP[!z@%PaPNPN!z?2=!v-3gRaP=1XaN!z?<F5;!v+7FP5!ud$!v++gePg!v+2fQ0QQ0111f5Rg10fnRF!v#+f!xg%FRa10fGRN!xg+a!xg%ftRa!xg:F!#7>,fPf%7f!xgFf!xgFg5N!ua7gP5!uA$!ua+fePf!ua2LQ0UPA11L5Rf10LnRg!u`+L7RN157gR[10LGRa94N7RFPNP[PNP710LtR[%GN1KNNe9JNN!u`-g!x;&qPuPLPL%7L!u`5F!u`3LRF!u`&F!u`<f5a!u`7fP5!u@$!u`+LePL!u`2_Q0VP@11_5RL%8DRf,0_!#?r,_7RF157aR[%E]R],0_Rg94F7RNPFP[PF!{@$]!{@%_R;%GF1KFFe9JFF!#?u/;!uo+_P_%7_Pf!{?+DP]P]!{?0PN!u{3_RNP=1XN]!{><L5g!uy7LP5!uY$!uy+_eP_!uy2\PiP?11\5Ri10\QR_!ut+\7RL157_Rg10\RRR94L7RNPLPgPLP710\eRg%GL1KLLe9JLL!ui-_Pg!ui+\P\%7\!#<e5!u^4\RN!x[&N!#<e<i5R!ua7iP5P\!#<e,hePh!u`2`Q0\P:11`5Rh%8TR\,0`Ri!ue+`7RR157iRNQ08#ERe,0`RQ94R7RgPRPNPR!x]$eO1RN,0`R_%GR1KRRe9JRR!ur-iP_!ur+`P`%7`P\PN!#BF'ePe!x]1g!u}3`RgP=1Xge!x]<h5Q!uz7hP5!u[$!x]+`eP`!u{201CjZP81105R`100nRh!ux+07RQ157hRg100GRe94Q7RTPQPg!#XQ$0tRg%GQ1KQQe9JQ!#XZ,Ph!x_-0P0%70!~;5T!u_30RT!x^&T!~;<`5e!ua7`P5P0Q0!#=N'R0eP0!ua2MQ0^P611M5R0%8KR`,0MRe!ud+M7RT157eRY10M1Rt94T7RnPTPYPT!xX$1O1RY,0MRg%GT1KTTe9JTT!uk-e!uk-MPM%7MP`PY!xX&KP1P1EZRK!uy/n!uy3MRy!uy&yQ0l!uz:05t!uz70P5!uZ$!uz+MePM!uz2k10k1RM%^SR0!#mr%P711j5R}P5PjP`C9Q0!v,$^7Rr10^1Rt%^jRP1V3kRy'hRn#8Rg,NGRe'0RT,57Rh'QRQ%8PRN%8yR\'0R_,NGRi,0tRR,57RL,QrR]PrPhPrPL%UrRD!vT-TPR!vT+tPt%7tRRPeP!#EB$q1N!#mB0iPGPGQ0`Pg!|e&oPnP_PP!#IB$yP\%7\J0JJ0<R\N:0:!w4$J06RNPr10^`RP,57RnA4r7tRoPrPnPrP710^YRrP!te/PPr!te+^P^%7^!x;$!x,0o%^^Ro$02RK%8o,1VRo1V3^RY$02R`%8Y,1VRY20I9GRrQ0n6089Q0E:089rQ0m'`!#iJ,PxP9P91q9:P6Q0oCmP71q98CmRsPzP{1{9VRrQ03,p9RP!#h{${Aj{rm!#eJ$Q0?!#Tf$l,i=R=PB!s7&P=1imP:0H9|CHR|60Q{RPL0GCx!#X:4X99X:911V8RVP6P8P8P6P1DTP8P:P:108110?@,NGDT[\V!#UK%^99^:9P51V3d#8RV%^4#8RmP?PlP7P6P8O7b2b?b>b7H09!zj'!z+$10j1R}%^kRr!zJ&!zy+OePO!}u3!#uL&SCtRM>0>3URXP5P>1V3MRW1V3U'h11t5RHP5Pt%87,NGC9Q0r!#pN+X;>P>P0P!sH$1h7y#8!sK$P!sD+}P5P5P}1V3S,hr!$%v%!{y$PQP]PN11t7RNPh1QNLRLPNPhPN!~|$_O1!{^%h,0tR]%UN!{J0]!{J/PRPePh!s8&!{80!zr,!yy&LPKPo!z8$wPxPs!#30&P=PEP|!~|6!x5,051R1!tN$1106!u?'kP6Q0q108:!uo$!x32PVP!x$%8O5!w|&[!w|%ZX09PW!wI+H0UJ0F1V3XB0j3MUJ0FN90iNP0hP4PdPIP^PjP!#yt%M9}eWWWRWMWLWJWOWFWPWTWIWQWGWDWCWKWUWSWHWNWEWXWVWYQ0_Q0eQ0hQ!$+e:5Q0;!$0]6P5OGn90!s#'1!s,&G110F10C10E10210;10510@10B10810010110410>10610A10=10310<10710910:10?10DWbW`WfWgWdWeWcW@WBWhW<WiW^X]9Xj9X_9XA9Xa9WkW\o"). Qed.

(* [comment removed for export] *)
Lemma poisoned_visible : ltac2:(zQ "h40!v2!hm0!iv7!h9!il1!jg1!ihf!jg7!jgf!uc!jh6!jhb!jl8!ih8!jm1!itf!j4!ja!v8!iue>1m$d>2m'>0@1$1@1$0#k0@1$2@1$1@1$0#8>1A$3>1k$8>1v$3>1x@1$1@1$0#k0>0@4$e^6^4^3^2>0@3$f$4^7^6>0@2$9@2$h1@1$5^6@2$6@1$0#k0^3@2$h2@2$6@1$0#k0^3@2$h0@1$5^6@1$h3^5@1$b@3$a@1$2@1$1@1$0#8@3$c$4^8^4@1$7@1$1@1$0#8").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_MallocCold ()) ["HCW"] "##>{h02W3h14__x1h24__x2h31ih41Hh52Hah67__arithh74__ffh86__sat3h9!s/%4h:!s/%5h;8__varmaph<5__with=4__x3h>4cstrh?5cstr0h@1AhA2HAhB2HBhC2HMhD2HWhE2HxhF2W1hG2W2hH2WMhI1bhJ1khK1mhL2m'hM1nhN5nd_i1hO1vhP1xhQ1zp;1p;4p;3p;2p;6p;8p;7g0013j1;Tg00M1j1Q!s/$Oj1JTg01:>j1W!s/$`j4oTg00PDj3hTg01;hj11Tg00S:j28Tg00ARj2=Tg00RZj12Tg002[j23Tg00QGj26Tg00bWR0j2:!sC$=j1CTg01<jj2BTg00:Gj3<Tg01=Jj25Tg01>Vj4LTg008=j1MTg01?Wj4K!sy$cj27Tg01@[j4ITg00[Kj2[Tg01A\j19!ti$dj1ZTg00Zlj3YTg01BZj3XTg01C<j6H!s/$Xj2@Tg00c[j1ATg01D5j2V!s/$]j3UTg01EAj3GTg0045j1TTg0055j1S!s/$Uj2FTg0063j4E!s/$Qj1R!s/$oj1nTg007Zj2DTg00Dhj4?Tg001Xj1m!s8$Ej3OTg00Cbj2lTg01F2j3kTg000Oj8g!ur$_j2fTg009Aj2e!s/$[j2`!vP$aj3aTg00;@j4b!w#$9j1_Tg00f\j6c!sw$Uj2dTg01G;j1^Tg01HMj6PTg01IRj3]Tg01JOj1\Tg00ESj7iTg00n5j7jTg00L4R1f0R2'=p=0f3R3g011NR4f2R5f1R63];<2#\p=4P6g0000R7g00HCR8P8g00HcR9P2g00ICFip=>P5P7P8P8P9P6P2Fjp=Ng015=g00IcR:#;R;#;#;R<#!s-%=#QR>#JR?%Q<#JR@#WRA[g00G>RBg0134RCf5RDP3P5P6Cof6RE=h4D%1DRF18>5RG'=f4RH#2,3F,6G':%0ERG%C<R<,BE=<B1P4f8RF%1E15DHCLPAf7RHP3%M@RDC41BH<!sL&:RI%1F15HECLP0P4f;R0f9RE#1RJ15FHRKCKP4P0PJ17@K#2CIPAP0PHPDC4P2P4f=RH%1015IECKP4f>R4f<RE#1150I,7@!sX$FPI%1HRF#0RK15E0!s>$,3F%C;RF%C=R='[R0'=%02RJ15HE!sG$RE,62':PAfARHf?RL#1/36#9PDC4[^3BPAPLPIPDC4%14/3E/=015L4!t'%62,:JPAfCRE%1HRI!s`1C%Z4RM=Y@L,7@%26!sU+ERN%1ERO!sU0XMCP2PLAX@MLEHf@RM#2RC!sZ+DRJfBRP#1RQ!t41218>4/@IRR%AM%0C15HM,7@RC#A%2C#01VF=RC161F%0=1610[[RS%0FR!z}$hRUAUF=6UW5R=%00\U^5TRTAGN<4%0<R4fFRU/B<#0[g00JHR0#TRF%S0R0PB1FB5RVP61FB3CE%RBRW%nBRX!zg+B1DB;R;g00G\R71DB:RYC?,>XPBPYg013SRZ%m:,DBR:9OB;!sB$5NX%M8PB1lB1P7AkBY;R7!s\'7PZP:!sM'Gg1fX9R9P2P5g00K4R:g00KTRZ'e1`25=<:ZdAaB16CbR1b7b;b<X1BX2BX=B1=621365!xm$1@65RZ#016Z3':[^1B^2B^=BP2%2UfGRZ#118>JPHO4b6b8b9b:b?b>O2PAPE13IR!wW%%AH%2H#015PH,7@R@#A%2@#0PCPSP=PTAGU<L1BZ<#0\4PFP0PBPVP6%_BCEPW!v3&KDAOB;!uh&9P!u-01@26,369<B2!tr%P2fH!tj$NO2!th/18>LRL1@LQ,3Q5<BPB18>MRM/@O,3OPAPU%92PDC4XQBP6PMP2EcPAPN%9M!}'$?18>H,d>PAPZP!sO%I?P2PH%^HEHPAPU!}T'b0b0b4b0b0W0WGXFKP2EPO2WDWBP6P2O2n20010!s#$12!s/&W4WCXAGP5EPWEWHWNXP?XOBWJW@WLWKo"). Qed.

(* [comment removed for export] *)
Lemma in_window1 : ltac2:(zQ "h21!v2!hm0!ja!jmd!h9!jr0!j4!v8!ihf!jr6!jre!js6!jsd!jt5!uc!jh6!khc!kia&@2$3@1$1@1$0#k0@1$1@1$0#k0>1x@1$1@1$0#k0>2lo$4>1n$4>0@2$2Z^2>0@2$2Z^2>0@2$7@2$6^4^3@2$h1+2+k0>0@3$f$9@2$h0^6@3$a~0@4$c@1$1@1$0#k0@1$1@1$0#k0@1$5^5@1$5^4@1$b~0$d@2$e@2$2^6@2$8@1$0#k0^7@2$7@2$8@1$0#k0^7@2$6^6^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_MallocCold ()) ["HCW"] "##?:h01Rh14__x1h24__x2h31nh41mh57__arithh64__ffh78__varmaph85__with91Hh:2Hah;2R1h<2R2h=6__sat1h>!s/%2h?4__x3h@1zhA2H0hB2HhhC2HnhD!sI%3hE!s/%4hF1bhG2lohH1xp;1p;2p;4p;3p;6p;7p;8g0013j1:Tg00M1j1o!s/$Oj1\Tg002[j22!s/$=j1NTg00[Kj2_Tg00QGj23Tg0038j2[Tg00Vkj1BTg00CBj4CTg0045j1O!s/$Uj3@Tg01Kkj2HTg00S:j21Tg01M6j2RTg01NAj2P!s/$^j3`Tg01C<j6?Tg01Onj1]Tg01FUj2MTg01PMj27!s/$jj24Tg01QGj2>Tg01D5j2Z!s/$]j3YTg00=4j1DTg00`dj2;Tg00oaj3<Tg00aMj2LTg0055j1X!s/$Uj2KTg00b9j1WTg0063j4J!s/$Qj1V!s/$oj1UTg007Zj2GTg00DEj3E!ur$bj2I!t^$ej3nTg008=j1m!s/$_j2lTg009Aj2k!s/$[j2dTg00:aj3cTg00;@j4b!tL$WR0j2ATg01RHj2QTg01SSj3aTg00ARj26Tg01T6j2e!s/$Vj2fTg001Xj1^!sy$Gj3g!ti$hj4STg00ESj7hTg00n5j7iTg000Oj8jTg00L4R1f0R2'6p=9g00K4R3g00KTR47g2p=0g00G>R5f1R6g013SP2CSp==P6g0000R7g00HCR8P8g00HcR9P2g00ICFhp=8P5!sM$G\!s[%Ff2R:P7P8P8P9P6P2Fip=Tf3R;!s;+:P6P2Gjp=5g00IcR7#:R<#:!s$'R=#oR>#\R?%96R@12;:%N<RA%N=R='_RB'3f5RC1[??RDP?P?f4RE#BRF%B;CC%ODRG3@'H#0P3f6RHP?P?%BCRIPFCCRF=@DG'H%02XF3RDP211>H/RF1HHG'PRJA`HFGE?%0JP3f7RJ,1>!sg%HPICC'RRIg01U6'PPDP2PI%]IE?%0IP51M>J,1>RIf9RD,1>R?,72122I,4?'>#0X@5P2PJ1ZA=RF131A%9=131B[[RG%9ARKg01JhRLAYA=6UW:R=%9B\L^:KRKg00JHRLg00LRRM#DRN#DRO#D,;5RP1;5O1;5MRM5<55<5g019RRO'L%OLRQ3@%XLRRP51K5:RSP6%W5CJRT%V5RU%U5RV1G57RW1G5<R<5E51I5A=n5>RA'=,8V%m8R8PV1I51RX/F<,8VRYP8PV1FXW,8VRXP81=WA,8V9TVXRZC5C5C51lV9R9P2P:1k341d2:#0dAc516CbR1b6b7b8X15X251226/3B%9:R4%9;R313;B'AR[\4[[^15^25P2PDf:R4PHPJf8R\O5b5b=b>,QJE?11>\R],7J1M>H,1>,2J,4]'>#0P5PI11>4RI,7DR]12D2,4I!wR-PFPGP=PK1;5N=<5M9<5P/LO=@LQPRPTPUPVAE5<W/=A,8VP8PVPX!s+$YP8P!u_&P9P!uE262/3BP[\3\@!u6+f;R3P4PJP\PD!u417\?12\J!y;&12D\,4IRI=a]2%0]%0I'AP011>3RI,74#0124D,4I#0f<RI,1>RD,631234,3D'AP2f=!z<$,7I#0f>,1>12DI'4#0P01762#016:6[RD166217:6#0RI[16;:\I1e62P6n20010!s#$12!s-%0X45X35PD^45^35P2f?RDf@!tN%3P:O316D3P014!t/$3:6[R0136214!t/$3[13;:\31f!t/B0!t/+B,1>R0fA/2IRIP;O3130I!wv'PQPRP5PSP61K5;CJPUPV%^7,G59E5W,=!zc$7!zc%W!s3$<P8ATV<7!wx7X?5122:,36166:16:;12:E,3;'A!z?'^?5P2fDfF,1>fEP;PC!x3$DbEb<b9b;b9W<W;P6P2O2!uU0!s/&b!s$+W0WBXC@WAX35XG5WHo"). Qed.

Lemma in_rangesb_if : ltac2:(zQ "92!v2!hm0!jr6!jmd!ho8!jt5!jh6!khc!js6&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>1x@1$1@1$0#k0>1b$2>1l~1>0@3$6$2@2$7^3M2\1b$2~1^2^1@1$8~0$5@3$6$2@2$7^4^2$5").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_MallocCold ()) ["HCW"] "##'+p'0h01lh11Hh22H0h31bi001bh41eh51xp;1p;2p;6p;3g0013j11Tg00M1j1:!s/$Oj14Tg0038j23Tg0055j19Tg0045j18Tg01Kkj20Tg01C<j65Tg01UVj26Tg00:Gj37Tg00K4R0f0R1g00KTR237p=2g00Ic#1!s$-:#4R3P01333R3#9R4f3R5P0P4f1R6P1%83R3n0110000020000'0#2f4R7/06#2[]0P1f2R6/01#2P1W1X041063#2P01053P0p-0P1g01V5R3g01Jh!su1X40g01VRP2P1E5P31076#2/61b2!ss$!sT230W5o"). Qed.

Lemma land_lnot7' : ltac2:(zQ "60!h9!jh6!kj0!kj7!kje!kk7>1x$0@3$1$0@2$2^1@1$3+7@2$5^1@2$4^1+8").
Proof.
ltac2:(KReplay.run1 (kr_t_AG_MallocCold ()) ["HCW"] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71zh81Hh92H0h:2H1h;2H2h<2H3h=1qh>1rh?1xp;1p;2p;3p;4p;6p;7p;8g001Xj1FTg002=j17Tg01Vnj2@Tg0013j1:Tg01<jj21Tg01CXj2DTg01WMj2XTg01Wmj2TTg00[Kj2OTg003Xj22Tg01XMj26Tg01Xjj2HTg00:Gj34Tg01JOj1nTg002[j2ETg01YKj2bTg00QGj25Tg00ARj2<Tg00bWj2CTg01Z2j2ZTg01ZYj2YTg01[?j2WTg00Xnj1VTg01[ej2UTg00=4j1STg00`dj2?Tg01\Fj3RTg00oaj3NTg00aMj2MTg0045j1LTg004Uj3KTg0055j1JTg005Uj2>Tg0063j4ITg006Qj1PTg006oj1QTg00Cbj28Tg01\oj6pTg008=j1oTg007Zj2=Tg00F[j3GTg00DEj3mTg01F2j3gTg008_j2fTg009Aj2eTg009[j2aTg00:aj3`Tg00;@j4_Tg00b9j1^Tg00Dhj4BTg01]Sj3cTg00f\j6;Tg01^<j3]Tg01^ej1dTg01_Cj3\Tg01_ij1[Tg01`Gj2hTg01`ej2iTg01C<j6jTg00ESj7kTg000Oj8lTg00G>R0f1R1f0R234p=0P0P1g01KDP2CBp=9P1g0000R3g00HCR4P4g00HcR5P2g00ICFkp=3f3R6P3P4P4P5f2R7P1P2Glp=AP0g00IcR8#FR9#F#7R:,@2%:8R;#:#:#7R<,11R=,D1R>,02X70R?P0%79R@,X2RA/T@RBP?P0%7;/O@RC,2AP?P0162C122C/0>X701H2<g00L4R>940<RC#n161<,2</E=,01[1b1<15><117<R=,<>15=<'C[1Z7<15<>116<R=,5<1<=>'C[1Y6<f4R=/6<=40>\C1W=<f5R=/1</0=\C16=<P0f6/1<P0g00JHR=%V8,U0g00LRR?#S,?05R01?0?5N0g019R'M%L=R?3K%J=R=P01>07P11>06CI%P0RD%Q0REPEPEP3P4P4P5180<R3180>RF'9,3EEp%o4R41=0;R;1=08R89G031=09R95m0'9,3ECAP4AG083Ag0;9'9,3ECA1fE5R5P2P7g00K4R9g00KTR;'e1a27=49;dA`0>1C_R;b1b2b3X40X50X60g01V5\C12<1/E6,07[121<1D76'0[^40^50^60P2P1f8P7f7O4b0b>b=b<b;b:b9b8PAP?P=%^0PDP0PFg00G\180@CB,3EP5P;b1b2b31<>@P2b0R>9c2@E;PBA]A@>E;%d@,@2A\2@>E;%[:,h21i2:EjX?0o"). Qed.

(* [comment removed for export] *)
Lemma amodelx_hit : ltac2:(zQ "h20!h9!koc!ho8!ks5!lgf!llc!lm9!ln1!ln8!lnf!lo7!lp0!lp9!lq2!lqa!lr3!lrc!ls3>1s$h0>2mo$3>1c$0>3cnt$0>4rest@1$2$0>2ch$4>0@3$1?5HCEIL^6^5@3$1?5HCEIL@a$h1@5$5@1$d^7^5^4^3^2@1$e^7@1$b^7@1$c^7@1$7^7@1$8^7@1$9^7@1$6^7@1$f^7@1$a^7^6").
Proof.
ltac2:(KReplay.run1 (kr_t_AG_MallocCold ()) ["HCW"] "h01Ah11ch22chh33cnth42moh54resth61sp;1p;3g0055j11Tg01aIj30Tg01bQg01cVg00G>R0%10g01dLp,5HCEILf5f430f0W0W2W5X30W1W4W6o"). Qed.

End HCW.


(* [comment removed for export] *)
Ltac trp lem AG WM H Z B :=
  eapply (lem _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Section MallocColdGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).

  (* [comment removed for export] *)
  Let st : ltac2:(zQ "10!lv0$0") := ltac2:(zQ "10!lq2@1$0?1s").
  Let TH : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!lqa@1$0?1s").
  Let sb := a_sb s.
  Let CTX := a_ctx s.
  Let rz : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!qqa@1$0?4size").
  Let needed : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!qr5!j4!qs1@2$1@2$0@2$2?4size+8+8?2rz").
  Let c : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!qs7@1$0?6needed").
  Let csz : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!qt3@1$0?1c").
  Let csz8 : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!qu1@2$0?3csz+8").
  Let CA : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!j4@2$0?2TH+t0").
  Let P : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!j4!iu8@2$0?2CA@2$1+l0?1c").
  Let RI : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!qu7!j4!iu8@2$1@1$0?1s@2$2+o0?1c").
  (* [comment removed for export] *)
  Let r : ltac2:(zQ "10!quf$0") := ltac2:(zQ "10!qv9@2$0?2st?1c").
  Let nf : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rg7@1$0?1r"). Let mfa : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rh7@1$0?1r"). Let au : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rj0@1$0?1r"). Let mu : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rk6@1$0?1r"). Let fl : ltac2:(zQ "20!ho8!h9@1$0$1") := ltac2:(zQ "10!rl8@1$0?1r").
  Let n : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rq9@1$0?1c").
  Let mu' : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rr1@4$0?1c?2nf?2au?2mu"). Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!rrb@5$0?1c?2nf?3mfa?2au?2mu").
  Let au' := rf_au' c nf au mu. Let fl1 : ltac2:(zQ "20!ho8!h9@1$0$1") := ltac2:(zQ "10!rs6@5$0?1c?2nf?2au?2mu?2fl").
  (* [comment removed for export] *)
  Let st2 : ltac2:(zQ "10!lv0$0") := ltac2:(zQ "10!sh4@2$0?2st?1c").
  Let chunks2 : ltac2:(zQ "20!ho8!h9@1$0$1") := ltac2:(zQ "30!sj7!h9!qg0@3$0$1@1$2?1n?3fl1").
  Let cp : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!h9!sl4@3$1$0Z?7chunks2").
  Let AB : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!sla@3$0?3st2?1c?2cp").
  Let U : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!j4@2$0?2AB?2rz").
  Let CHI : ltac2:(zQ "30!h9!ho8!jmd@1$1@2$2$0$0") := ltac2:(zQ "40!v2!ihf!sr0!lr3@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!ho8!h9@1$0$1") := ltac2:(zQ "50!v2!lo7!lr3!svc!ihf@6$3+pgtq0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!hne!h9!iue@1$2@2$0$1?1T").
  Let id := d_putid d (depot_hash T).
  Let d' : ltac2:(zQ "10!tg6$0") := ltac2:(zQ "20!tl0!tle@3$1?1d@1$0?1T?2nT").
  (* [comment removed for export] *)
  Definition COLD_COST : Z := 606208.
  Let L2 : ltac2:(zQ "40!v2!hm0!ho8!jmd@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b5!jr6!v2!j4!hm0!tm7!ln1!ho8!jmd!tmd!tne!to4&@2$7@1$3@1$1#k0@1$3@1$1#k0&@1$6~0&\0$0~1&@3$8@1$5?1s@2$2@2$4?1s?1c?2mu@2$2@2$4?1s?1c?3mu'&M0~2@2$9?2mu?3mu'~3@1$5?1sM0~2@2$9?3mfa?4mfa'@3$8~4@2$2@2$a?1s?1c?3mfa@2$2@2$a?1s?1c?4mfa'~4").
  Let S2 : ltac2:(zQ "40!v2!hm0!ho8!jmd@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "h24!v2!hm0!jmd!jr6!js6!jr0!lt3!jre!ho8!jsd!jg1!j4!qu1!tne!kk7!to4!tm7!ln8&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$8~0&\0$3~1&@1$4~0@3$6~0M3~2@2$d?3mfa?4mfa'@3$7~0@4$9@1$1@1$0#k0@1$1@1$0#k0@1$5@1$a@2$b@2$f?1s?1c?3mfa@1$5@2$c@2$e?4mfa'?3mfa+8~3~3@3$6~0M3~2@2$d?2mu?3mu'@3$7~0@4$9@1$1@1$0#k0@1$1@1$0#k0@1$5@1$a@2$b@2$h0?1s?1c?2mu@1$5@2$c@2$e?3mu'?2mu+8~3~3@1$h1?1s").
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).   (* [comment removed for export] *)
  Let ch : ltac2:(zQ "10!lgf$0") := ltac2:(zQ "20!toa!tp8@6$1?2AB?1U?4size?2rz?1c$0").
  Let st3 : ltac2:(zQ "10!lv0$0") := ltac2:(zQ "30!h9!llc!tq3@5$1?3st2?1c?1n@2$2$0?7chunks2?2ch").
  Let sF : ltac2:(zQ "10!lrc$0") := ltac2:(zQ "80!lm9!lnf!lo7!lp0!lp9!lqa!lr3!ls3@a$7?3st3@1$5?1s@1$3?1s@1$4?1s?2L2?2S2@1$1?1s@1$0?1s@1$6?1s@1$2?1s").
  (* [comment removed for export] *)
  Let Wr : ltac2:(zQ "20!ho8!lsc@1$0$1") := ltac2:(zQ "a0!h9!jre!jsd!jmd!v2!j4!ihf!tq9!to4!tm7@3$1@2$3$0$0@4$2$0$0?2lo@2$6@1$4#k0?2sp@3$1@2$3$0$0@4$2$0$0@2$5?2TH+sm0@2$5?2TH+sm1@d$7?2lo@2$6@1$4#k0?2sp?1P?2RI@2$8?1s?1c@2$9?1s?1c?2TH?2CA?2nf?3mfa?2mu?4mfa'?3mu'").
  Let Wt : ltac2:(zQ "20!ho8!lsc@1$0$1") := ltac2:(zQ "90!h9!j4!jre!jsd!jmd!jg1!v2!tr1!ihf@3$2@2$4$0$0@4$3$0$0?2lo@2$8@1$6#k0?2sp@3$2@2$4$0$0@4$3$0$0?1P@2$1?1P+4@3$2@2$4$0$0@4$3$0$0@2$1?2CA+qh0@2$1?2CA+qh8@3$2@2$4$0$0@4$3$0$0?2AB@2$1?2AB?3csz@3$2@2$4$0$0@4$3$0$0@1$5?2AB@2$1@1$5?2AB?4csz8@3$2@2$4$0$0@4$3$0$0@2$1?2TH+qv0@2$1?2TH+sm1@1$7?1d").
  Definition mc_W : ltac2:(zQ "20!ho8!lsc@1$0$1") := ltac2:(zQ "20!lt3!lsc@3$0$1?2Wr?2Wt").

  Hypothesis HR : ltac2:(zQ "10!npf@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis AX : ltac2:(zQ "30!uc!nq9!ns2@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!koc@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!il1!oh0@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!mt4@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!nr5@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!il1!pm4@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!v2!il1!ot6!ihf@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!trc!ja@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!v2!j4!ja!ihf@2$2@2$1?2lo+rr0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!jh6!v2!h9!kje!ihf@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!v2!j4!ja!kia!ihf@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SZ : ltac2:(zQ "30!ja!uc!ts5@2$1@2$0+1?4size@2$0?6needed$2").
  Hypothesis MISS : ltac2:(zQ "40!jh6!h9!tt1!ttb@3$0$1@1$3@2$2?2st?1cZ").
  Hypothesis TP : ltac2:(zQ "50!jh6!v2!tu7!jr0!hm0@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis DCAP : ltac2:(zQ "60!j4!uc!tue!tva!ja!v8@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis FCH : ltac2:(zQ "d0!v2!ihf!lr3!jr6!jt5!jh6!ug3!uc!il1!lo7!uh0!j4!ja>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!jh6!v2!jr0!hm0@3$0@1$3@1$1#k0?2a0@1$2?4size").
  (* [comment removed for export] *)
  Hypothesis PROOM : ltac2:(zQ "50!uhf!umd!un7!j4!ja@2$4@2$3@1$2?2st$0$1").      (* [comment removed for export] *)
  Hypothesis ROOM : ltac2:(zQ "50!uo1!up6!j4!ja!iu8@2$3@2$2?2mu@2$4+2$1$0").
  Hypothesis OK : ltac2:(zQ "60!mnc!il1!ln1!ln8!lnf!or8@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "d0!v2!jg7!jh6!lta!il1!ln1!ln8!on3!os6!pha!pqe!uq6!hm0@3$2$3@3$7@1$5?1s@1$6?1s?3msF@7$9@hf$8?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$b@1$0#k0+pgst8?2fc@1$1@1$c@1$0#k0?1m@1$a$4").

  (* [comment removed for export] *)
  Definition malloc_cold_gpost : ltac2:(zQ "20!lta!ks5>4msF'$0>3mo'$1P") := ltac2:(zQ "j50!v2!hm0!uc!lub!h9!ho8!il1!jmd!lv0!lva!jsd!jre!jh6!lta!ln1!ln8!ih8!mk0!jg7!mk8!js6!iv7!mnc!ks5!mo5!mt4!njb!nk3!np7!npf!lnf!koc!nq9!nr5!ns2!oh0!oh9!om5!on3!or8!os0!os6!osd!ot6!itf!pha!pi0!pm4!pqe!pv4!jr0!qg0!ihf\4msF'$d\3mo'$h7@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3$h0\2m'$h0@2$2@5$i7$6@1$e?2sF@1$f?2sF@1$he?2sF@2$h6^h1^h0@2$2@3$c$d@3$i6@1$e?2sF@1$f?2sF^h1@7$id@hf$i9?2ra?2sp?2gp?2tp^f^e^d?2s0?2s1@1$j2?1U^c^b^a^9^8^7^6?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^5^4^3^2?1F@1$ie?2ra?2fc@1$h2@1$1@1$0#k0^1@1$j0$6@2$2@4$hd?5HCEIL?2sF@3$b@2$7$4$4@4$a$4$4?1U?4size?2LB^1@2$2@2$i0?2sF^1@2$2@1$i2^1@2$2@3$hf?5HCEIL?2sF^h0@2$2@2$i5?2mo^h0@2$2@3$i3$6?2d'^1@2$2@3$h9?5HCEIL?2sF?2d'@2$2@2$i1?2d'^h0@2$2@2$if$6^1@2$2@4$ib$6^1?2lo@2$j4@1$0#k0?2sp@2$2@3$ia$ha?1m^1@2$2@3$ic$6?1m^1@2$2@4$hc?1s?2sF?2mo^h0@2$2@2$3@1$5@1$1@1$0#8\4junk@1$5@1$1@1$0#8@4$j1$6^2?1U@3$b$h1@2$i8@1$j3?4size^1@1$h4$h1@2$2@3$i4^1?1U?4size>5kaddr$4@2$3$8\4st''$8@2$3@1$5$9\2ev@1$5$9@2$2@3$c@1$h5@2$7@2$7$4$8@1$5$9@3$h8?2st?4size^3@2$h3@2$7@2$7$4$8@1$5$9@4$a@2$7$4$8@1$5$9@4$a$4$8?1U^2^1@2$hb^2?3st3").

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.

  (* [comment removed for export] *)
  Let RQ : rq_rz (compute_req size) = rz /\ rq_needed (compute_req size) = needed /\ rq_primary (compute_req size) = true
           /\ rq_size (compute_req size) = size /\ 16 <= rz <= 2048 /\ size + rz <= needed /\ needed < size + rz + 8 /\ 8 + rz <= needed.
  Proof.
    pose proof (rz_size_facts size) as (RZ & _). unfold compute_req. replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.ltb Z.eqb].
    replace (round_up (Z.max size 8) 8 + rz_size size <=? kMaxSize) with true by (symmetry; apply Z.leb_le; subst needed rz; lia).
    subst needed rz. unfold round_up. repeat split; try reflexivity; Z.div_mod_to_equations; lia.
  Qed.
  Let HC : 1 <= c <= 30.
  Proof. subst c. apply class_id_le30. ndestruct RQ as (_ & _ & _ & _ & A & B & _). unfold kMaxSize in SZ. lia. Qed.
  Let CSZ : 32 <= csz <= 65536 /\ needed <= csz /\ csz mod 32 = 0 /\ 8 * csz8 = csz.
  Proof.
    npose (class_size_table_facts c ltac:(hci; lia)) as (T1 & T2 & T3 & _). subst csz8 csz.
    pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; ndestruct RQ as (_ & _ & _ & _ & A & B & _); lia)). subst c.
    repeat split; try lia; Z.div_mod_to_equations; lia.
  Qed.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PURE := refill_pure s m c R HC MISS.
  Let NR : 1 <= n <= 8 /\ n + n = max_count c.
  Proof.
    pose proof (max_count_facts c ltac:(hci; clear - HC; try acb; lia)) as MCF. clear - MCF; try acb. subst n; unfold rf_n; destruct MCF as [M1 M2].
    destruct (proj1 (Z.even_spec _) M2) as [k Hk]; rewrite Hk in *; rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Tactic Notation "bands_as" simple_intropattern(p) :=
    (let X := fresh "BX" in
     lazymatch goal with B : hidden ((TH + 4096 <= 65536 \/ _) /\ _) |- _ => pose proof B as X; destruct X as [p] end).

  Theorem malloc_arep_cold : ltac2:(zQ "70!mnc!il1!qk2!qo3!lta!ks5!qp4>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
  Proof.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay whose
       first error was `Illegal application: the term "and_elimF6"' (As:210 / Bs:196): it
       destructured amaps_in_ledger's SIX conjuncts at their PRE-RESTATEMENT shape, and that
       definition's first conjunct is now guarded by a non-zero ledger-word size (As//Bs
       AllocRep.v, same series).  The proof is written out as plain text; the STATEMENT IS
       UNCHANGED and no other item of this file moves.
       Structured after a donor tree:projects/openssl/echconfiglist_parser/proofs/
       lib/As/AG_MallocCold.v:229-615 -- the same theorem in the same Section, already plain
       text there.  The two places that touch amaps_in_ledger (AIL here and AIL1 after
       AMODELX_mat) only ever use NOV/NW/NWA and discard IL1, so the restated guard is never
       discharged and the donor's shape ports unchanged.
       Every literal is THIS tree's own, read out of its own interfaces in
       a farm round: AIMG_LO = 65536, AIMG_TOP = 7417856,
       AHI_LO = 17594333495296, ASHADOW_BASE = 2147450880 (so sh AHI_LO = 2201439137792),
       kSpaceSize = 2 ^ 37, and the depot slab is 8 * 32768.  Where a pc or a frame word would
       otherwise be transcribed, the goal supplies it instead: the return address handed to
       refill_sreach is left to unification and the five cold-frame facts are transported into
       their own goals, so the donor's 1706468 / 1687924 / 1687204 / 1852660 / 1852768 -- ITS
       addresses -- appear nowhere. *)
    intros K.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct AX as [AWV FXR]. destruct AMX as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0). destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof (ienv_of_arep s m R) as IEN. rewrite <- TP in IEN.
    assert (UNW : rw_cells asegs m (TH + 3168) [C1 (b8 0)]).
    { pose proof (proj1 HR) as RR. destruct RR as (_ & _ & _ & THR & _). destruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0). exact U0. }
    destruct (refill_cells_of_arep s m c R HC MISS) as (q0 & q1 & q2 & q3 & PC1 & PCJ & FAM & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    pose proof PURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    fold st in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ. fold r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ.
    fold nf mfa au mu fl in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ.
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ sb mod 65536 = 0 /\ 7417856 <= CTX /\ CTX + 160 <= aceil /\ 7417856 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 7417856 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7417856 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s /\ aceil <= lo /\ 1 <= c <= 30
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
      assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
      pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as T2e. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; clear; lia)) as P2e.
      pose proof (aapp_env _ _ X2 ltac:(clear; lia)) as X2e. pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
      clear - Y1 Y2 Y3 P1 P2e P3 T1 T2e T3 X1 X2e X3 TCX G10e G11 G12e G13 LO HC E1 E2; try acb. unfold TH, sb, CTX, P, CA, RI, a_ri. unfold a_sb in *.
      acb. unfold AHI_LO, AIMG_TOP, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; (first [clear - T2e T1 Y2 Y3 Y1 X2e P2e G10e G12e TCX LO HC E1; lia | lia]). }
    assert (BANDS : hidden ((TH + 4096 <= 65536 \/ (7417856 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 32768 <= 2147446784 \/ 17594333495296 <= d_sb d))).
    { split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
      split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
      split; [exact (aapp_lit _ _ G10)| exact (aapp_lit _ _ G12)]. }
    assert (BDJ : (TH + 4096 <= sb \/ sb + 137438953472 + 4096 <= TH) /\ (TH + 4096 <= CTX \/ CTX + 160 <= TH) /\ (CTX + 160 <= sb \/ sb + 137438953472 + 4096 <= CTX)).
    { clear - D2 D3 TCX; try acb. unfold TH, sb, CTX. unfold disj, a_sb, kSpaceSize, kPageSize in *. repeat split; lia. }
    pose proof BDJ as (BDJ1 & BDJ2 & BDJ3).
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@malloc_head _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d
                ATSD CTX TH (a_top s) (a_bot s) CH sb (wz (if as_cache_inited st then max_count c else 0)) rz needed c CA P).
      - constructor. repeat split; reflexivity.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZ.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold kSpaceSize. clear - BDJ; try acb. lia.
      - constructor. unfold kSpaceSize. unfold disj, kSpaceSize, kPageSize in G1, G2, G3, G4, G5, G6. clear - G1 G2 G3 G4 G5 G6 G10 G12 BND; try acb. unfold TH, sb, CTX in *. unfold a_sb in *.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      - constructor. unfold AHI_LO, kSpaceSize. acb. clear - BND; try acb. lia.
      - constructor. clear - BND; try acb. lia.
      - clear - BND; try acb. lia.
      - exact FCH.
      - exact Ha0.
      - exact IEN.
      - exact MI.
      - exact ST.
      - exact PC1.
      - exact UNW.
      - exact DEP. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a4_1 & a5_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & jk & j8 & rest & m1 & VIS1 & MU1 & WM1 & MI1 & AEN1 & LR & TRNG & NRT
                     & ST1 & FRC1 & AFR1 & FRA1 & FRB1 & FRM1 & PC1' & UNW1 & DEP1).
    pose proof (munch_agree _ _ _ MU1) as AG1.
    assert (Z1 : forall a, a < lo /\ a <> TH + 3168 -> outside [(lo, bv_unsigned sp); (TH + 3168, TH + 3169)] a).
    { intros a Ha. cbn [outside]. clear - Ha; try acb. repeat split; try exact I; lia. }
    pose proof CSZ as (CS1 & CS2 & CS3 & CS4).
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ Z.of_nat (length (wlist (rev fl))) = nf /\ 32 <= csz <= 65536)
      by (clear - U1 U2 U4 U5 U8 CS1; try acb; unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset in *; repeat split; lia).
    name_bands.
    pose proof (conj BND (conj BR BDJ1)) as BB. pose proof (conj BND BDJ1) as BD1.
    assert (PCJ1 : stk asegs m1 (a_cache s + PCLASS_SIZE * c + 16) (a_cache s + PCLASS_SIZE * c + 80)) by (unfold a_cache, OT_CACHE, PCLASS_SIZE in *; trp stk_transport_pt AG1 WM1 PCJ Z1 BND).
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (a_cache s + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (a_cache s + 80 * c' + 8) [C8 cs]
                                              /\ (as_cache_inited st = true -> mc = wz (max_count c') /\ cs = wz (class_size c'))).
    { intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & V1 & V2 & V3). exists mc, cs. unfold a_cache, OT_CACHE in *. pose proof (conj BND Hc') as B2.
      split; [trp rw_cells_transport_pt AG1 WM1 V1 Z1 B2|]. split; [trp rw_cells_transport_pt AG1 WM1 V2 Z1 B2| exact V3]. }
    assert (QST1 : rw_cells asegs m1 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3]) by (trp rw_cells_transport_pt AG1 WM1 QST Z1 BND).
    assert (TST1 : stk asegs m1 (TH + 2800) (TH + 3168)) by (trp stk_transport_pt AG1 WM1 TST Z1 BND).
    assert (RIC1 : rw_cells asegs m1 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]) by (trp rw_cells_transport_pt AG1 WM1 RIC Z1 BD1).
    assert (RIJ1 : stk asegs m1 (RI + 64) (RI + 68)) by (trp stk_transport_pt AG1 WM1 RIJ Z1 BD1).
    assert (EXH1 : rw_cells asegs m1 (RI + 68) [C1 (b8 0)]) by (trp rw_cells_transport_pt AG1 WM1 EXH Z1 BD1).
    assert (RST1 : stk asegs m1 (RI + 69) (RI + 128)) by (trp stk_transport_pt AG1 WM1 RST Z1 BD1).
    assert (FARR1 : u32arr asegs m1 (FA s c) (wlist (rev fl))) by (trp u32arr_transport_pt AG1 WM1 FARR Z1 BB).
    assert (FAJ1 : stk asegs m1 (FA s c + 4 * nf) (FA s c + mfa)) by (trp stk_transport_pt AG1 WM1 FAJ Z1 BB).
    assert (USJ1 : stk asegs m1 (RB s c + au) (RB s c + mu)) by (trp stk_transport_pt AG1 WM1 USJ Z1 BB).
    assert (REN1 : RENV (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m1).
    { apply (renv_transport (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m m1 _ REN MU1 WM1); cbn [disjoint_from]; unfold wz, ATP, ATSD; rewrite ?unsigned_lit by (clear; lia); clear - BND BDJ2; try acb; unfold CTX in *; lia. }
    pose proof (AMODELX_mat s mo mo1 (conj AM AK) SBM1) as AMX1. pose proof AMX1 as AMX1'. destruct AMX1' as [AM1 AK1].
    pose proof AM1 as AM1'. destruct AM1' as (AIL1 & ASV1 & AB1). destruct AIL1 as (_ & _ & _ & NOV1 & NW1 & NWA1). destruct AB1 as [AB1a AB1b].
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q _ (Z_to_bv 64 (bv_unsigned sp + -2320)) gp tp t0_1 t1_1 t2_1
              (Z_to_bv 64 c) (wz P) a4_1 a5_1 a6_1 a7_1 (wz 8) (wz CA) (wz AINST) (wz size) (wz AINST) (wz (bv_unsigned sp + -2128))
              (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) t3_1 t4_1 t5_1 t6_1 F fc m1 lo sb c CA TH CTX ATSD nf mfa au mu fl (as_cache_inited st)).
    all: pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    { exact LO. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - HI; try acb; lia. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - SPT; try acb; lia. }
    { constructor. rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - SPA; try acb. Z.div_mod_to_equations. lia. }
    { exact HC. }
    { reflexivity. }
    { unfold AHI_LO, kSpaceSize, kPageSize. acb. clear - BND; try acb. lia. }
    { constructor. clear - BND; try acb. lia. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    { constructor. clear - BND; try acb. Z.div_mod_to_equations. lia. }
    { constructor. unfold kSpaceSize. clear - BDJ; try acb. lia. }
    { unfold kFreeArraySize. clear - BR; try acb. lia. }
    { constructor. exact U3. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - BR; try acb. lia. }
    { constructor. exact U6. }
    { exact U7. }
    { exact OK1. }
    { exact VIS1. }
    { exact MI1. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). exact ST1. }
    { rewrite TP. exact REN1. }
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
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - BND; try acb; lia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - BND; try acb; lia).
    { exact FARR1. }
    { exact FAJ1. }
    { exact USJ1. }
    { intros a k Ha Hmc. exact (ak_resf_hi s mo1 AK1 a k Ha Hmc). }
    { intros a k Ha Hk. apply (ak_prim s mo1 AK1 a k c); [unfold kNumClasses; clear - HC; try acb; lia| exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW1. }
    { exact NWA1. }
    { exact NOV1. }
    { intros x Hx. apply (ak_zr_sb s mo1 AK1). unfold kSpaceSize, kPageSize. clear - Hx BND; try acb. unfold sb in *. lia. }
    { exact (ak_zrsh s mo1 AK1). }
    { exact (ak_lsh s mo1 AK1). }
    { intros x Hx. apply WM1. exact (AWV x Hx). }
    { unfold ABUDGET, aPhi in AB1b. change (a_st s) with st in AB1b. unfold COLD_COST in PROOM. unfold page_size in AB1b. clear - AB1a AB1b PROOM; try acb. lia. }
    { exact U9. }
    { exact U10. }
    { exact (ak_atop s mo1 AK1). }
    cbv beta. intros msF2 mo2 RD.
    destruct RD as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & q0' & q1' & q2' & q3' & m2 & L' & S' & RD).
    lazy zeta in RD.
    destruct RD as (OK2 & VIS2 & EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG & MU2 & WM2 & MI2 & ST2 & PCN & FAM2 & CHA & CHJ
                    & RI2 & RIJ2 & EXH2 & RST2 & FARR2 & FAJ2 & USJ2 & POIu & POIf & QST2 & TST2).
    fold mu' nnew nf1 mfa' au' fl1 n in VIS2, EL, ES, VMN, EAG, MU2, PCN, CHA, CHJ, RI2, FARR2, FAJ2, USJ2, POIu, POIf.
    rewrite unsigned_lit in MU2, ST2 by (clear - SPR HI BND; try acb; lia).
    subst L' S'. fold L2 in OK2, VIS2. fold S2 in OK2, VIS2.
    pose proof RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    fold st r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13. fold nf mfa au mu fl n in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    pose proof (rf_mfa_delta st c WFs HC ROOM) as FD. fold r in FD. fold nf mfa au mu in FD. fold mfa' in FD.
    assert (BR2 : mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ mfa' <= 536870912 /\ 1 <= n <= 8 /\ n <= nf1 /\ 4 * nf1 <= mfa' /\ au <= au' <= mu').
    { unfold kUserMapSize, kFreeArraySize, kFreeArrayMapSize in Q7, Q12, FD. clear - Q1 Q6 Q7 Q11 Q12 FD NR; try acb. repeat split; lia. }
    assert (SHB : 2201439137792 <= sh (RB s c + mu) /\ sh (RB s c + mu) + (mu' - mu) / 8 <= (sh aceil)
                /\ 2201439137792 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= (sh aceil)).
    { clear - BND BR BR2; try acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    pose proof (conj BND (conj BR BR2)) as BB2.
    assert (UNW2 : rw_cells asegs m2 (TH + 3168) [C1 (b8 0)]).
    { eapply rw_cells_transport; [exact UNW1| exact MU2| exact WM2|]. unfold rf_W. cbn [disjoint_from cells_size csize Z.of_nat Nat.add Pos.of_succ_nat].
      unfold PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (BT & _).
      repeat lazymatch goal with
        | |- disjoint_from (icW _) _ _ => apply icW_disjoint; clear - BND; try acb; lia
        | |- _ /\ _ => split; [clear - BB2 SHB BDJ1 BT; try acb; (first [clear - BB2 BDJ1 ACEILB BT SHB; lia | lia])|]
        end. }
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM02.
    assert (AG02 : agree_on (outside Wr) m m2).
    { intros x Hx Hr. transitivity (m1 (wa x)).
      - apply MU2. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr, rf_W. cbn [outside app]. clear - HI; try acb. intros (X1 & X2 & X3 & REST).
        split; [clear - X1 HI; try acb; lia| exact REST].
      - apply MU1. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr. cbn [outside]. clear. intros (X1 & X2 & _). repeat split; try exact I; assumption. }
    pose proof (arep_after_refill s m m2 c L2 S2 (a_AL s) lo (bv_unsigned sp) q0' q1' q2' q3' R HC MISS ROOM LO AG02 WM02
                  PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW2) as R2.
    pose proof (flagsx_after_refill s m m2 c lo (bv_unsigned sp) R HC MISS ROOM LO AG02 WM02 FXR) as FX2.
    assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).
    pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 (a_AL s) AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK))
                  eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.
    pose proof (rfd_pc_c st c WFs HC ROOM) as PCc.
    assert (HIT2 : pc_count (get_pc st2 c) <> 0) by (unfold st2; rewrite PCc; cbn [pc_count refill_pc]; fold n; clear - NR; try acb; lia).
    pose proof (hit_cells_of_arep sR m2 R2 c ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIT2) as HCL. cbv zeta in HCL.
    cbn [a_st a_cache a_sb a_thr] in HCL. fold st TH in HCL. unfold st2 in HIT2. fold st2 in HCL, HIT2.
    rewrite PCc in HCL. cbn [pc_count pc_chunks refill_pc] in HCL. fold n in HCL. fold fl1 in HCL. fold chunks2 in HCL. fold cp in HCL.
    destruct HCL as (j0 & j1 & j2 & j3 & QC1 & QC2 & QC3 & QC4 & QSTb & CHUNK & SHK & TSTb & UNWb & CC & CR & CPS & ABlo & ABhi & INI).
    assert (ABE : AB = sb + c * 2^32 + cp * 16) by (unfold AB; rewrite compact_to_addr_eq, region_beg_eq; reflexivity).
    rewrite <- ABE in CHUNK, SHK, ABlo, ABhi. change (a_sb sR) with sb in ABlo, ABhi. unfold kSpaceSize in ABhi.
    assert (GD : (TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= TH)
                 /\ (sb + 137438953472 + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + 137438953472 + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= sb)).
    { unfold disj, kPageSize, kSpaceSize in G1, G2, G3, G4. clear - G1 G2 G3 G4; try acb. unfold TH, sb. lia. }
    assert (DAV : depot_avoid (rf_W lo (bv_unsigned sp + -2320) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') d).
    { pose proof GD as (GD1 & GD2 & GD3 & GD4). unfold depot_avoid, avoids, rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (BT & _ & _ & BN & BS).
      split; [| split; [| split]].
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; (first [clear - BB2 BT SHB; lia | lia])|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; lia|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD1 GD3 BN; try acb; (first [clear - BB2 ACEILB GD1 GD3 SHB BN; lia | lia])|]). apply icW_avoids. clear - BND GD1; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD2 GD4 BS; try acb; (first [clear - BB2 ACEILB GD2 GD4 SHB BS; lia | lia])|]). apply icW_avoids. clear - BND GD2; try acb; lia. }
    pose proof (DEPOT_transport asegs d m1 m2 _ DEP1 MU2 WM2 DAV) as DEP2.
    assert (ZR : forall a, (65536 <= a < 7417856 \/ TH <= a < TH + 288 \/ CTX <= a < CTX + 160 \/ bv_unsigned sp + -2320 <= a) ->
                 outside (rf_W lo (bv_unsigned sp + -2320) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a).
    { intros a Ha. unfold rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize. cbn [outside]. bands_as (BT & BC & _).
      destruct BDJ as (BDJa & BDJb & BDJc). destruct Ha as [Ha|[Ha|[Ha|Ha]]].
      - clear BDJa BDJb BDJc BDJ2 BC. destruct BT as [BT|[BT|BT]]; repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT; try acb; (first [clear - Ha BB2 BT SHB; lia | lia])|]
        end.
      - clear BDJb BDJc BDJ2 BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT BDJa; try acb; (first [clear - Ha BB2 BDJa ACEILB BT SHB; lia | lia])|]
        end.
      - clear BDJa BDJ2 BT. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BDJb; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BC BDJb BDJc; try acb; (first [clear - BB2 Ha ACEILB BDJb BDJc SHB BC; lia | lia])|]
        end.
      - clear BDJa BDJb BDJc BDJ2 BT BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI; try acb; lia|]
        end. }
    pose proof (munch_agree _ _ _ MU2) as AG2.
    assert (AEN2 : AENV tp ATSD CTX TH sb (bv_unsigned sp + -2128) T rest m2).
    { eapply (aenv_transport_pt _ tp ATSD CTX TH sb _ T rest m1 m2 AEN1 AG2 WM2).
      - intros a Ha. apply ZR. left. unfold AIMG_LO, AIMG_TOP in Ha. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - unfold ATSD, AIMG_TOP. clear; lia. }
    rewrite ret_pc_even in VIS2 by (clear; lia).
    eapply (evt_sreach_lazy_at asegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (malloc_from_refill ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 lo size d ATSD CTX TH (a_top s) (a_bot s) T rest
                sb n (max_count c) chunks2 j0 j1 j2 j3 rz needed c csz csz8 (Z.min size 4096) CA P cp AB U nT id).
      - constructor. repeat split; try reflexivity. exact ABE.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZ.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold kSpaceSize. clear - BDJ; try acb. lia.
      - constructor. unfold kSpaceSize. clear - GD G5 G6 G10 G12 BND; try acb. unfold disj in *. unfold CTX in *.
        repeat match goal with |- _ /\ _ => split end; first [assumption | (first [clear - GD; lia | lia])].
      - constructor. unfold AHI_LO, kSpaceSize. acb. clear - BND; try acb. lia.
      - exact CC.
      - exact CR.
      - exact CPS.
      - constructor. split; [exact ABlo| exact ABhi].
      - constructor. clear - BND; try acb. lia.
      - exact DCAP.
      - clear - BND; try acb. lia.
      - exact NRT.
      - exact LR.
      - exact TRNG.
      - exact AEN2.
      - exact MI2.
      - exact ST2.
      - trp rw_cells_transport_pt AG2 WM2 FRC1 ZR BND.
      - unfold aframe in AFR1 |- *. rewrite unsigned_lit in AFR1 |- * by (clear - SPR HI BND; try acb; lia). trp rw_cells_transport_pt AG2 WM2 AFR1 ZR BND.
      - trp rw_cells_transport_pt AG2 WM2 FRA1 ZR BND.
      - trp rw_cells_transport_pt AG2 WM2 FRB1 ZR BND.
      - trp rw_cells_transport_pt AG2 WM2 FRM1 ZR BND.
      - exact QC1.
      - exact QC2.
      - exact QC3.
      - exact QC4.
      - exact QSTb.
      - exact CHUNK.
      - exact SHK.
      - exact TSTb.
      - exact UNWb.
      - exact DEP2. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j0' & j1' & j2' & j3' & b1 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 &
                    QC1' & QC3' & QC4' & QST' & HDR & B1 & LEFT & FILL & SLACK & SHA & TST' & UNW' & DEP').
    assert (HR2 : ARHEAP sR LB m2) by (destruct HR as (_ & ND & EQ); split; [exact R2| split; [exact ND| exact EQ]]).
    assert (DPL2 : depot_placed sR d) by exact DPL.
    pose proof (arheap_after ra sp s0 m2 sR LB d lo size CH HR2 DPL2 LO ltac:(hci; clear - HI; try acb; lia) SZ HIT2 m3 j0' j1' j2' j3' b1) as AH.
    pose proof (new_block ra sp s0 m2 sR LB d lo size CH HR2 DPL2 LO ltac:(hci; clear - HI; try acb; lia) SZ HIT2 DCAP m3) as NB.
    cbn [a_st a_thr a_ctx a_fsb a_L a_S a_Zr a_AL a_top a_bot] in AH, NB. fold st TH rz needed in AH, NB. fold c in AH, NB. fold st2 csz in AH, NB. fold csz8 in AH.
    rewrite PCc in AH, NB. cbn [pc_count pc_chunks refill_pc] in AH, NB. fold n fl1 in AH, NB. fold chunks2 in AH, NB. fold cp in AH, NB. fold AB in AH, NB. fold U in AH, NB.
    specialize (AH MU3 WM3 QC1' QC3' QC4' QST' HDR B1 LEFT FILL SLACK SHA TST' UNW').
    specialize (NB FILL SLACK SHA).
    pose proof RQ as (RQ1 & RQ2 & RQ3 & RQ4 & RQ5 & RQ6 & RQ7 & RQ8). rewrite RQ4 in AH. fold ch in AH. fold st3 in AH.
    apply K. unfold malloc_cold_gpost.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3.
    split; [exact OK3|]. split; [exact VIS3|]. split; [exact AH|].
    split.
    { intros x Hx. cbn [a_S] in Hx. unfold S2 in Hx. rewrite !in_rangesb_app in Hx.
      apply Bool.orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [| apply Bool.orb_true_iff in Hx; destruct Hx as [Hx|Hx]].
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m3 _ _ _ x POIf WM3). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m3 _ _ _ x POIu WM3). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply WM3, WM02. exact (AWV x Hx). }
    split.
    { pose proof (munch_agree _ _ _ MU3) as AG3.
      (* this tree's flagsx cells are AGOT_SSP 1782024, ACFLAGS 2419880, ASSPGUARD 7410520 and
         ALIBCPGSZ 7411160.  Wt is missed on two windows of the image rather than one: besides
         the TH-based intervals (outside by TH's band) and AB / sh AB (above AHI_LO and above
         sh AHI_LO), Wt carries the static region [2748504, 6942832) of this tree, which sits
         between the first two cells and the last two.  Measured on the goal itself in
         a farm round. *)
      assert (ZT : forall a, (65536 <= a < 2682952 \/ 6942832 <= a < 7417856) -> outside Wt a).
      { intros a Ha. unfold Wt, depot_W. cbn [outside app]. bands_as (BT & _).
        assert (SHAB : 2201439137792 <= sh AB) by (unfold sh, ASHADOW_BASE; clear - ABlo BND; try acb; Z.div_mod_to_equations; lia).
        destruct BT as [BT|[BT|BT]]; repeat split; try exact I;
          first [ (clear - Ha BND BT ABlo SHAB CSZ; try acb; lia)
                | fail ]. }
      destruct FX2 as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
      split; [trp rw_cells_transport_pt AG3 WM3 FXa ZT BND|]. split; [trp rw_cells_transport_pt AG3 WM3 FXb ZT BND|].
      split; [exists g; trp rw_cells_transport_pt AG3 WM3 FXc ZT BND|]. split; [trp rw_cells_transport_pt AG3 WM3 FXd ZT BND|].
      exists bb; trp rw_cells_transport_pt AG3 WM3 FXe ZT BND. }
    split; [exact (amodelx_hit sR mo3 c n (tl chunks2) ch (AMODELX_mat sR mo2 mo3 AMX2 SBM3))|].
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM1) (nonvm_same_trans _ _ _ NVS (nonvm_same_mat _ _ SBM3)))|].
    split; [exact DEP'|].
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split.
    { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
      rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI3|]. split; [exact ST3|].
    split.
    { intros x Hx. unfold mc_W in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2]. rewrite (MU3 x Hx2).
      pose proof (AG02 (bv_unsigned x) Hx1 (bv_unsigned_in_range _ x)) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
    split; [eapply wmono_trans; [exact WM02| exact WM3]|].
    split. { apply avmx_same; [| reflexivity]. rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). reflexivity. }
    split; [exact (proj1 NB)|]. split; [exact (proj2 NB)|].
    intros kaddr.
    assert (WF2 : WF st2) by exact (WF_refill st c WFs HC MISS ROOM).
    assert (TK0 : forall l : list Z, n = zlen l -> l = hd 0 l :: tl l).
    { intros [|y l] H; [exfalso; unfold zlen in H; cbn in H; clear - H NR; try acb; lia| reflexivity]. }
    pose proof (TK0 chunks2 CC) as TK. clear TK0. change (hd 0 chunks2) with cp in TK.
    assert (CV2 : carved st2 c AB).
    { apply carved_cache; [exact WF2| unfold kNumClasses; clear - HC; try acb; lia|]. unfold st2. rewrite PCc. change (pc_chunks (refill_pc st c)) with chunks2. rewrite TK. left. reflexivity. }
    pose proof CV2 as (_ & _ & CVa & CVm & CVle). rewrite region_beg_eq in CVa, CVm, CVle. change (as_space_beg st2) with sb in CVa, CVm, CVle. fold csz in CVm, CVle.
    pose proof (rz_size_facts size) as (_ & RZ16 & RZC). fold rz in RZ16, RZC. pose proof SZ as SZ2. unfold kMaxSize in SZ2.
    assert (UM8 : U mod 8 = 0).
    { unfold U. destruct BND as (_ & _ & _ & _ & _ & SB64 & _). clear - CVm RZ16 SB64 CS3 CS1.
      assert (Zcsz : csz <> 0) by lia.
      destruct (proj1 (Z.mod_divide _ csz Zcsz) CVm) as [q Hq].
      destruct (proj1 (Z.mod_divide rz 16 ltac:(lia)) RZ16) as [u Hu].
      destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      destruct (proj1 (Z.mod_divide csz 32 ltac:(lia)) CS3) as [k Hk].
      apply Z.mod_divide; [lia|]. exists (4 * q * k + 8192 * t + 536870912 * c + 2 * u). (first [clear - Hk Ht Hu Hq; nia | nia]). }
    assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. clear - Ha Hb BND; try acb. lia. }
    assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
    { change (as_space_beg st) with sb. unfold kHighMemBeg, kHighMemEnd, kSpaceSize. clear - BND; try acb. Z.div_mod_to_equations. lia. }
    destruct (am_malloc_cold st c WFs HC MISS ROOM HM size kaddr cp (tl chunks2) ltac:(hci; clear - SZ; try acb; lia)) as (st'' & ev & EQ & SB).
    - unfold size_too_big, kMaxAllowedMalloc. rewrite RQ2, RQ4. change (rq_n (compute_req size)) with size. change (2^40) with 1099511627776.
      replace (1099511627776 <? size) with false by (symmetry; apply Z.ltb_ge; clear - SZ2 RQ6 RQ5; try acb; lia).
      replace (1099511627776 <? needed) with false by (symmetry; apply Z.ltb_ge; clear - SZ2; try acb; lia). reflexivity.
    - rewrite RQ2. exact (proj2 SZ).
    - rewrite RQ2. reflexivity.
    - exact TK.
    - rewrite RQ1. change (compact_to_addr st c cp + rz) with U. rewrite land7_mod8. exact UM8.
    - rewrite RQ1. change (compact_to_addr st c cp + rz) with U. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 SZ2; try acb; lia.
    - rewrite RQ1, RQ4. change (compact_to_addr st c cp + rz) with U. rewrite land_lnot7'. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 SZ2; try acb; Z.div_mod_to_equations; lia.
    - rewrite RQ1, RQ4. change (compact_to_addr st c cp + rz) with U. rewrite land_lnot7'. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 RQ7 SZ2; try acb; Z.div_mod_to_equations; lia.
    - rewrite RQ1. clear - RZC; try acb. clearbody rz. lia.
    - exact RQ3.
    - rewrite RQ1, RQ2, RQ4. clear - RQ6; try acb. lia.
    - exists st'', ev. rewrite RQ1 in EQ. rewrite RQ1, RQ4 in SB. split; [exact EQ| exact SB].
  Qed.
End MallocColdGlue.

End HCW2.

