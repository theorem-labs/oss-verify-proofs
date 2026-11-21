(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes RefNodes AllocSim MmapSim AsanAcct AsanAcctShape AsanPlacement BackingAlgebra AsanNodesMmLib AsanNodesLibE.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanCeil Scfg AsanRefNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsanNodesMmB () := KReplay.lz_vm "#+GoC46Stdlib5Lists4!s+#2hdI47Core!s>+7!s+#Def6Forall00C!sG+4Init9Datatypes3fst!s{+9micromega5Tauto5eKindK!sE;8GFormula04I!t-;6option00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib8AsanPlan2AP8lit_diffC13~~~!t825Logic2eq!t0R?AxSymExec3Sound4AX2S;mkAlu_denot!t<%K!t<+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!v6#s2bv!u0R:!u0,3AX26e!t}8!v;21K!wgC2!vw83and!yT#!u9?;bv_unsignedC5!yB&6ZArith6BinInt1Z3subK!u]^4expr01!xr8!uC,4prod00K!sFA1!tt<<pos_div_eucl!xE>Z02!u`=opp!sC=addC!w/77f_equal!w1A7Z_to_bv!t-=pow!sC<6modulo!|6e7u_sub64!wT%!uF86eq_ind!t:hlit!t:+!uR;>pow_!x+#nonneg!sN<2lt!sB<:!sj#!sf%!yX=list01I!sFA0!#6256VarMap1!sd$!sD>0!sD6=RingM!s4'7!#6u&!t577Env!sT#5PE!|@$!sIE7K!t?L1!#8y;8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!u~<4f!yS#!sq@C!sq0_s!yH#!xI<=mod!y5$b!sM#K!#5A;1!#4Rd2!{|>9False!|##!t6e3!#8A%!sod4!sok5!sok6!sok7!sok8!#<N7!#<441!#=a^5!#?e#!yU'ELinuxProcessSemantics5Riscv3Sem5alu64!#5?=eI!#:_>0K!t0@5Instr!t2#op02I!v_d0!uM&!v=_two!#8V&!#=2?1!t}_3env!t|'!#D+F3!#An74True!#7q7!#4p,;!wy%!to$!sR#!#9I:uni!#9I8!#6y$4ki!#4h#!#7lB3Op205K!t5A!#:x=bool!#B:>!sF$!sf=3nat!u\4!vL%5!#5m#!t&4!vi/1I!zmM0!sRHmul!sR#!#@0eknow_ok!{HV!#LV-<page_al!#Gn$!z>L1!u7e<e!tD$!#<1%!}^d6!su%!#C7A6divide!#;m73no!#C+=mod_!sc%!#QPE7!#Bh?2!#ATD2!t3F5!sJF8!wne>pow2!uq&_le!w#B<!sO&trans!#JO<eqb!sC=le!sC=6eqb_eq!sc=mul!#QF9x!#NA44Zdiv1Z>!xK#!xO,!y488!#Jy$_r!ti=leb_le!~e;?!s<2<MemImageType7Segment00!#9<^6kentry!#9?+!#7BF!#7iI3!#[K7InC!ueJ5State:iv_overlap!s_Q;region_free!#M=A2!#\e;4negb!sD=andb!u\+4Bool!s'$<!s>#_f!#Gj#r!sd<8!tJ#!#H2#!#:I@!#X@82or00!#B\@7Prelude5bvmap!#97eregs!#97+7!#97NProp!su#4getr!#Di&!#VA>4BvWfK!#]&C1!slA9bv_eq_dec!vc26Specif7sum!#>n$!uEY6regup!#:'fsr_get!vy_9!vy#_same!sl_:!sl$other!#IX@!}+98m_vmmaps!s]Q6vm_brk!~@Rvm_reserved!s`Q7vm_!ts%!#D3:app!wLZu64_range!#AR2!#E>62!#6IC5Psatz!sOM6K!#IBL2!uYQAgentLib7!uY#lit!#=oA3ltb!w]Q?!#E1#round_up_Z!sdQ9alloc_to!#8wQ?!z:#acking_us!ya#!#3X>6bv_su!uOR8vm_limit!w7P<AsanRefNodes=!#e%%_u_eq'!}Q'!#8g56eq_sym!#D`D4!#]N59SatDivModCZ!#@n#!#bE$!#c4B6ltb_lt!t^85proj2c!uoT!ul$MmBL!#=^,!#<B%of!#>Q'!zAA7ad!#C,#!{NR!y^#SimG!zM2!#LcJ1Z03!wE>3Pol!#AzE!~-&4C6!z$I3Sys2Mm4Mmap;brk_gr!#OU#!#Jw?3!y=E3!}<R!vS$siz!#FUK!s^%5Model!#Rr<!#9-9VmMaps!#UE=!#6e#1!#5kM1!#8c;9!#C]#prop!#odAbv_wra!sLB?!#3O$!#tAD9!}>#small!#?GO=!#Tb&!#CG#3APS9sum!w`$s!#3E7!vR-sn!|AQ7!z3#Sim5zfill!#Jj;!#Pz23K!#FX:2!s@<1!tgP>B!#8#$Algebra6ivs_wf!#@gV;vm_noac!s;#!{xRm_vm_lazy!s^QAmaps!y9#tract_!xn#!sfP:live_bytes!vR_7cover!#5L&!sp_!z>$count!sre8!uS$msa!#;P=!#9p#!yF`J!wI4_app_cuts!#H2V!}H#Acct:eager!#?S$!v$d5iv!{9,!sn^;!|&%_cons!|/Xwith!#Is&!tV^D!#J`&_!sw/!uUd1B!sjfS!#?VA6to_nat!t2_=z!|0$_le_len!u&e6z!}$/!u/<of!u/$!#^c<ax!#]{8iff_refl!#D{5;ZifyClasses5mkre!sKC7rew_iff!tU<8max_spec!#_}4nat5Z2Nat2id!#3__iv!#4RjE!#8G'!{15!#G6\B!#3C+_se!#S=$!}e&!wHCapp!sK68!sK#Inst@!xs%_!{'%_eq!#54X4A!#4>'I!sgYMI!#u2+!tRY7A!#;?%!#4wUA!w}$materialized!#uu'!#cO,5NoDup!#[~R!tn'=!#pS%lowedb!ttW>!sh$in!#Vj$!#Wp<6length!tuYC!tp&_!t;#!$,k%!#3P8!}7%!}5#Z9is!$3d'!#J{B5!tfYE!#Ta1_sp!#W6+!#GK`6in_iv!#GHCorbI!t7a4seps!$#VW!sr5;iv_disjoi!#4f&!#3f\=!tf#!#>D#_inv!#3a1!{g-=!$HB$_f!s,$!#IdE!#]0+!|U51!sB>2!w/b5cs_ok!w0X!#{>-;is_ec!#D1#t!sqb9node_exi!soc2pc!#3BP>!#m/#!sE+:fetch_word!shZ8!v4'!$Kv9x!$$HQ!}G6cfg_of!vHb7reg!#c:E4lan!$F73Peano2lt!#<OA9and_morph!sOB;!#@u%_rev!v;b=!uM&!$%J/5!#]/'!#]#%6PosDef3Pos!uW%!uu<of_N!sf@6pred!sJ8NatDef1N5l!$Q{#!sG=3lor!sE>8succ_po!#SlQ4m_fs!#f9Da!#X$Q!#lF'7seg_rom!#?|V!#uS'mks!$Qx'!#`dIRun6config!$/iQ!yC57co_hal!#FXV=!#8p'LibE@srz!#4m#_at!#X#$!sxc:!wa%_255!~GV3Lib2Nd:!sh#elimF2!sk]9ex!sj%1!uKdA!#9$,!$3{[!uR43!skV!#aB5!x,$stm!#yiWShapeAlg6t!#:d,!#IcO7SpinAlg9sre!#H3#!#AA+!#E0<6inj_ltI!#8SZ3ac!t5+!$Dc<!$9j+!$`[]!#=x#sy!#W_V9!#~X#Run39env_agree!xbV!uo0nx!#?Qb4a_ss!sjb6a_!#Zk,!#=a[a_totsz!smb5a_ylo!tZe!#T=#!tZevi!v6fghos!xWc8a_a!#SB-!uJ^!#WA+!z4^fd!v6evmo!z5d8fresh!$4m+!#Cj&!$7]+=negb_true!#][#!wG^tidse!#=>d8Some_inj!uqV!#HW6o!tg#!uu'!#x'Om!s`$!tNO!$563_reg!x2c:sr_vars_l!#N8ckn!tZckn!tZj<!#jL#!sri=pair!ssk<exp!w7k:fd!sp1I!#Nd8e!#Q#c4ext1!|@h:!sp#!#=W[!#[,5!#Wp#!sw0!$3MP!#hU#!}@S!tV5<!#?~'!$N]+!sxa7!vH%!y;W!#3/12ev!t`h3hi!#wCV!zq$Acct9mrestrict!v?iin_hu!$&:&!uRcTOP!yVW!$1R$base!tOb2uE!tN'!#a,47ex!s2#b!t2b5sh_!#CfW!sq9hi!u$4ogicHFunctionalExtens!s1$ityIf!s?+_e!s@0C3!#WK$7tac!w2#<!${Y%_help!vwcMr!uhh6!#lg#A!}Ee5s_log!#4[Wm!#WS#e!#4[b6fd!$Q',!#YmMAs!$Xp$s!$JC+!#8]a!#=>#match!~rihole!$SVX!#zH1<model_!$54/8!#5LRP!#=?$6img_!#Moc!sl$!}&+!sl[7am_ki!#YnW!w558amap_den!tcf!#6B#!v@bam!$+P,!|iP<vm_start!#N`#!v4bin!#Q,[!st59!$TA#play!#4%d6sr_!$YR'!${a^!$ck&6!tbg_know!vJh=!$_5%_set_!zSW!$`379!uc%!#3]+!#_u<7inj!#RH#!#rY67iff!$PV$!sC'!%BQ82K!#B=W!$+R$1!xKV!#=u5!#xo$!#foV!$`W+v_addi!siV!t^$!#Ta'9!sn%_!#x#'!#kla!y2#tid!#kl-!vKa>!#XU&!sK#t!#T?V!#iH37!tgh8sys!#iG-!#6VZ5mk!#cp'K!sk[!#h8#!%Bd&!sk[4amap!#j5Ke!#l1X4TS!#\X&!ud\5snode!%6h&!#:&J2Fs2Fs!#<5\PID_MAX!tC&!$X4M6Kernel4Fork@!sl&_ENVELOPE!$ud_s!$ud/!uQ\4CEIL!sjb7!sj#!v=,!sm[;e_sp0_early!{5b5m!%17#0!z'c!sm%3!smi4!smi!#yg&!#:jWJsame_but!$>s/!$G<$!#5pf7co_m!$72+!sse!#e`Y!#NZ5co!#m;Y!tg9!#B:k!#_P%fr!$ud+!}?\brk_req!smb3re!#SM%!$=1\>!%[i&!$#t[!~y0!uO#base!%7zX!%?62x!#PBW!sl4!#PBW!#G08xlo!vG\!sx:hi!sx/!$O']!%;K-!x<h3KHI!si&!$5[?5!%%H#!$p@<div!$p@#!$U`;di!%Z5<!%Q5#neg!$JH%!sM'5!$Pv$PreO!s/#1Z;!t4#0_r_ext!sL>!st#!sL&!$p=J7!sOK5!$m%M3!#4<a9reg!yNiA!}j-!$3Yl4!tec=!#5z%!ta/!%NT=N!$0h]@!$u1'blocke!#[bh>!#ox+!#=M+!v-]!#6Y#keep!#`lX!#On0Bsrz_!sw#query!#OpZ!#:q/set_!#:-e;!xe'va!#@x&!#l~5>!#l~%_!s-%!#8m^7lin_ge!#Hnb6is_f!#iL'!#8ec=!td&!#9cp6xt!#c3Y!#B:8s!#C/n!$7mY!#^C5!#jr+_In!y[=9in_or_app!zm]K!%%L,!#<j'refut!$q>W!}\1I!}\'!#4J-!}cg6!}c#!#\=&!#U9b2!#3@bvis_ad!#EQc!sm&!wD#!sqb:!sq'!#HpW!#3f19!$a~#_l!$Z7c9shad!z##!#qDcflat_x!uQe>!$gN$_apar!sw,!#}U6!$`_$b!u%\8!wX#c!$?od<!vb&fact!$8Gb9!tb#twin!sod!$IO#brk2!#5Ug7hull!%_:d@kn_grant_filterM!yFe6s_nex!#b8V!$#$3addr!#lYW!#q~97!sqm!#5fb?!w?2!subC!x63_!#VvcC!#:2'admissib!$7Y&!#Ie]!$E-#pair!$E3Y!#58/no!#BkY!}N0budget!|YY!#]o8re!#@qh@!#@q,exa!$8_i8co!%J1%!ufktop!srlsp0!y{d!#=o&shap!$AviA_wf_!$51/!tmT!%Mf&?!%Ju-ap!vY'!#<?56in_ma!%UeQ!t5'>!t5/I!%2-W!vs-Lib!$43$!#>D#!u%=8!#?\#!u'#!sC6?!$xG&!sJ&!#7-f!&#^3!$#S8!&#]_6a!$1,Z!#:p2a_of!#C_V!#ON8e!$1A#!suk5elenZ!xI=:!x+&!zq#!#6kZ<!#:B$!#X/#b!{_>!#;Z%!}ka>!%ym%!#<Ph?!#WY#ange!#E-[!tq5B!s{2!#9|j<!#Is$!#VV[!sx5:u_of!%/T/!$]]4>!%n<,!%<;>!%ZS#ge!#cS]!#52-intr!#mW%!#ju]!%262!$QUi8co!$ff[!st59co!$e9\!tk6in!#:r$!st&!wv=eb_gt!#`}]!%51$!%IX-!u0a3!$ik+!tcO!%V+&9!%V+#_ou!#B0lnasub!sth!vK'tru!$ZJ'!#:{83!#<V9:!#>v$!}:$7!#5ERCeil:init_sp!#4=j5co!$J='!y\]C!$@E&!%uQ$!%sw-!$FCSm!v>#!#=k#!%X$Pvm_!v:&!#9?[7is_ho!#3f'!x-:ap!x-$!$@/a!%>%$!$,zV!$ON1H!$ON-!%R~5!#8[4:or!$o9%r!%>Q^!%ao&!#GP+!%L/h!%?M#l!%zOWA!$14%>MInv!&2\$po!#Bf'!#6C:;lt_ge_cases!vM68!vM#pro!#ht]8!#5+$i!#lhh5in_s!$Vmh9!#E0#!#dKY!#F&74fl!$fq'!%>}Ystor!$-?#!#}d4!%;y-3inj!t1Z<find_!$[R%!sjK!&6%/<seg_writable!shX9!sh#!#>p$!seW8!se$ase!%=O<to_N!v?Z?!v:&!to$_at!smZ5wview!#>GPS!xl#Ok?!xt'_o!#U5#!z^V!#\:/kdisj_ne!$9BhAH_off_!$b+'c!%'ocgaps!#mqd9!sm$loh!$QlV!#VT1Akimg_!$nb%_pure!sze>!wM+!sw/!wRb!tv$clip_!$p_n<!uu/!sxh@!vo0!#\N4!&>',!#=8'!%,KR!#G%5vis_mon!$pEh8hid!v0m!#U^'unhid!x}i!#bB+o!$6[eH!$#F6eli!%IjV=A!$#C-A!$#C/!$Zjk9brk2!$Y&,!$#D[!$WP$!#rA&!#HZO!&&`&1!#=XA6!%hM#2!$Ngb!$`s&!$YD<8inj_succ!$RG[6spiece!%DX+!#^Y5E!$4z#00!#eT7map!#Sk$!sC7nil!sC1!%kP57Inj_Z_Z!#8j[8!#Mp#l!$oRc<!sn'!$'pe;!sr+!#ukc7!$Ge#u!&7eB8ltb!%s5#!&`;;8BoolSpec00!%XE?!&zn#!$GZ;po!%~c#!shAmul!uf\5n!#t|,!#M<P!&:&%F!&:&2!$Hp#!syY!#WE%H!&:}9'!s{V!#oK2!xN&!y@,!wB;9p!#{`#!&Xt>7!&Yb#ul!sj=mul_assoc!}J6!&@`/div!&@`9!$L'3:!&],%alt!$NO@C!&Bw&!',5,!$cK^9sy!$xl#t!#4o'!#YSP=!&-r/!#WT^6in_rng!x}W!so1!&4x1sem!#3Fb!#44$!#a`V!w428!%@q#!sqY!'6Z8!sw'!#5|ekzero!$8:>!#xY&!%rL$!#EUQ!$Hj2xins!#C_'!#yKf1!vrk=!ti&!#DU-!tog3!sqm4!sqm5!sqm9!sqm:!sq%!#50^!$9@%!%{yh5kfoot!~_e6a!'?>,!#<7P!%#b&3rd!%1}Q!#Yq1@word_to_l!&C6&!|Ad!$EN$u!uM_7rdn_ex!w&f2e!$$4'!#q99n!&-`Q!#\h&<!#\h'!#\efn_un!&L/+!#6o69fold_left!t5\6!#VX#!v/&!#RK\5sh_iv!tx?!$'5#_In!#;e_mk_sprep!vzb?!%4D%!$L+$b!suc>!su1!#3WgB!tq2!#=VX!s~5;!#4W#!$7X/!um[;!$L'#munma!wWd!sq-!#P&e>!su/!vW'!#q:]s!%d#\!te/:!%Cy#!%I$,!#vB]!#EI%!$2'm9co!#O,/!$1@]!$XF$!#8B#!$:,[!to5!$bU#e!&N<XA!#Ow/C!$Gj,!&:Gj@!&:G#In!sw2!#<r:!&{Z06!$vE#b!%5BM!&yA$b!&G=S!#<=&;!sf&!%,,Y!#[d/a!|u%!$/Pi!st'!#5H+!xX^=!#Ln'!u_-!sv_!tl+!sv-!$,DP!#59$mov!$;2]:!z'$!&?w#!w;hA!{w-!tj%!uQ'!#=a4=!#=a%ext_in!vk_<!$5',!&sJ8!#_A+?!$?,#!#o?$!$=r#!#oa4>!%v/#!$?P+!&Uw7eq!'7A%!uP6>!$c2%!&Ds%!#7D]!#S1%!'=rj5mkSr!}]c:!$gk'!$K3k7u_srl!'[l'!svd;!u^$!'g0-!{>b?!$kH'!s{\!uo;add!'^]C<!'1c$id!$'q$!#`F>@!&|?'!&q7&!#7}W=!&rK%64!%0E#!#4NU7map_has!#5|_!sj&!$HU-!#MgP!$Br%6!#Lp/!shW<!#D4%!$:I#!#8Nd?!%'`0'!w$W!%6l$out!#\3#!$OO#!#3q\E!&ov%_!#e>0!u_d>!$Hl'!&p}[!sw1!#lN$of!$26$out!'$N0!t%_K!&\k0!#fY+!$IBX!%4?3!#^A%!wk]D!%-2&!#<%%!$S8,!&WPE!'LzF1!sJF:!#;z5;!#<E+!$YPb!u[,!#<p#!#<2$!|-'!tG5or!'E&+!~7W:!~y%!$Nnk!%tR$1!zLeAin!$cS'!$Xj0!#?v53!$NMR!t;2F!&h$%!t@9!#>iZ;is_tok!%oS,!{b]?!#]:#!ws&!%PE'!#M~]!#Xg%!$ae#!#eK,!yZWC!#8k-!%xn&!xod;!#Hk#!$b>/!stP!&w$1!$Mu%!svk@!#uT0!&}BX!ug1D!sy1!$-m#s!{[>6or!'zD#!%lW7and!sC$!t^^C!t^1!y@#!#V3f!$Q,+!#7m%l!$?}f!&v>0!xNe;!#>O&!$=|+!ukc!&~A$!uk3!$/M<e!#My<<!#Qj#!{3'!sG6;!#9<&!&xl-!&FS,!#9,+!$XWR!#57-4vmop0!&Wbh7!%{E#e!w3W!$=,0?srz!#c;&!$='+!#6$\>!$58'!#Q=-!#:x_!&\0e!wM0e!%=S'I!x9a!'a$<!'qd-!'I-]6bv5_17!wZc!sm%0!smi!$AXA!'qZ57!sRN1!#LDP9TASK_SIZE!s^Q>stack_!'/q#iz!$eQQ<sp_window_lo!#i#]!#mF-!$'\Z!zS/!%F^%1!xVcF!&`G&!td%_YM!#p|,!s}]C!s}3B!%NK&!tynSetTi!~<c!vg&!|?&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3andhc2eq04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~k16edenotk14exprk15two6435stdpp9bitvectorbdefinitionspabbv_unsigned37Corelib4Init9Datatypess54Somes56option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~ud8lit_diffk13env46Stdlib6ZArith6BinInt1Zhjc2lehjc2lthjc6modulohjc3subs54listpa2bvs54bools54true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehob7Segmentudcpage_alignedk16kentry79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~hu37know_oks54prods55falses54pair3h5LinuxProcessSemanticsfLinuxProcessSem5Stateikbaiv_overlapikbbregion_free36Stdlib5Lists4Listip62Inhu37regs_okhc1Ihc3not3h5LinuxProcessSemantics5Riscv7Preludeis45bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~iv34getriv36regupdpa2BVpa4BvWfhjc3addikb9page_sizepa7Z_to_bvs53appikb5Modelikb6VmMapsikb8m_vmmapsikb6vm_brkikb7vm_mapsikbbvm_reserved5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapjr3bbrk_grow_okhjc3powikb9alloc_topikbfvm_backing_usedikb8vm_limit79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~ki99sum_sizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~kna5zfills54negbikb9m_vm_lazyikbbvm_noaccess69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~ku0aeager_used69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBackingAlgebra~~~~~~li97coveredli96ivs_wfli99sum_counts54consikbbwith_vmmapsli95iv_wfku07A_bytesku04A_wfku04MInvki96in_ivss54andbs53orbhjc3lebhjc3ltbki94seps37Corelib5Lists7ListDeflv36Forallki9biv_disjoints53sndip65NoDupki99exit_stmtud7YSetTidki98sys_stmtki95cs_okud5a_brkud3acsud2pcud6set_pcud7set_regud7brk_requd3regud3KHIudbbrk_base_okud6img_hihjc6of_natud4YBrkud7a_ghostud6a_mapsud4a_ssud5a_visk16s_regsk19split_lits53fstud4amapud6flat_xud2knud7vis_addki99brk2_stmtikbfpage_round_up_Zud8mmap_lenk12SAhu36estartikbdmaps_subtractli96in_rngud7len_eqbhu35elenZud7kzero_xs54Nonehu39kentry_okhc5Falseki95kfootikb4m_fski96cfg_of69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AxSymRun3~~~~~~ns79env_agree69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~oh09srealizes3h5LinuxProcessSemanticsfLinuxProcessSem2Fsol72Fsudbis_ecall_atudbnode_munmapud3nxt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~oqa4TSetud7YMunmapud5snodeud6atables53nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticspgecfind_segmentki97in_hullki97hull_okki99shadow_okud4CEILki9ares_len_okud6img_lohc2ex3h5LinuxProcessSemanticsfLinuxProcessSem3Runppbh1segments_reservedudbe_sp0_earlyudcexpr_vars_lts56lengthud5n_resudashadow_off" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma lit_diff_sound : ltac2:(zQ "h00!h9!j0!j6!jb!o2!ob!p2!r7!td!u4!hib!hj6!hl4!hla!hm0!hma>1E$b>1e$5>1f$5>1d$0>0@3$2@1$9$0@2$a^3^2@2$8$0^1@2$1@2$1@2$cZ^2@2$d^2$6@3$2$0@2$e@2$f@2$7@1$3#k0@2$4^5^4@2$7@1$3#k0@2$4^5^3$6^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##I2p'0h01Dh11Hh22Hmh32H0h42e0i002e0h54e0_1h64e0_2h72opi012oph81zi021zh91ni031nh:2Hah;1dh<2sxi042sxh=1Eh>7__arithh?4__ffh@6__sat0hA!s/%1hB8__varmaphC5__withD1ei051ehE2e1hF1fhG1ii061ihH1ki071khI2loi08!s+$91ai0:2a'i0;1bi0<2b'i0=1oi0>1pi0?1qi0@1ri0A1xp;1p;2p;3p;4p;6p;7p-1R0p10000p4p710p8P!s6%G!s62hR1!s8,P!s2$210p8g001E!sB&1g001dR!sq$3101!sD$2HR2j1sTg002jj2rTg0042j36!s/$Lj4qTg005`j1@Tg006Ej1^!s/$cj1\Tg007Fj20Tg008Oj2D!s/$ij1hTg009Kj24!s/$fj21j1YTg00:Pj2;!s/$mj1MTg00<6R3j2Z!s1$Vj4BTg00=6j2J!s/$\j1ATg00>:j1F!s/$Wj2ITg00?4j6K!s/$Qj2ETg00@7j2X!s/$Tj2=Tg00A4j2WTg00BDj6:!s/$`j1VTg00D0j2U!s/$Xj2CTg00E4j3p!s/$Xj1oTg00F8j1n!s/$Xj1kTg00G6j1j!s/$Tj1iTg00H?j2Q!s/$bj3gTg00IEj4fTP0j7eTg00J0j2d!s/$Rj2cTg00K>j3`!s/$]j4aTg00LOj3bTg00M6j4_!s/$Qj1STg00NZj2HTg00O9j3PTg00PBj3OTg00QKj3LTg00RTj3NTg00S]j4RTg00Tfj4TTg00Uoj2]Tg00VQj3lTg00WYj3mTg00XAj2[!s/$]R0f0R4']p=7g00Y;R5f1R6;l4p=<Am564p=>f3R7f2R8/06;64p=8g00YgR9?664p=5g00[0R:,=4p=3g00\8R;/[4p=91C4:p=?A6064p=2P0P0P6P4CBp=Gg00\V%s0R<1r86%7436f4R=P5P7P8Cqg00]^R5#@R>#@!s$'R?#^R@#\RAP=1<7810=710=8'>C81<=7P91D94f5RB/<=/54P9f7RCf6RD'<!s5$P<P6%34#7%h0REP!s$-n0110A000810102101033010110910;!s1D40104108103100!s4&7106103%7D56<PAf:RFP8f9RG,0Ff8RH,0F'>C8%9H%?H'4f;RI/0FRJ,1@10IGRK,1@';#3/2H'4]0]1]2P61<HCRL%M4'5%36#7%7CRM!t-$PI%M81>JKRKC8P<P0P!w9%4P4P3!s0$0P01Z00RJP=!s4$;P;CBP0PJP:!s6&BCBRN1J6:RO!sZ&J%A4,J6RP!sN$4P0P0%F6P;CBRQ%A5,I8#FR51I:6'GRRPR!vh$@0003001010>!s'$n200110>00012010?10@!sP$;!sP2<!t]&N!tM'PO!tG&Q1;:6,G5R5P5!t3M!sm+P%F4,G6!tWM!s<$9!s<,:!s'$P4!sh100010@n!xw$=00!yQ%200X4<%37RP#7%7GRJP6EK12PG%3=/2FP0%3B%94%?4'4f?RPf>R3'0R5,1@f=RQ,0PRO!xk$RN#3/24'4X;0PAP0%Y@1E@BRR103Qf<RS,03'>RTP8EK11@R11@T'2P01>5ORT,1@1E@C,1@RR/24X80P4%A>R>%A?R?'XRU,=NRN1W5OE:1E@D,1@/2NP0PRfARRf@RN'0RD!zN$R!ta+5/=URV,!sv'3CRW%VCE:10NP!sQ$N3!sO$/=U,2W%3HRW#9%?W'4%35R5/2WRW1U>?1C;>%9?1C;URC[[%9>RXg00^CRYAp>?6UW:%9U\Y^:!s=$_RX#o%nX%k0%j0%i0RXP1g00_KR1!s/%kR1P01Q0;g00`K1Q0>=g0@Cfg00a2Fe1dX1P4P8g00aRR1g00b2RX'D1c48=61XdA`0;6Cab?bBbCPCP4b>b@bA1C;:e9bH:P01=HURH1=GU!uu%1D0HPVP4E:PWeC_b0b0b0PIP4E:W1P4O1b3W0W1W2!vI$O!tB$RRW%S4,5LA6<EM!}m$S8P!}i%EP2P0p-0P4g00c1R2PY!yq0!s#$RYX4<RKg00cNRMPJP6E:P2%9F%?F'410QS!wL$QI!#3E'F'4/H4!tZ'W9!tY&cjRF1<SIRSAP864'5%7I96<ERIPAPPAP=78PT!tf&KPM%7QR!t;+3%?3'41253!t&&R5!u`&69X59W7P8P6P4O3AO864,5S!sy$O!sy'5W0X1I!sT'X7F!sU'g00dVRFAL!s\-L!s\9!t2-N!sT-N!t2D1<3QRQP!se&CR'5A6<EJRJPAPRPBP=P7P8CR1>DORO!uv&YXE<PM%7PRP!uy'N%?N'4fCRYfB'0!w:$YR!w:+N!v6$RN!xp+49X9WXIWX<1!tI'O4!tS+T,5Q!tM0TPO!wA,P!tC&P!su$X1JW2X9WXG0XH!sv1n01105000811!#:fc5!#:f0P!t|$O3b2b4b0W1X;0XF9XD9W=o"). Qed.

(* [comment removed for export] *)
Lemma page_aligned_sound : ltac2:(zQ "h10!jb!hn1!j6!hn8!hnd!u4!ho4!h9!hs0!hsb!o2!hj6!ob!hta!iia!hm0!r7>4SEGS@1$1$8>1E$b>1M>0@1$3@1$0#k0@1$5@1$3@1$0#8>1k@1$1$d>1e$c>0@4$e^5^4^3^2>0@3$2$4@2$9^3^2$6@3$2$7@2$f@2$h0@1$0#k0@2$a^6^3+hgg0Z").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##HCp'0h01Hh13GENh22H0h31ni001nh42e1h52e2h61mh72opi012oph81zi021zh91ai031ah:2Hah;7__arithh<4__ffh=8__varmaph>5__with?4__x1h@1bi041bhA1ei051ehB2sxi062sxhC1EhD2HKhE4HdivhF3HlehG2HrhH1MhI4SEGShJ6__sat0hK!s/%1hL1ii071ihM1ki081khN2k0i092k0hO2loi0:!s+$;2e0p;1p;4p;2p;6p;3p;7p;8p;5g00F8j1PTg005`j19Tg006Ej1S!s/$cj1YTg002Hj1pTg00eBj4lTg00fRj2hTg00g^j1TTg00=\j1<Tg00hCj6\Tg00iXj20Tg00XAj21Tg009KR0j2=Tg00@7j26Tg00jaj2?Tg00kAj1g!s/$Zj3eTg00EXj1dTg00FXj1cTg00G6j1b!s/$Tj1aTg00H?j2KTg00IEj4LTg00l>j6`Tg00J0j2_Tg008Oj2R!s8$Rj2^Tg00K>j3]!s/$]j4[Tg00D0j2Z!s/$Xj2Q!tL$4j3x!sw$bj2wTg00m@j2v!sw$ij1u!s8$cj7tTg00nGj8s!s/$kj3rTg010Bj5q!u`$Tj27!s8$hj2OTg011Ej2JTg00:mj1NTg0042j33!sA$bj2oTg012Bj2V!s/$_j4nTg0139j4m!s/$_j6UTg00?Qj2k!vv$fj2MTg00B`j1jTg00MQj1FTg014=j2iTg00O9j3DTg00PBj3ATg00QKj3CTg00RTj3@Tg00S]j4GTg00Tfj4HTg007Fj2XTg001dj7fTf0R1#9#9p=;g00aRR2g00b2R3731p=:f2R4f1R5/01'1p=5g00\8R6/11p=81X51,M4p=Eg00X]R7f3R81X45'M/71;36p=2A3716p=B1751=376p=>P5g001ER9g00_KR:P:g00_kR;P1g00a2Ffp=I1051,J4p=W1J51=323p=4g014]#Pg00\Vg00]^R<#9R=#;R>#9#;R?#SR@#Y%S>#Y#p[g015\!sU$YgR>f4RAP8P4P5Cl1h45#:%T<#9RB#9#<RC?584RDf7REf6RFf5RGP!sU$E\10A8RH#8%<?RI,1H'=%<=R=/6HAE@F8RH'?'=P010GARJ#811JI'=16=JAE@EA'?P@f8RJPG%;?#;#;#<R?C2P110EFRK#811KI'=10JE,6=f:RK=E@E'?%B1RL#gRMP01>451?48RN[1?541>84[RO1>A8\NAe451P1n20010!s#$12!s-%0UX@7X97PO\M^@7^97P1f<RMf9RO5E@RNP?g00^_RP#dRQ%PPRP%c7%b7RR%a7RSP9P:P:P;P71K7?g016g1K76RTCL,ISE`1_S;RUP1P41R231^14#:dA]765C[R3b<b=b>%B?g00c1[P1b;P?10KORV,6=PN1Z=V1Q6=f;RN/0K#810MN,6=,Q6[[%8=RWg00^CRXf=RY/0MRZ=x=5UW:16=Z#8\X^:WPQPP1w75PRP!t|1CRRg017NRP1v7<!t~$R<%u:!sM/PTPPPR!sB$P<FtGsPUP!u+&X?711C1%8C11C5'=[^?7P1PZPOO2b;bJbK9rCVP5DqO4b2WEWGP5P1O2!wK0!s/&b9WF1>H?\DP>P>P2P1171?RD/O6RH10F5RV,JCAWCJ8RJP!s$$AWCOARJPJn011050008101021010030101103104!s1D4010610:10010;!s4&9107100#:11CVP@POP4P?C2RV[PV]1]0P8%:H%N595CEP@PK%N!sF$[P01O51#:A3745[RHA37511O45#:RV[A3784\V1o51P5!zK7X67X37PH^67^37P1178?RHP6P4O3%BHP7g00[0,7ARH%BDX87P717A?PLX87P116=IRI,7A/7?PAPIP?P71V1?937IX87%TB#;#<,6=R=1V=?,R7CnCmEU1>H?e1k@A,M@%jAEUP@PM%NAP?C2eb0b2W1W0!t0$O1g00bRRH%F1,0F,4C%F!uz,F!uz&1P014511145[R011511445RE[1184\E1i!uuAREP0!uw%R0P1PC%F8,0OP4O3b2O1W1W0W3!tY&cjROAD451,0K,4CAD84595CNP@f>R=ADA8!ta+EP!ss$ADGA8,0Y!su/X5>X4>W7P4!z`$3AA!sx,A!sx+P=AA!sv6A!sv;X7O!sw'g00dVROAC!s~,C!s~/C!s~6C!tvF@!sv,@!sv/@!sv6@!tvF!#8G$P1CG,0M,4CP!#8Y&G95CYP@f@ROP!#8@%CG!t02f?R=PF!sE%CG'0!t80A>X3HXOHXB2!t3'O4!t=+H!t=2H!t=%P!t;,H!t;2!t7+H,0=!t803HXL7XN!t81!#3&,1!#3&c5!s4&8!#3&$!t0$2b1W0WDWAWMWHWCWIo"). Qed.

(* [comment removed for export] *)
Lemma region_free_false_of_overlap : ltac2:(zQ "c1!jb!hn8!hnd!ij5!j6!ijc!hn1!ik4!ho4!in9!io7!iq9&@2$3@1$1@1$0#k0@1$1@1$0#k0>1L@1$6~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>1a@1$1@1$0#k0>2sz@1$1@1$0#k0>0@3$b~0@4$7@1$1@1$0#k0@1$1@1$0#k0^2^1^5>0@3$4$2@4$9^5^4^3^2$8@3$4$2@3$a^7^6^5$5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##3Jp'0h03Hinh11Hh21Lh32a'h41bi001bh51eh63sz'h71Eh83Hovh92IHh:1ah;2a0h<1lh=2loh>1nh?2szi011pp;1p;2p;4p;3p;6g005`j16Tg006Ej1C!s/$cj1>Tg00<6R0j2=Tg00F8j1B!s:$Vj40Tg0185j32!s/$Lj45Tg0042j34Tg019Ej33Tg00EXj1<Tg01:?j39!s/$_j17Tg01;=j28Tg00?4j6;Tg008Oj2ATg013_j6:!sJ$[j1@Tg01<;j6?Tg00aRR1f0R2g01<]R334p=1g00]^#6!s$-C#>R4/=4R5#BR6P4P4f1R7P2C0f4R8525P8f3R9f2R:P7C5g00b2R;541P5P4P4P8P9C0R<=252f7R=f6R>537#1]0X2!su$P9P:C0R?%<5R@525g00c1A3@=>#1P2n010!s#%W0P0!sV$4P4P>f5R@C0RA!s~$9RBf8RC!s~&!sG$=P>C0RDA95:7525A959:f:RE;3B#1]0[^<6P2!sP$BPCC0!sm$<RFf;RG!sm/EPBC0A95?7!th$1==!s=$GPEC0R?945<A25?:f>R?f=RHP@P8C5#7A39?H'8#1!t2&@P8C!sw%FPGC0RG545!v>$!uH'2P2n20011!ue$120100100X55PA!sG$HPFC0P2E;A44@F!sb27!sb;D!sG$?PHC0P7!sb$=?f?RD944CRCP4f@R0A44B0fDRAfCRIP7PE!u7%BAIRE'8#1[X34!t<$APIfBRAP2C5#7/8E#1X64P1P;%72!s5%411A13PIPAfAP0C5P?E:PBP2E:X1C!s/%W1P2O1b!s+&W7P2O1A25G9P1P3P0PD!x$$!t/$2!sx$PDP?P>P@C5#7#@A38D?P9P2O1E:W0P2O1!ur$!y9%21!ux$0000A95<:?3HF#1eW0W9X26X64X34P7P2O!w311!vO&;5P>P7E?W8W0X?4X:4X>4X=4W2o"). Qed.

(* [comment removed for export] *)
Lemma regs_ok_regupd_same : ltac2:(zQ "e0!jb!hn8!j6!iqf!hn1!ira!ire!iua!hj6!ob!jie!jj6!jk0!jk5>1E$8>2sr@1$4$9>1R@2$7@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0>0@3$3^5^4^3>0@3$2@1$1@1$0#k0@2$a^4^3^2>0@1$6@3$2@1$1@1$0#5^4@3$c@1$0#5ZKv$5@2$d@1$0#5Z@3$3^8^7@3$b^6^5^4").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["FPX1"] "p'0h01bh12r'h21vh31Eh42HRh53Hneh62Hrh72Hvh81Rh91dh:1ei001eh;1rh<2sri011ni021sp;1p;2p;3p;6p;4p;5g00F8j1DTg005`j12Tg00g^j1>Tg006Ej18Tg006cj1:Tg01=Wj2BTg01>Cj39Tg01?Sj21Tg0042j30Tg01@Tj2=Tg01A7j3<Tg00kAj15Tg01AZj3;Tg01BBR0j2CTg01Bbj36Tg01Cej24Tg007Fj23Tg00BDj6ATg01Dnj4@Tg013_j67Tg01F4j5?Tg00\Vg00Yg#Dg00]^#2R1#>#8R2%21#2#2#2#2#8#:R1'B%:2R3f4R4f3R5f2R6391156f1R7501g00\8R8g00cN1=28d5<29035#5f0R8f5R95;2A0389R2%52'CP0f6R09037R7%57f8R7f7R2;60/16f:R:f9R;/46'3501P8A0362R6P3P7A6:;7/18f<R:f;R</48'3501X13P1P214<;,3:9018R=X01P111;7P=X21P0P7O1P2P9EAA6;72R=/17P;P7P2P4C@E7P5P8E7W:P8O1%56P111;514<4,3:9018X01P0P5O111=5P;P7P2P5P8D?E7W5P8O1n200110200021010010101b9X13A69459920eW6W7W4X21W;W8W<W3o"). Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_refuted : ltac2:(zQ "h82!jb!r7!hn8!jkc!hla!j6!h9!jl3!ij5!hm0!jm0!jma!hnd!ijc!ik4!jn0!jn9!jo3!jof!jp9!jq4!ju7!iq9!jv6&@2$8@1$2@1$0#k0@1$2@1$0#k0&@2$a@1$0#k0@2$3@2$1@1$0#k0^9^d>1m$f>1d$6>1a@1$2@1$0#k0>2sz@1$2@1$0#k0=1h$h0@1$h1^4=1b@1$2@1$0#k0@1$h2^1>0@3$5$6@2$9@2$1@1$0#k0^1$7Z>0@3$5$6@2$9^6$7Z>0@2$4Z^7>0@2$4Z@2$1@1$0#k0^4>0@2$4@2$3@2$3@2$1@1$0#k0^5^9$7@2$h7+2+k0>0@3$h6~0@4$e@1$2@1$0#k0@1$2@1$0#k0^9^8@3$b~0@1$h4^7@1$h3^7>0@2$4@2$1@1$0#k0^7@2$3@2$1@1$0#k0^a@2$1@1$0#k0^9>0@2$4@2$1@1$0#k0^b@2$3@2$1@1$0#k0^8^c@3$5$c@3$h5^e~1~1$d").
Proof.
(* LPS 727298f3 port: written out (rule 11g); the zQ statement above is untouched.  The
   replay recorded [Mmap.brk_grow_ok]'s budget conjunct in its old byte form; the model
   states it as [brk_budget_ok] over [brk_grow_bytes] (page-granular).  Shape of
   boost-beast/http_request's As/AsanNodesMmB.v [brk_grow_ok_aligned_refuted]. *)
  intros m d a sz h b Hbal Hdal Hd Hb0 Hnw Hin Hov1 Hov2.
  unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia.
  rewrite (region_free_false_of_overlap _ b (Z_to_bv 64 (d + page_size)) a sz Hin).
  - rewrite andb_false_r. reflexivity.
  - unfold iv_overlap. rewrite (u64_lit (d + page_size)) by (unfold page_size in *; lia).
    assert (Hov2' : (bv_unsigned a < bv_unsigned b + (d + page_size))%Z) by (unfold page_size in *; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hov1), (proj2 (Z.ltb_lt _ _) Hov2'). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_elim : ltac2:(zQ "hc1!jb!jkc!r7!j6!jl3!h9!hla!jm0!hn8!hnd!ho4!j0!hl4!hm0!jma!ij5!jn0!jn9!jvd!jo3!io7!kga!jof!khd!jp9!jq4!ju7!jv6&@2$7@1$0#k0@2$1@2$2@1$0#k0^6^8>1m$h0>1d$5=1h$h1@1$h3^2=1b@1$8@1$0#k0@1$h6^1>0@3$3$5@2$d@2$2@1$0#k0^1$4Z>0@3$3$5@2$d^4$4Z>0@2$6Z^5>0@2$6Z@2$2@1$0#k0^4>0@2$6@2$1@2$1@2$2@1$0#k0^5^7$4@2$hb+2+k0>0@3$3$9@3$ha^9~0~0$a@2$b@2$c@2$1@2$2@1$0#k0^7^9@1$h2^8@2$b@3$3$9@3$h4@3$e@2$f@1$8@1$0#k0@1$8@1$0#k0@1$h9^8@1$h8^8^7@2$7@1$0#k0@2$1^9$4$a@2$c@2$1@1$h5^a^9@1$h7^8").
Proof.
(* LPS 727298f3 port: written out (rule 11g), for the same budget form as the lemma
   above.  Shape of boost-beast/http_request's As/AsanNodesMmB.v
   [brk_grow_ok_aligned_elim]. *)
  intros m d h b Hbal Hdal Hd Hb0 Hnw H.
  unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H. rewrite Hureq in H.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in H by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in H
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in H by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z in H by lia.
  apply andb_prop in H as [H Hbud]. apply andb_prop in H as [Htop Hrf].
  apply Z.leb_le in Htop. apply Z.leb_le in Hbud.
  split; [exact Htop|]. split; [exact Hrf|].
  unfold Mmap.brk_grow_bytes in Hbud. fold h b in Hbud. rewrite Hureq in Hbud.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hbud by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in Hbud
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  replace (Z.max 0 (bv_unsigned b + d - bv_unsigned b)) with d in Hbud by lia. exact Hbud.
Qed.

Lemma sum_sizes_app : ltac2:(zQ "92!jb!hn8!ij5!kmd!hn1!jma!j6!h9!jkc&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["FPX1"] "h04__x1h12l1h27__arithh34__ffh48__varmaph55__with64__x2h74__x3h82IHh92ivh:2l2h;1zp;1p;2p;3p;4p;6p;5p;7g005`j13Tg006Ej1OTg006cj1DTg00<6j2@Tg00F8j1<Tg01JWj34Tg01eFj11Tg00>Wj20Tg00EXj1:Tg00lbj26Tg00G6j1>Tg00GTj1=Tg00m@j27Tg00H?j2NTg01^Yj35Tg00IEj4;Tg00J0j2MTg008Oj2LTg00JRj2KTg0042j39Tg00K>j3CTg00K]j4ETg01fUj3FTg009fj2BTg01^;j4GTg00g^j1HTg013_j6ATg01:?j3ITg01<;j5JTg001dj7?Tg00X]R0f1R1f0R239p=2P1g001Eg00_KR3P3g00_kR3P2g00a2F?p=8g00]^R4#3R5#3#3#3#3#3#OR6#DR7/@7R8#<R9P8A4821#1%12R:%11R;'0'2X19g00^_R<#:R=%<<R<1601%>0R>%=0R?P01704R@g016gRAg00\8RB,N0=50@C;'81M?3R3P2f2RCg00aRRDg00b2RE'L1K2C=9DEdAC0B1CEREb3b4b5X0010B2,22^00P2P;O1b2%:8RB=482#1%1B/0:'2eA482C#1%1CRB,0:'2P0f3R:#1RD,0;AF77:,B6R6/02106Bf4#1R7'0'2X;0P=P<P0160CP1160:CGP>P01705R5%H4,70R4550950@PAA50@5=504C;,8?P3PEb3b4b5X00X60X70101C,021021/0C'2^00^60^70P2P7PBP6O3b2A481:#1P2EAAI8C1RC=48:#1%1C/0D'2eW8X19X98P1DJX:9W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma Some_pair_inj : forall {T U : Type} (a c : T) (b d : U), Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##+4p'0h01th11Hh21Th31Uh41ah51bh61ch71di001oi011pp;2p;1p;4p;3p;6p200R0g00?4R1p4p710R2p8P0P!s4$210R3p8p201R4P2p8P4P3p8g00<6R3j22Tg002HR2j15Tg00<Vj40Tg00Uoj21Tg0042j34TP1j63Tg00M6j46Tf1R1f2R5f3R6f5R7f4R8'2R9#5P7P8P6P1C0,19!s3$5f0R:!s5$34f6R9?486A47511297R;P9P3f7R<P9f8R=P:P1n2001101000120!s#%X0;P!su&C0R8!s2$!t4$R1%5;R>P;P212<912=<P:P:P<!sI%C0n1011!sj$21!sr'>11;811;1P:E3R>E3P;P7P3!s[$!se$!tQ;8P1P>E3C6W1W7X55W6W4X34X20o"). Qed.

Lemma zfill_in : ltac2:(zQ "c0!jb!hn8!r7!u4!td!j0!j6!kr4!jkc!hl4!hla!jm0>1b@1$1@1$0#k0>1l@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1x@1$1@1$0#k0>0@2$5@2$9@2$2@1$0#k0^4@2$2@1$0#k0^1@2$a@2$2@1$0#k0^1@2$8@2$2@1$0#k0^4@2$2@1$0#k0^3@3$6@1$3@1$1@1$0#8@4$7^5^4^3^2@2$4@1$1@1$0#8@2$b@1$0#8Z").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##4`h04__p1h14__x1h24__x2h31bh47__arithh54__ffh68__varmaph75__with84__x3h92Hxh:1lh;1mh<1xp;1p;2p;3p;4p;6p;7p;8g005`j10Tg006Ej1G!s/$cj1?Tg002Hj1KTg009fj21Tg00XAj24Tg00>Wj23Tg00DXj25!sJ$Kj27Tg01O[j2;Tg01;=j2=Tg00?Qj2ITg00Uoj2HTg0042j36Tg008Oj2FTg01WFj2WTg00EXj1VTg00F8j1UTg00lbj2BTg01^;j4@Tg00G6j1S!s/$Tj1RTg00m@j28Tg00g^j1Q!sS$Yj3PTg00IEj4:!t:$ij1LTg00J0j2J!s/$Rj2MTg00K>j3N!s/$]j4O!t^$fj4ETg013_j6ATg011Ej2CTg014=j2T!tp$Xj1]Tg01g2j4\Tg01h3j6[Tg001dj7Z!tg$cj7YTg00nGj8XTg00aRR0f0R1g00b2R236p=2f1R3g001ER4g00_KR5P5g00_kR6P1E[p=>P3P4P5P5P6P1g00a2FZp=<f2R7!s>+3P1FYp=Df3R8!s;+7P3P1GXp=9g00]^R4#0R9#0#0R:#0!s$$GR;#?R<%G:R:#?R=#KR>\<11;8R?11;1R@'411;7RA,3?,5@'7P0P2P0P>f5R@,1;RBf4RC,1;RD'3RE,;ARF,=1g00\8RG,I:,H=R=P8P7O1R:n010!s#$20000=6>=X30!sx'1=21P=P!sK91F>=11;3R;13D?R?';R:%2:15AERE[15;?%2F[1W;?p-0R?g00X]RFg00^_R:#VRH%U:R:PF1BF7RIP31BF8C@%SFRJ%RFRK1>K@PF18F4R@g00`K18F9R9%Q4,8F5PFC:,<KR45DK%L5R5P4C91JK6R6P1P71F021M17#2dANFG3CORGb5b6b7X1FX2FW8W01337,51,781378,53[^1F^2F^8F^0?P114BAR2PDPBPAP3O5b4CEEA1CD;R0%20P2[14D;1CBA#2[1TD;PHP:PFPIP3%]FC@PJPKPFP@g017NP9!t~%91>KC5DKP5P9C9P6P!te0X0?1413/771437!t^'0?P1PEPAPBP3O4!tU%PCP8P7P3C\=6>=eW9X<<W;X:<W3o"). Qed.

Lemma region_free_intro : ltac2:(zQ "c1!jb!hn8!hnd!ij5!j6!ijc!hn1!ik4!ho4!in9!io7!iq9&@2$3@1$1@1$0#k0@1$1@1$0#k0>1L@1$6~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0>1a@1$1@1$0#k0>2sz@1$1@1$0#k0>0@3$b~0@4$7@1$1@1$0#k0@1$1@1$0#k0^2^1^5@3$4$2@4$9^5^4^3^2$5@3$4$2@3$a^4^3^2$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##1Np'0h01ah12szh21Hh31Lh41li001lh53Hinh62IHh72a'h82a0h91bi011bh:2loh;1nh<3sz'i022Ini032l'i041pp;1p;2p;4p;3p;6g005`j15Tg006Ej1E!s/$cj1>Tg00<6R0j2=Tg00F8R1j1D!s<$Vj46Tg0185j34!s/$Lj40Tg019Ej33Tg00EXj1<Tg008Oj29Tg01:?j38!s/$_j1;Tg01;=j2:Tg0042j37Tg01hWj3CTg01==j2BTg01i1j3?Tg013_j6@Tg01<;j6ATg00aRR2f0R3g01<]R437p=2g00b2R59723p=1g00]^#5!s$-E#>R6/=6R7#DR8P6P6f1R9P3C6R:f4R;547R<P;f3R=f2R>P9C0#2[^16^06P7A47:>R?f6R@f5RAP!sF1A39;=#1]2X38%<7947:PAP;!sL21925W2P0!tJ$8R0f7R5!sI'\?!sp+@A#1]2A87;=947:f9RBP0!t?387=>?35@#1]2[^48P3f;RCf:RD!sx6B0#1]2P6P6PAP;C6=87!t%%<PC!t#2P2P4%;3A3=CD':#1X92P9P=P>P9!sf$5P@C6!s0$>P9C6R@577A47@A;C3O3X5<X<6X76O1%;4A3>DB':#1ePDPBP;P=C0P3P;P=!sg$;P=C6R4=774p-0R<^48^07P1P7P<P3g00c1A779=!sW$3O2'Bn10110000020020!s4$3X48X07p?1001102P4P>O219743?O3E@A874>?3DB#1eW2W6X38X16X06P9P3O2n2!s]$4010121!sx$1X87P=P3EAW2X;6X:6W3o"). Qed.

(* [comment removed for export] *)
Lemma eager_used_sem_brk : ltac2:(zQ "h00!jo3!jb!h9!jp9!hn8!jma!krd!ij5!j6!jn0!ks4!kt1!lhb!lma!ln5!lnf>1m$9>0@1$e@1$3@1$0^1@3$8$2@1$c^2@2$f\1x$2@1$6@2$d@3$5@2$7@1$4@1$1#k0@1$4@1$1#k0@1$b@1$0^3@1$a^3^1@1$3@1$0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##'ih01xh11Wh21lh31mp;1p;2p;3p;6g01G;j11Tg01Iaj17Tg01iKj1:Tg005`j10Tg006Ej1E!s/$cj1DTg00<6j2>Tg00F8j1=Tg01jTj15Tg01kNj12Tg01JWj34Tg01lFj23Tg01mFj18Tg01n?j2<Tg01:_j1;Tg01oIj29Tg0042j36Tg020Uj3CTg021`j3BTg022;j3?Tg00BDj6@Tg023Xj1ATg01`4f0R0#1#7#:g00]^#0!s$-E#DR1/>1R1#=R2f1R3#1R4#7R5%54R4%23R6541R7'3R8g00X]R9%80f3R:#1#5%2:541/<0#;X09f2R:#1R;#7'936X22%88%5;!sK1/95R1569%:8AC7503B1354/36A?546E@%A3=691eW1W3o"). Qed.

(* [comment removed for export] *)
Lemma eager_used_cons_le : ltac2:(zQ "h32!jb!hn8!ij5!jo3!jp9!hn1!ik4!j6!kt1!lhb!loc!jn0!jn9!lp3!lq2!ln5!jkc!hl4!r7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$5~0>1m$b>1b@1$1@1$0#k0>1n@1$1@1$0#k0>2h'$c>0@1$f@1$4@1$3^4>0@1$e@4$6@1$1@1$0#k0@1$1@1$0#k0^4^3>0@3$7~1@1$4^3@3$a~0@4$6@1$1@1$0#k0@1$1@1$0#k0^5^4@1$4@1$3^6>0@3$7~1@1$8^4@1$8@1$3^7@2$h1@1$9@2$d^5^8@2$h0@1$9^8@2$h2@1$0#k0^6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##B]h01xh14__x1h21lh31zh42Hah52Hch67__arithh74__ffh84__p1h96__sat1h:8__varmaph;5__with<4__x2h=4__x3h>1vh?1Hh@2H0hA3Hc0hB2HmhC2HnhD1WhE2W'hF2WbhG!s{%0hH!s/%2hI1bhJ2h'hK1mhL1nhM1yhN2z0p&0p;1p;4p;2p;3p;6p;<p;7p;8g005`j1>Tg006Ek100!s0$cj1dTg01G;j11Tg01Iaj12Tg01iKj1ETg00<Vj48Tg024_j1c!s8$6j2`Tg00F8j1QTg01:?j3BTg0042j3@Tg01jTj1=Tg025gj4~Tg013_j66Tg0275j2D!s/$oj2UTg01kNj15Tg01oIj23Tg023Xj1JTg009fj29Tg00>Wj24Tg00XAR0j20Tg01JWj3CTg029Fj1ATg02:Jj1RTg02;NR1j1:!s1$nj3]Tg02=>j3;Tg02>GR2j1KTg01K4j1\Tg00=\j1PTg00@7j2[Tg00DXj2?!tR$Kj2F!s^$gj2GTg02?Dj1ZTg008Oj2H!s8$bl<{Tg02@Gj4z!s/$nj2xTg01==j2w!sw$0j2vTg00E4j3u!s/$Xj1rTg00lbj2OTg00G6j1q!s/$Tj1oTg00H?j2nTg00m@j2NTg01h3j6i!s8$cj7h!tU$ij1gTg00J0j2f!s/$Rj2jTg00K>j3k!s/$]j4eTg02APj2lTg00BDj6mTg01^;j4bTg00g^j1p!s8$Yj3WTg01fUj3a!s\$nj2sTg02C9j2tTg02DQj2STg01n?j2V!xu$_j1XTg02Edl<YTg00IEj4_Tg001dj7yTg00nGj8^Tf3R3f2R4#=f1R53Cf0R6'V#Xp=71V56#Xp=Ig00\8R7/06p=<g00X]R8g00bRR9P8P8P1f4R1P2P3g02FIP4P5P6M<Yp=}P!sG%8P2P2f5R2P1P3!sF-|P8P5g017NP6C_p=LP5g001ER:g00_KR;P;g00_kR<P6g00a2Fyp=MP3P:P;P;P<!sq%G^p=Tg01`4g00]^R=#>R>#!s$+R?$00R@#dRAg01`jRB%13#2#EPAPAP3P4C8#c1`AARC#QRD%24!s?$1P3C8%12#25BC3@%=3f6RE#1#=5@DPBP1%26RF#EX>BPD!sX$EP2C8RGf7RH#1#2RI5BC%E6X2DPGPIP4P3C~%21P5E61D1H#1RI1U1HE6%2I#EP8PCf9RI,DERG#1RJ%5GP6C7X08f8RG,D2RK#1RL#2'3%JI19@HRM'4,06X38P8PC%1IRN%5I!s[&RO%1GRP#2RQ'3RRPCf:RS,DHRT#1%5TRT!sN&%2J'3146M'0X38PBP2PCP5P!sE'/3FPC%1S%5SRF!t%'T%2NRN'3RJ/4MRU'0!u{$%5G%=HRB=CC5/I6!t&$E'3/0UX2D!vB&HPEC8RV=BCQRQACCBF!sP%/36!sN'%=PACC5!s?&!s\$GPHC8RF=BCN!sv'%AVRD%RV#:RV5]OA;ODV%KV'0%\H%<M%P>RH%P?R?'[RV,?M'FP819@GRM#:RD#KRNPCf<RP#1%5P!uN&!t:$SPIC8#A19@IRB#:3;/!w$%5PMPCf;RW#1%5W!sX/IPGC8#A;;DRI/0N1G7M,0IRW!{_$0P6X08RXP01056#ZXM8X08PIPI1H8IPNPX1G7!sI$NPMO1R0O1PXPX%K6,H8X09PDP0PXPNPMPM1H8MD}E|M<{P5CzPW1x7B1?7B1G7BRW=@8B'F10B7A@8W7'F'w19@S,G7P81vH?RS1?7H%<?1?7V[[RW%<HRBg00^CRNAuH?5UW4R?%<V\N^4BRBp-0RNg00^_RH#rRX%QHRH1O85%q8R0%o8RDPD!}B'1n871N8=R9'L,MDRY!sA,P3EiFh%g;R;PYCT1fD<R<P6P4g00aRRYg00b2R:'H1j64=@Y:dAk875CeR7b7b:b;X18W8%<6/F5%<5[^18^8NP6f>RN,9@R:/?VP:PEO3b6b9bHbNb@bA,lMEm10IMPSPWP?PBPXPHP81O84P51O83CbP0PD%p=,N8R=,L9,MDP;1N8>R>9W89AW8>=!uC$CTP<P!tZ,X<8X=8106414541443'0!tc$<8^=8P619@PR7PCf?RC#1%5C!|F'8%1N#2'3PAPAf=PPC8#A%:75;8P3O4b6bGb9b5b?%AFR3AaAAF,9@#:5;T/4J/0Ue%RF#:9;T3!s6&1sTF!s1&b513OQ19@E,4R'0e%=2P5E6%22P4E6%5K1t2GE6PL1U2GE6%JG1SG1E6%JK1SK6E6bEWCWBWFWDWJXLAWIWKo"). Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le : ltac2:(zQ "b0!h9!hn1!ij5!jn0!kga!lqb!lr6!lre!lhb!jkc!hl4>4Aset@1$1@2$2$0$0>1m$3>0@1$6^2>0@2$7^3^2@2$a@1$4^3@2$9@1$8^3@1$5^4").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["FPX1"] "p'0h01ph11Hh24__x1h34__x2h44__x3h54__x4h64Aseth73Hwfh82N1h92N2h:2N3h;2N4h<2N5h=7__arithh>4__ffh?8__varmaph@5__withA4cstrhB1mhC1zi00<minv_alignedi01<minv_allowedi02;minv_budgeti039minv_lazyi04:minv_nodupp;2p;1p;3p;6p;4p;8p;7g00<6j2bTg00F8j1@Tg02G6j1NTg02H7R0j2GTg01Qnj1CTg023Xj14Tg02I:j15Tg00>Wj23Tg00XAj21Tg005`j12Tg006Ej1FTg006cj1ETg02J>j10Tg02K>j2aTg0185j3;Tg009fj2WTg00@Tj2VTg0042j3=Tg02KZj2TTg01kNj1STg02Ldj2RTg01G;j1MTg01SQj1LTg02Maj29Tg02>Gj18Tg012Bj27Tg02NAj6ITg02OQj1HTg00EXj1JTg00lbj2<Tg00FXj1KTg01^;j4ATg00G6j1OTg00GTj1PTg00m@j26Tg00g^j1QTg02P6j3DTg00IEj4>Tg008ij1`Tg01^Yj3BTg00nGj8_Tg00J0j2]Tg008Oj2\Tg00JRj2XTg00K>j3YTg00K]j4ZTg02PYj1[Tg013_j6UTg001dj7^Tg00aRR1f0R2g00b2R33=p=:f1R4g001ER5g00_KR6P6g00_kR7P2g00a2F^p=?g00X]R8/b8#@g01`4%N4f2R9/G4P0f3R0P9%C0%40f4R:#5'3'1P2g00]^R;#2R<#2R=#2#2#2#2#FR>#ER?f7#0'af9#09;?21W>4g01_<R>'Vg00\8R@5=8[^0?f:#09;?2f<RA/T4#:[^0?f;RB#09;?2%SA,R4#:[^0?%4B%5A'3%MB#L'1P8%4A%0ARC,9?#8/7>RD'3f=RE#4f>#5'3,12XC8PEPCPBP:P0P9EI%5E,1D%0E,9?RE#H%8E,1@g00^_RE#J%@EP8P81<8:P9%K8CAP41<80CA%O8%P8REP5P6P6P7P8168<%Q;,685D8R<g017NR5168=R=C>,?E%`6P8168;R;=B8<P5AB8;=C>,?EG_1]E7P2P91\131X29#:dAY8@4CZb>b?b@X28X38X48X581749/101790,34134:'1[^28^38^48^58P2f@#5P>f?R>#0,9?#8%4>P9O5b=bAb1%CA%[AEUW<W;W:W9W8P:P0P9P4P2O5n2001000000151104100101103102W1W7WBW6o"). Qed.

Lemma in_ivs_cons : ltac2:(zQ "h01!jb!hn8!r7!ij5!ls6!lt0!hnd!loc!hn1!lt7!ik4!j6!h9!jkc!ltd!lu4&@2$3@1$1@1$0#k0@1$1@1$0#k0>1z$c>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1l@1$8~0@3$b$6@2$4^4@3$7~0@4$a@1$1@1$0#k0@1$1@1$0#k0^3^2^1@2$9@2$5@2$e@2$2@1$0#k0^3^4@2$f^4@2$d@2$2@1$0#k0^3@2$2@1$0#k0^2@2$4^4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["FPX1"] "h01ah11lh21nh31zp;1p;2g005`j10Tg006Ej1<Tg006cj13Tg00<6j22Tg00F8j1;Tg009fj21Tg011Ej2:Tg00>Wj24Tg01O[j25Tg01;=j26Tg02Qkj27Tg02S7j28Tg008Oj29Tg00X]g00]^#0#0#0#0#0#0#<R0#3R11211#;g00aRf2,10R2f3R3':f1,10,42,53'6f0,73'8'9W1X21W0W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seps_cons_inv : ltac2:(zQ "91!jb!hn8!ij5!lub!loc!hn1!j0!mga!mh4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1p~0>1l@1$5~0>0@1$3@3$4~0^2^1@2$6@3$7~0@1$8^3^2@1$3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##0zp'0h02H0h12H1h22H2h31eh41li001lh52H3h61pi011ph71Hh82l0h92p0p;1p;2p;3p;6p;4g005`j15Tg006Ej1A!s/$cj1<Tg00<6j2;Tg00F8R0j1@Tg01:?j31Tg02STR1j12Tg0042j30Tg02T`j14Tg000Gj33Tg009Kj26Tg00EXj1:Tg00BDj69Tg00NZj2?Tg00?4j68Tg00M6j4>Tg013_j67Tg008Oj2=Tg00]^#5!s$-A#<R2/;2R2%@2R3f1R4f0R5512#2P1f4R1f3R6512R79034f5R8#4=321%21'6R9[P5%:2R:f2R;=124R<503A126;R=903:P3P:P0P2p-0P5g00^Cg00c1R:n1011000002!s%$!s#$X33g00cNP7P5E9P:1?95b1W0P5O1W0%44R9=325%24R:f:R>f9R?512903=f;R@=12>9037P3P3P0P2P3P5P8P5!t:2!s4%X33A1281f<R7=12@P5E8A031@P3P2!sd$2P5f7R0P4!sf;f6RA=128f=R8=127P4E8A02A8f>9020P5f8R0f?R8502P2f@RAA03?ARAA329>%2@fDR@#4fCR9532R7%29RB'6]1]0[X62A0308P5PAP3fARA%4!us$fE!wG$@%2@'6^1:]0X43fBR:!s=$A%2:P7PBP4P5C>W5W2P>P5E7b5W1P?!s0$!vn&b!s+&W2P5P;P4O3W2W1W0X83X92P6P;P4P5O4n02!ur%!uu$141!v'+000A035=%41=326%26'6[X43P<O1P51=3=!t-$7W4W6o"). Qed.

Lemma seps_In_disjoint : ltac2:(zQ "c1!jb!hn8!ij5!iq9!hn1!mi3!j6!ire!mh4!lub!hla!r7&@2$2@1$1@1$0#k0@1$1@1$0#k0>1l@1$4~0>1p~0>1q~0>0@1$9^3>0>2iv~0>0@3$3~0^1^5@2$aZ@2$b@1$0#k0@3$5@1$1@1$0#k0@1$1@1$0#k0^2>0@3$3~0^4^5>0@3$3~0^4^6>0@1$7@3$6~0^6^5@2$8^7^6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["FPX1"] "##:ph03Hneh11qh22Hqh32ivh41ph51Hh62Hph72Hsh84Hposh94__x1h:4__x2h;4__x3h<4__x4h=1lh>1xh?1Dh@2HfhA3HivhB2HthC2IHhD7__arithhE4__ffhF8__varmaphG5__withH1hhI1tp;1p;2p;3p;7p;6p;4p;8p;5g005`j15Tg006Ej1`!s/$cj1WTg00<6j2MTg00F8j1JTg02STj14Tg0185j30Tg01fUj3<Tg009fj26Tg00DXj2PTg0042j31Tg00kAj13Tg02T`j22j18Tg00EXj1ITg01:?j3>Tg02V1j3]Tg000Gj37!sz$KR0j2YTg008Oj2FTg00NZj2XTg00BDj7=Tg02W?j3VTg021`j6ETg00lbj2D!u/$Xj1UTg01^;j4CTg00G6j1T!s/$Tj1OTg00g^j1NTg00m@j29!sS$Yj3ATg00IEj4@!tL$ij1LTg00nGj8QTg00J0j2K!s/$Rj2RTg00K>j3S!s/$]j4_Tg00>Wj2;Tg00XAj2:Tg01==R1j2G!u[$hj3HTg01hWj3^Tg01<;j5\Tg001dj7Z!uP$aj7[Tf1R2g001ER3g00_KR4P4g00_kR5f0R6g00a2FZp=?f2R7P3P4P4P5P2P6F[p=Bg00]^R8#5R9#5R:#5!s$&`R;#WR</M<R=#JR>P=%47f4R?90=6g00\8R@A<<<2,6;'PRA[^3=f3RB=0=?f5RC90=BA1=C?#3RDf6RE/2C[[[[[^1=^4=RFX=>%I=RG#4A0=6GP!sh$A0=BGRGg00c1f7RH/2EP7n010!s#%X0DX2GW6W8W7X1=X4=A>=?B#4A>=EC!tC$6!so,CA>=HE90=Bf9RCf8RA;]?%8C=7=A%4A'YP0f:#8=7=C%4C12AHP6f<R0#8f;RG57=%40P1f>RI=1=Gf=RJ90=G120GPHf?RG=1=0P=f@RKA1=6J#3122I]0X4=A1=K0RL#3P1fARM=1=JRNA0=JKROfBRP/2IPCA1=PIP=fCRQfDRR=1=6#3fERS/22RT]0X1=A1=QQ#312RRP61F=RO1'XW0PGP6P7F=W5P6O1A0=IM%8QRU=7=PA0=6RfF/22[^>=[RVA0=6QPT[^>=%8R=7=Q[RTAV=UPRUPEPGP6EEW2P6O1n20!w0'2!s-$11000W0PJP6PH!t=-0IP1PLA0=0G12IJPAP=PPA1=K6#312M2!u2'GP#3PVPTPUPEPKPBEE12QKg00X]REg00^_RU#I%JUPEPE1DE?P7%UECCP21DEBCC%TE%OERU!zs+E%N8,9ER319E:5AEg017NR:19E8R8C@,?URTPE19E99AE8P:P3!s;%35BU%L4ABU3TGQ1KU5P6P7g00aRRUg00b2R5'F1R67=1U5dASE@2C_bEbFbGX9EX:EX;EW<1;7B/:61;62/:7'G1;27/:B1;B?/:2'G[^9E^:E^;E^<EP6A<<<S,6;AH!s-&<<<P!s6&P,6;P2O5bD12MReb?W0PIP6PCF=X5NP6O1PKPGPIP?A0=6PPIP2A1=R2A0=2Q;^6O2WAX3=P7P6PCO7X2O!x0410!s3&W6!sB9!xL$BW@P2P6O2!sF-1!xm%00b7X0DW2!}#/XCFXI>XH=P6D\W=o"). Qed.

Lemma seps_NoDup : ltac2:(zQ "a1!jb!hn8!ij5!hn1!mi3!lub!iq9!mi9!hla!r7&@2$2@1$1@1$0#k0@1$1@1$0#k0>1l@1$3~0>0@1$5^1>0>2iv~0>0@3$6~0^1^3@2$8Z@2$9@1$0#k0@3$4@1$1@1$0#k0@1$1@1$0#k0^2@2$7~0^3").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["FPX1"] "p'0h02ivh11li001lh22Hsh34Hposh44__p1h54__x1h64__x2h71ah81xh91Dh:1Hh;2Hfh<3Hinh=3Hivh>2Hth?2IHh@7__arithhA4__ffhB8__varmaphC5__withD1hhE1ti012Ini021bi032l'p;1p;2p;3p;6p;4p;7p;5p;8g005`j12Tg006Ej1cTg006cj1NTg00<6j2FTg00F8R0j1CTg02STj11Tg0185j30Tg01fUj37Tg009fj25Tg00DXj28Tg02K>j2<Tg00EXj1?Tg02XEj1DTg01:?j3:Tg02V1j3^Tg02T`j13j29Tg000Gj34Tg009KR1j2UTg02W?j3STg021`j6RTg0042j36Tg01==j2>Tg008Oj2;Tg01i1j3MTg00lbj2LTg00FXj1KTg01^;j4HTg00G6j1GTg00GTj1ITg00H?j2JTg00m@j2=Tg00IEj4BTg008ij1ETg01^Yj3OTg02Waj7PTg01h3j6QTg00J0j2TTg00JRj2bTg00K>j3aTg00K]j4`Tg00>Wj2]Tg00XAj2\Tg000hj3YTg00kAj1XTg01hWj3ZTg02Xaj5[Tg01<;j5WTg001dj7VTg00nGj8_Tf1R2g001ER3g00_KR4P4g00_kR5f0R6g00a2FVp=Af3R7P3P4P4P5f2R8P2P6G_p=@g00]^R9#2R:#2#2#2#2#2#cR;#NR</F<R=#CR>P=%16A0=68g00\8R?A7<<2,5;'8R@[^0=1<=8[[RAX1>%?=RB#1A0=6BP@[^0=%D=W3W2A:=82#1f4RB=:=790=6P@[^0=A^B72%3B=4=7%17'UP1f5R1#3=4=B%1Bf6R@=:=1,<=P6f7R1#3=4=@%11P=f9R@f8RCA0=@CRCf:RD#3RE=4=@f;RF90=6f=RG/92[^8=[A0=6Df</92[^8=%3F=4=D[AS=E@P8PDP6ER19DDP1PFA6=FFp-0RE^1>^7=P0P=PEP6g00c1R0A6=27PBP7P6O2'>n10110000020020102103X1>X7=p?1001101PFPDO21;=F3MO2A7<<F,5;,8?g00X]R7g00^_RH#?%CHP71L78P2%K7CH%G7%I7RHP71J7?g00`K1=7:R:CB,AH%E4RIPHPHP3P4P4P5P71=79R9=O7:g017NP9CB,AHR9P9FPPIPHP3P4P4P5PBEQC@C@1TH5P6P8g00aRRHg00b2R5';1b68=6H5dAa7?2C`bAbBbCX57W6X4E18?21]28/\2R?/>?PB[[^57^67^4EP6P0A7<<G,5;AY<<G,5;P2P8O5b@b:b9W<%XCeP1P6A0=6@P1P2A6=F2A0=2D;Z6O2W=X0=O2D[W>W;P2P6O2n2001000000121000000b2W3W2X?AXE>XD=P6DWW1o"). Qed.
End FPX1.

Section SoundB.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!hn1!hs0@1$0$1").
Variable A : ltac2:(zQ "10!ovf$0").
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : ltac2:(zQ "40!jb!hn8!u4!hj6>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
Variable argH : ltac2:(zQ "40!hnd!jb!hj6!hn8>0$2>0@1$3@1$1#k0$0").
Variable FS0 : ltac2:(zQ "10!oo2$0").
Hypothesis SEGS_in_hull : ltac2:(zQ "b0!jb!j6!hs0!r7!np0!hnd!ijc!u4!pk5!pl5!hn8>1a@1$a@1$0#k0>0@3$1$5@2$9?1A@2$3@1$0#k0^1$6@3$1@1$7$2@3$8?4SEGS@2$3@1$0#k0^2+1@1$4$2").
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : ltac2:(zQ "10!pm0@1$0?1A").
Hypothesis SHADOW_ok : ltac2:(zQ "10!pmb@1$0?1A").
Hypothesis argH_high : ltac2:(zQ "90!jb!hnd!ho4!j6!pn8!hj6!hl4!hn8!r7>1E$5>1a@1$7@1$0#k0>0@3$3$1@2?4argH^2^1$2@2$6$4@2$8@1$0#k0^2").
Hypothesis argH_agree : ltac2:(zQ "60!hj6!hnd!j6!jb!og3!hn8>1E$0>2E'$0>1a@1$5@1$3#k0>0@3$4?3nx0^3^2@3$2$1@2?4argH^4^2@2?4argH^3^2").
Hypothesis SINV_frame : ltac2:(zQ "71!jb!hn8!u4!j6!hnd!ho4!hj6&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1E$6>1M~0>2M'~0>0>1a@1$1@1$0#k0>0@3$3$4@2?4argH^4^1$5@3$3@1$2@1$1@1$0#8@1^3^2@1^4^2>0@2?4SINV^4^3@2?4SINV^5^3").
Hypothesis SINV_agree : ltac2:(zQ "50!jb!hj6!hn8!u4!og3>1E$1>2E'$1>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@3$4?3nx0^3^2>0@2?4SINV^4^2@2?4SINV^4^3").
(* [comment removed for export] *)
Hypothesis RES_len : ltac2:(zQ "10!pnf@2$0?4SEGS?1A").
Hypothesis RES_cover : ltac2:(zQ "h03!jb!hn8!j0!ij5!hla!r7!mv9!mq8!pod!hl4!mi3!pp6!h9!ps7!iq9!jkc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@3$6@1$1@1$0#k0@1$1@1$0#k0^1&@2$5@1$0#k0~1@2$2@2$4@1$8?1A@1$7?1A>1z$c>0@2$2@2$9@1$8?1A^1@2$4^1@1$7?1A@2$b~0\2iv~0@2$2@3$e~0^1@1$d?4SEGS@2$2@2$9~2^3@2$4^3@2$f~2@2$5@1$0#k0@3$a@1$1@1$0#k0@1$1@1$0#k0^1").
Hypothesis argH_sp0 : ltac2:(zQ "a0!jb!r7!hnd!ho4!j6!ptd!o2!hj6!hl4!hn8>1E$7>1a@1$9@1$0#k0>0@3$4$2@2?4argH^2^1$3@2$8@2$1@1$0#k0@2$6^3$5@2$1@1$0#k0^2").
Hypothesis E_SP0 : ltac2:(zQ "50!hnd!ho4!j6!ptd!pub@3$2$0@2$4?3nx0$3$1").
Context {SC : StepCfg} {AF : AllocForced SC}.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
Let kn_grant_filter_ok := AsanNodesMmLib.kn_grant_filter_ok SEGS A RES_len RES_cover HULL_ok.

(* [comment removed for export] *)
Theorem node_exit_sound : ltac2:(zQ "10!mj2@8$0?2fx?4SEGS?2SC?1A?5LIMIT?4SINV?4argH?3FS0").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "#$lDp'0h03H17h12Hnh21pi001ph31Hh43H10h54codei01!s-$h61wh77__arithh84__ffh98__varmaph:5__with;2a7h<1eh=1oi021oh>1Eh?4FULLh@3G10hA3G17hB3H94hC2HChD2HEhE2HFhF3Ha7hG3Hc0hH3HechI4Hpc0hJ4Hpc4hK1RhL1ai031ahM1bi041bhN2c0hO2cshP5modeli052p0i062p1i072p2i082p3i092p4i0:2p5i0;2p6i0<1xi0=1zp%0p%1p%2p&0p;1p;2p;;p;3p;6p;4p;@p;8p;5p;<p;?p;7g005`j14Tg00g^j12Tg006Ej1L!s/$cj1[Tg01=Wk20MTg002HR0j1`Tg02Y=m;0=Tg02ZJk20:Tg02[Uk102Tg02\^j1!sX$=\j1:Tg00>Wj2sTg00?Qj2?Tg02]`j2qTg00Uoj2PTg0042j30Tg02^bj1nTg009KS00j2>Tg02_bk209Tg02`<j6QTg01L:j1FTg02aHj23Tg008Oj2U!s/$ij1{Tg02bOj28!s/$mR1j2RTg00DXR2j2OTg02cEj6tTg00EXk10!uo$F8k10K!s0$Xk10JTg00G6k10I!s0$Tk10GTg00H?j2XTg00J0k20F!s0$Rk20ETg00K>k30D!s0$]k40C!t:$nj4pTg02dYl@_Tg02>GR3j1oTg01?Sj2I!w5$=S01j2DTg02elk20!u4$fNj1b!s/$lj1mTg02gPj2lTg02h1k205!s0$Pk104Tg01[Sj1Z!w5$4k603Tg01hWj3iTg00M6j4hTg00BDj6YTg01i1j3gTg02i4j1]Tg021`j3kTg013_j8jj7|!sD$gk301Tg02jLk10!wq$kPk506Tg02lQk207Tg02mFl<~Tg02nSm?0;Tg02oej2}Tg00NZj2=Tg0311k40>Tg0326k40?Tg033:k30@Tg034Mj6zTg035Rk80ATg00XAk20BTg036aj2aTg037dj4cTg02?bl<dTg00IEj4yTg001dj7xTg00mck70HTg00aRR4f0R5g00b2R630p=Sf2R7f1R8g00X]R9/P530p=Cg00\8R:00B5p=Jg00[0,O5p=Hf5R;f4R<f3R=1?78%]5'aCcp=;P;P<P=%M7P8P5EQp=<%F5#Fp=\!s-$#F#Fp=K1378=0=5p=B%25#2p=G%25#:p=A1P95p=1%4!s5$E1U95p=Ng00bRR>P9P1P3P2g038kR?g01aaS02P:P=P!t@$M<dp=wP!sO+P?!t_%!sD-vP9P8g00`KP5Cyp=W!s4$1ER?g00_KR2P2g00_kR3P5g00a2Fxp=VP7P?P2P2P3P8P5K0Hp=rA0985p=5A09<=A0978'D/>5p=@!tA%g00cN!u~$Yp=61>78/=5p>0<%:5,P9p=7A09;<A09=7'D/>!sE$=9%4!v0$^%25#4p=T!sF$!t:$'Dp=f!uG%1?78/a5Ccp=e!t<%1a8!s5$ug039Mg00\Vg00]^S03#4S04#2R2#LS05Q04#4R?#4S06#4#4R1#4#LR>#[R@+0MQ06#L#[#`\@g01`4p,4SEGSRAp,1AS07p,5LIMITS08p,4SINVS09p,4argHS0:p,3FS0S0;P=P;!w=%N;0=f6RB-0:A#S%`9RCf7RD$02;CBf8RE#MRF#JS0<%:?R?,sF#H%L1#[RG%`GRHf9RI#MRJ,?>,qA1PG5RK30%n5#SRL'>X6G+09PAp,2SCRMp,2fxRNPAP;PFP<P=EQP>PDP=E;Q0<1sJ?#HPGf;S0=!s{,=0HKS0>/>LX6GPAPMPNPAPDf:S0?PBP;E<P>PIP;E;Q0>PL!sH+EPJPDPBEQP>Q0?PB!sF$%n8#Sf=S0@Q02#\#K#KRJ#F#\#KRL'3PC1UC5RIPCf>RKPLP5CBP0P9PCf@RH!s6/P8!s+$5%{9R?g03:RR<PCP5P!s+%?P!s4/!s@7?P?!t$&IRF/3JQ03#2RO#2S0A#2S0B#2S0C#G#ARP,85#1RQP?n10110<00021010100n0110:00031010;!s'$00P?!s>$9!s>':!s'$00P?!s@&8!s@'9!s'$!s@-7!s@'8!s'$!s@-6!s@'7!s'$00RR!s@&5!s@'6!s'$00!uZ&R!sb+!sH5!s>%0!s>'5!s'$!sz-=00030!u[%!s'$!ut4=00%1HS0D50C!xd'f?S0EfBS0FPKQ0@E<P>fAS0GQ0@E;S0H]1]0P8PCQ0GPL%15RSCB!x=&?P!tI<Q0G5CCfCRR/3JPCPIPCfDRIPJ!y6-FRT!s6&9PCPB!xp2!x~NPEP!xX~!xXZQ!xXBQ!xXU!w3;=CCT!x=+ERQfHRUPIPR!x:$GRVPRE;]1]4P8PCPVPJP!x1'D!w:W18EPS0I#1!v}~!v}EW!v}BW!v}m%1VS0J!|A$Q07Q08Q09Q0:Q0;PVPFPTPQPIPJP7PRQ02/RJRW%FL!#6$$#KS0K,RJRX'>%E2RY,O:RZ%:1R1,OYR['>R\PWPXPZP[1U9:S0LPJPY%NYR[CwPJPYP[Q0KP1%N1S0MEvEtg00^_R[$0LS0N&0K[S0O&0J9S0P&0I9S0Q&0G9R[1X9:S0R1X9YRY'W,V[1X91S0S,WY,V[3r20F[3S0TP5P71U4620E57#SdB0D9:8H0CS0Ub8b9b:P\P5b7CpP8M@_Q05%oJ'?R\,IT1?>750@%J7%H7'>'>Q001IV\1?>=!s>$=%H='>!z['PUfKR6PVPT!zY$JR4PTE;P51IF\1?>;!sY$B%HB'>P9fOR\/3LS0V=0CS!#3y'!znVHP#1S0W!zn~!znE3!zL;RY!ty&3!zp=!sd+!zrN\S0X50CP7%G2RZ#2#ERXP7%4Z#ARZfPRWQ0?/8P'5R]D@]1]0Q0@PCfNR^PL1P9:S0YCBACC?^PC!#6g$p-0P5g00c1R_g00^C!#6p$2!#6p$!s#$X<CR`Q0XP5D6P_A09:XA09:Z'D@0<]5b3W1W013WLS0Z%75S0[50C!uv$8PYP!u\<%1WR3!sP$fSRY!y'$\Q!sb/!x}PRP!#4j~!xzF]!xV;S0]!tw&]!x{=S0^!vF=YS0_50C%:7RaPXPaPZfTRa18KPS0`'5S0a!x[%P713aLS0b%25Rb#7Rc!vk,?P!to<%1aS0!sQ%fWRd/3LRe=0Cc!s`+!wGHTPRf!wI~!wI+Rg!wK=S0d!u[=dS0e50C%27Rh#:RiPXPiPZfXRiQ0F!|C$S0f!vg,iLRj%2bRk#7S0g50C%1iS0h90C?S0i!|M$`fYS0j#1S0kP5D6S0lP_%2=Rl#2Rm#:RnPXPnPZfZS0m18IPS0n'5S0oP5E9!|D%X2<P5O1%45Rn#2Ro#7Rp90Cj!wA&!ua>Q0h50CS0pP<f[S0q!|N$r=0Cp!|L0!wu<F!|>n!wY-!|@NQ0q#1S0s!u=$t%47S0u#2Rq#:RrPXPrPZf\S0v/5fS0w!w^'Q0v/3LRf%4bS0x#2!{M$r!{M,!tX>Q0v#1S0y!t>$zP<f_S0{!vU$|=0Cr!vU6!vO-fLS0}/8PS0~!vVS!v<-!{MNQ0{#1S1050CS11%4hS12#ARsPXPsPZf`S13184P'5S14!v;+13/3LRs%4kS15#2#7Rt!v97!tU4Q13#1S16!t;$7P<fcRg/3LS18=0Ct!#757!y[$\!y[<Ru!y]U%1gS19!tR$:%2hRh#4S1;#ARvPXPvPZfdRv18^!uj$<!}_,vLRw%2kRk#4S1=!ul$x!#5N-!tX<%1vS1>!t>$?P<fgS1@!uk$A=0Cx!#5S1?P?fRRu/8PRy#1Rz!xqQQ1@#1S1B!t:$C%2hS1D#4S1E#ARhPXPhPZfhS1F/5yS1G!x=,F/3LRy%2kS1H#4S1I#2#7S1J50CQ1F#1Rk90C?S1K!#4=%i#1P5D6S1LP_%GmS1M#4#ARmPXPmPZfjRm18aPRh'5S1N!#4442oS1O#2S1P#4S1Q!vi${90Cy!v'+?P!up:=0CkS1RP<fkRk!vd$S=0C{!s_,fURz/8PS1T#1S1U!sl9%1kS1V!vD$W%GqS1X!u6$qPXPqPZflRqfVR|/8PR}'5S1Y!xs,qLR~%GbS1Z#^#7S1[50CACC?qRb!v:&mS1\!v=']P_%^l#GS1^!t/$lPXPlPZfn18iPRl'5S1_!v=54nS1`#2S1a#GS1b!t7%c90C~Q!sx$4=S1d#4S1e#2S1f#GS1g#4#AS1hPXQ1hPZQ!s}'X1b!s~+13mLS1h%1ZS1i50C%1h=CCmS1jPCP9P0P9P9P5P5!s-$|P:!s-$PP:20885#b%L8%m5R0'l#b!vt$4!#De+4!s'$!sW'%L5%m8Rm'l#b205m0$04#Z!sZ9!s<$3!s<,!wm$3!#DJ/10=00X<CQ1UQ1VP5J03S1VQ1T/5kS1T15}qS1UP918dPR}15ZXRq15ZZRk'DRm155lS1k'>X59Pm15}}S1l%NZ9iqk%N}S1mChQ1\P5EYW3P5O1!wR%!#AY0!ti$001P8P5O2!wr-ffS1n!zE$oQ0B#4S0B#ARk#1S1p!|K$n#1S1q!|L%r!y8%Q1B!y4%BP_PkPXPkPZQ1G!xv,!tJ3!s4%!tJ4Q1O#4!|W$#7S1s90CwQ1>!t9%t!zK&eS1u#1S1v!t@%wP_Q1d#2Rk#2!yZ&x!{^,Q1n18WP'5S1y!zT4fbRq!u_$zQ0A#4S0A#ARm#1S1{!yb$qS1|!tJ%}!u]'9!tC%~P_P!~x&Q1<!u]81!w%+!u]5%4oS20!u[$2190CsQ16!t7$22!u[&aRo#1S23!t=$24P_%4kS25#AR!v|'0~,5qS0~!uL5^!#3L$26%4OS27!uJ&28!uJ$kS29!t9%:!uJ'0!t3%;!uJ/4!uJTQ1a#7S1a90CfQ0y!t2%<!uE&]!tQ%=!t8%>P_Q1f#:!#3B&18UPS1f,5kS2?!uF4Q0m!uE$@%:2R2#1S2A50CQ0!sx$B!t6%C!uB&0s!t0%DP_P2PXP2PZQ0w!uBT13|LR2%:ORO#1S2E!vX$|S2F!t<%G!t<'e!t<%HP_POPXPOPZQ0f!{[U0b%7nRn!#<g+!#L[=Q!#K4%A0Cen!sU%Q0d!sV?e!vL$u#:R]PXP]!tr$!#DA+x#7R]90CjQ0pP<Q0r=0C]Q0tQ12#:R!uL+!#Ds+15#7RO!xT%zP<Q0|=0COQ11Q1;!xA,Q!#B8-=#7Rl!{M%7P<Q18=0ClQ1:Q1E#:R0PXP0!|V$!sX,I#7R0!~\%?P<Q1A=0C0Q1CQ1D#2#E!#>7&Q!#>/-H#T#7S1H90CyQ1KQ1LP_Q1M!sV1!#=P4Q1P#T#7Rh!s^%RP<Q1S=0ChQ1WQ1X!se$yPXPyPZQ!#;|+Q1Z!t=%Z!#:b'Q1^!sS1!#:N5Q1b!s]%b!s]-g!s]$~PXP~!s]<h%1XS1_50CQ1jQ1VQ1TQ1UP9P}15XXR}15XZRb'DR~Q!#8g&~Q1l%NX9g}bQ!#8``Q1oQ0C#ERb#1S0C!tS$rQ1BP_PbPXPb!#8:ZQ#7S1Q!xU%tQ!#7p'#ER!s}+y!wv6zQ0B#:!t[%B!t[$}Q1~!t[/!#78TQ1O#7S1O!zd$22Q24P_Q1x#:!tY+!#6h5Q26Q0A!tY'A50CQ2:Q2;!tY/!#6GU20#7S20!|q$2<Q2>P_Q25!tY-!#5{62@Q27!tY&27!tY$CQ2D!tY-!#5^UQ1`#7S1`!~~%iQ0lP_Q1e!v4/!#T?4Q04!v1'490C2Q2GQ2H!tW/f!tWTPCPuPLQ03!t$'3CB%1uS2G90C?!#75&_!#_L$!t7,a!t741!t7'!zS;0Z%Z5#1S0a50CA0C?3!t+%fQ!tG%f!t2%%Z=R=PXP=PZf<R=/8PR},5u!v'4!#bk%103!tB&!uX$P=P;O2Q0@PXQ0@PZfMR=18DP'5D@Q00PKPXPKPZCfQ0I,5^!#gT'=PWQ0}P6E<P>P\P6E;P5PHPXPH!sS%=/8P,5bP9P}P9PCPR!#gEVQ0n!#\z~!#aEEH!#o1AH!#s0m0CS!v}+u%MzS0nPbPWEQS0=P>P8%]WS0IEe]1X59P9PCQ0F!vL'Q0]Q!#bZ<!#tK=}Q0115RX15RZQ05%oL'?RR,IuR}1?>XRH50@1?>ZR~90@}'DP715IXP9PXA0Ce!#li]Q1!#bF~!xJG}!xJB}!xJmQ0G/8P5CC1I|RR}=0@HA0@}~'D]1]0X;9S0GQ1_90C2Q0WQ0W50CS0W1Iz!sT&Ry!sV$R}%JX%HX'>!#uF4|PiPzPaPYPLPXPuQ02/RLS02Q0K,RLS1f'>Q06#ARX,O:S061OX1R:'>S05Q02Q1fQ06P:Q0LPLPX%NXR:Cw!sq$:Q0KP1Q!#u9$Q0NQ0OQ0PQ0QQ0R1X9XRX'W,V[Q0S,WX,V[5r[Q0TQ!#tP&Q05!#tQ$R[P8M@_5ky3gW1W0PQP5PIP7Gj!#>G$15IZP9PZQ0GQ1i!v&&%JZ%HZ!ufCZPuP!t+'}9iy}!t-7n20!#7z$002!x'$!s'%IbRRR!wX&R~'DP@1?>KRR1?>P601!#uw&Y%M|RP,?>Pu&00AR~I06007bP5%]bRHDuXM@!}q$MPuQ0n,?>PbP~PWP4PRPFPU!u75YPzPuPbPWP\M<~P5PEN?0;Q0`,?>RR1}KDEYPAPMQ0=PRQ0IDuebAW1PuP5Q0?F|W3WF!#9+$!uP-1!#rM&bBWGW@!sF>LW1W4XN9!#:s%QPJP?!$#b%;!~/W!{b&!~+4RJ!~-;RR!~0=RK!~2=R~!~4>@!}j;RI!tz&@!~6=!~r+!~84Ry!#6C=Q!vT$UPLP!$0O-!sX<%1URy!$1],PVP4PTPQE<P>PFPQE;RQ]1]0PBPCPVPLQ0YCBQ0J!#?G+Py!#>:$1=Q!#w_'FLRQ!#vw/IP!uD=}%1FRI!sR&Q0}PLQ0[CBQ0}#1Ry90C}!tk+6P^P4PF!tk$=PFE;R}!#`=&=LRB!#si/!wC=T%1=RS!t?$Q0Z=0CcA0CT3!t4+\PuP^P=!t4$bP=E;R=!t4'bLR^Q0g50CQ0f!uz,Q2G!u{%!sj+bPaPWP\!sj$YP\E;/=!v<$R\!#A;'A0C^!#pi&!y\?~Q0f50CRWP<Q0b=0CpQ0c90C~!t;+YPPPuPbEQP>PzPHEeRH]1Rb!u%%zLRu!#nL,!{2?K%1zRP50CR~P<A0CjrQ0h90CK!t8+dQ0mP|PzE<P>Q0jPzE;R|]1RK!#S=$j/3LRr!#lP,!|d?RQ0k50CRp!t:$ft!#Xm$R!t:'Q0qPkQ0mQ0j!vd$!s/$;RR]1Rt!uP%mLRT!#jw/!~<=JQ2=50CRc!t:$sx!#\H$J!t:,{PqPkPm!t8$oPmE;Rk]1RJ!t7%oLRxQ!#jB$23!xd-1|!xd2oPvQ13Q0{!sn$gQ0{!xg,[!xg/x!#i>,!#4[;ZQ2350CR2!u'$w{!#a&$Z!t<+gQ1nPqPo!wS$1uPoE;Ro]1Rq!wS$1u/3LRZQ1[50CQ1v!u-/q!u-1Q1uQ1FPvPg!sq%@Pg!u-,g!#Lf,c!tN$!s8/8Q1i!t-$9!t-/>!~q'o!sj%o!#S[9!#K06|Q!#e#%0!sx/6!sx'k!sx%k!#SWMs90CTQ2=!}f/9!x$2m!w~$vQ0q!{A%{Q0q!uz,m!tn-rQ1{!~^$s!sv-0!#5['R!sX%R!#R7M190CrQ0k!tn/B!wh20jQ0vPiPd!tm%qPd!tl,v!sr-890CeQ0e!tj/h!tj'|!sV%|!#cDN90CuA0C?P!th'F!vX2zPiPaPY!{X$dPY!te,Y!vS-\Q!#b}%_!tg/c!tg'H!sX%H!tgM0VQ2E!sx$X!sx,P3!sw'!tQ&d!y<LA0CB!#ao%!#='?@=0CS!#9-&nA0C@3P!#8l%A0C^]!#7J&]Pb!s:&uO!}u$jOPK!s8&rl!s8$flPt!s8&T0!s8$s0PJ!}r%H90CxP!#390h!~e%hP!~>&Z!}C4b!}U7_50CP!}7BX12!}800C50CP!|rBX1c!t8-Q90CTP!|710B50CP!{qBX1p!sm-O90CrP!{8-0A90CeP!zrBX1~!{k-090CuP!z>2750CP!yxBX1W!tZ-`90C^P\!z300450CPd!#ZAN6PLQ03!$;'$6!#Aj2}5!#[88!#Z#;a90CQA0C?I!sq%%14!}G2FQ0}PUPV!}H$6PV!}H+!#Yu20!#Yu1;!t;&4!#w;-!sP$1P5P7O2b4b=!sm$;!#Hx%Q0EPLP?CBQ0E9C!~7,D!ta%Q0H!tI+!sz'1!sz'0P5PDO2b0b=WDWEH0>X6GH0?WJWIB0@AE8EzW1WHWCWPW?WKW>X59WO!uY$M!#L-1L0Aeo"). Qed.


(* [comment removed for export] *)
Theorem node_sys_sound_YSetTid : ltac2:(zQ "20!mjf!mk9@a$1?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0$0").
Proof.
(* LPS 727298f3 port: written out (rule 11g); the zQ statement above is untouched.  The
   recorded replay rebuilt [cs_ok] positionally with the old one-equation [co_res]; this
   proof keeps every field from [cs_ok_agree]'s record by [assumption], so [co_res]'s
   current form passes through unchanged.  Shape of boost-beast/http_request's
   As/AsanNodesMmB.v [node_sys_sound_YSetTid]. *)
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  cbn [node_sys] in Hn. unfold node_settid in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (negb (a_tidset cs) && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hts Hfresh]. apply negb_true_iff in Hts.
  apply Some_inj in Hn. rename Hn into Ecs'.
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 96 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_tid _ _ _ _ _ _ _ _ _ _ _ HC Hts) as Htid.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  unfold cfg_of.
  eapply (srz_set_tid_lazy SEGS); [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact Htid |].
  intros tid Htidr.
  set (v := nxt cs) in *.
  set (E' := ext1 E v tid).
  assert (Hag : env_agree v E E') by apply (ext1_agree).
  pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH E_SP0 argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
  rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
  replace (pc cs + 4) with (pc cs') by (rewrite <- Ecs'; reflexivity).
  apply (Hk E' (regupd R 10 tid) FULL (with_tid tid model)).
  - split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
  - assert (Hv : edenot E' (EVar v) = tid) by (cbn [edenot]; unfold E'; apply ext1_at).
    assert (HMr : Mr A argH E' cs' (with_tid tid model) FULL = Mr A argH E' cs model FULL).
    { unfold Mr. f_equal. apply functional_extensionality. intros a. rewrite <- Ecs'.
      unfold hid, vis, in_allow, in_vis, in_sh. reflexivity. }
    assert (HA : allowA A E' cs' = allowA A E' cs) by (rewrite <- Ecs'; reflexivity).
    subst cs'.
    destruct HC'; constructor; rewrite ?HMr, ?HA;
      cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
      try assumption; try reflexivity; try discriminate.
    + apply (regs_ok_set_n); [exact co_regs0 | lia | exact Hv].
    + constructor; [|exact co_know0].
      cbn [kentry_ok]. rewrite Hv. unfold PID_MAX. unfold PID_MAX_ENVELOPE in Htidr. lia.
    + destruct co_minv0; constructor; assumption.
  - reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brk_keep_ok : ltac2:(zQ "h30!jb!hn8!ml5!u4!ira!jn0!jo3!jof!iua!mle!mm6!mmc!mn1!mna!hj6!jj6!jkc!jk0!jk5>1E$e>2cs$a>1R@2$8@1$0#5@1$1@1$0#k0>4FULL>0@1$1@1$0#k0@1$3@1$1@1$0#8>5model$5>0@b$2?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^5^4^3^2^1@b$2?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^6@2$c@3$d^5Na@1$9^5@2$h0@1$b^5+4@3$f^4@3$h1@1$0#5+aKv$4@2$h2@1$0#5+a@1$7@1$6^2^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "##7-h01Eh14FULLh22HCh31Rh47__arithh54__ffh68__varmaph75__with81ah92csh:5modelp;1p;2p;;p;3p;4p;<p;6p;7p;9p;Gg005`j10Tg00g^j1jTg006Ej14!s/$cj1@Tg01=Wj2iTg002Hj1WTg02Y=l;STg02\^j1MTg00=\j15Tg00>Wj2GTg03>Ij1FTg03PEj19Tg03G:j1eTg04A8j3XTg03RXj1VTg03=Fj1UTg04R2j4TTg01A7j3RTg01G;j1QTg01H2j1OTg01Bbj3LTg04cgj1KTg04e>l<ITg04fKl<HTg02bmR0j28Tg009Kj2:Tg00DXR1j2;Tg008Oj22Tg02cEj6NTg00EXj1?Tg00F8j17!s/$Xj1DTg00G6j1P!s/$Tj1CTg00H?j26Tg00IEj4=Tg00mcj7hTg00J0j2g!s/$Rj2dTg0042j3>Tg00K>j3c!s/$]j4Y!tL$nj4ZTg007Fj2[Tg04gXl<\Tg01UVj4]Tg04DUl9^Tg01>Cj3_Tg04hdl<`Tg03b3j6aTg04j1lGbTg01L:j13Tg02?bl<ATg001dj7fTf0R2#3#3p=<%3!s0$#3p=1g00bRR3g00X]R4P0g02>GR5P1g038kR6g01aaR7g00\8R8f3R9f2R:f1R;P2M<Ap=JP3P4P0P5P1P6f5R6f4R1P9P:P!sH'EP;g001ER5g00_KR0P0g00_kR3P2g00a2Ffp=Bg00\Vg039Mg00]^#0R<#jR=#4R>%0<R<#0R?#0#0R@#0#4#@RA'i%4?#@#WR?\Ag01`4p,4SEGSRBp,1ARCp,5LIMITRDp,4SINVREp,4argHRFp,3FS0RGP!tz,;SPBPCPDPEPFp,:SINV_framePGP6!sN'%M1%5<'G%F1#9R<%<7#1#1RH%e1RI3X%V1%U1CTRJ%0=#5R=g00cN5R>%Q;#OR>5L9RK!t>%%K;!t>,!t1/P2M<IP6P<P9PHPIP>!sM=H187HR7%<H#1!s$'R<,8HRL':1;8=RM%5@R@,;=RN':ROP7PLPMPN1248PHP=124=RNCJPHP=PNP<P@124@EEENg00^_R<#?%7<%D4%P4%C4R<P5P0P0P3P41648g00`KR0164=R=C=,B<P4P=P0164@!s5$Fh1g<3P2P:g00aRR<g00b2R3'21d2:=><3dAc48;CYb5b6b7POP2b4CZPAP>1[6I!uq=\C]M9^%9J=_6Keg04ZjRK#7%?K'2!s\=`PCPFf6P6P:P2Ea=><3P1P;O1,2?UX8AMGbW2W:W1W3W9W0o"). Qed.

(* [comment removed for export] *)
Lemma brk_req_sound : ltac2:(zQ "h80!jb!h9!j0!j6!hn8!u4!hm0!r7!td!jn0!jo3!jof!iua!mm6!mo4!moe!ml5!o2!hj6!p2!hl4!hla!jv6!hma>1E$h2>2cs$d>1R@2$c@1$0#5@1$4@1$0#k0>4FULL>0@1$4@1$0#k0@1$5@1$4@1$0#8>5model$9>1d$1>0@b$h0?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^6^5^4^3^2>0@3$3@1$5$1@1$e^6@2$8$1^2@2$2@2$h5Z^3@2$2@3$3$1@2$6^3+hgg0Z@2$2@2$h4^3@2$h6+2+i8@3$3$1@2$6@2$h7@2$7@1$0#k0@2$h1^8@2$f^7Na@2$7@1$0#k0@1$b@1$a^4$h3^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "##D-p'0h01Hh12Hch21mh31nh43Hldh52H0h62H1h72H2h82H3h91bi001bh:1di011dh;1eh<1Eh=4FULLh>2HCh?2Hmh@1RhA2_HhB1ahC2cshD2d0hE5modelhF1oi021oi031xi041zp;1p;2p;;p;3p;6p;5p;4p;<g005`j1ETg00g^j1lTg006Ej1N!s/$cj1[Tg01=Wj2fTg002HR0j1VTg02Y=l;_Tg04kBj1]Tg0042j30Tg04lIj2:Tg03G:j16!s^$jj2FTg008Oj2YTg00=\j1RTg00@Tj22!s/$7j2`Tg011Ej23Tg01;=j29!s\$ij1^Tg01G;j1@Tg01H2j1?Tg00?4j6\Tg01blj3TTg009KR1j28Tg01O[j2GTg00DXj2ATg01WFj2kTg010hj2I!t<$bj2jTg00XAj2CTg014=j2iTg04mLj5hTg007Fj2LTg00M6j4PTg04gXl<dTg013_j6cTg00BDj6OTg00NZj2WTg00Uoj2bTg01L:j1U!ti$fj2KTg00:Pj2QTf0R2#E#Ep=Bg00X]R3/b2p=>%U2#Up=Hg00\8R4,I2p=Zf1R5,G4/92p=a1A42p=5A0324p=7f6R6f5R7f4R8f3R9':'L'Kf2R:/K5'Qg00[0R;'2=032p=<1C:5/82p=41852,8:p==1G4:1252/I4'9p=;g00aRR<g00b2702p=1A0352p=D1G42p=M!sS&p=S1L52,K:p=J1Q52/2;p=g!sS$!t$$e1:9:,L8,K7/Q5/2;!tS%Xg00\Vg039Mg00]^#ER=#lR>#N%B=R?#E#BR@#NRA#[RB'f%N?#[#V\Bg01`4p,4SEGSR?p,1ARCp,5LIMITRDp,4SINVREp,4argHRFp,3FS0RGP7P8P9P:P5M;_%V3RH%]7%>5RI30g01aa#H!s$'RJ,:6%66'FPH1YH2f7RK/:J%6K'F=0H2P0P3f9RL!s:$L!s:,PHP5P<PH%B@#B#B#RR@,22RM#Z,a2%R=%E>#B#R'`R>,32'9%>2R=%^3RNn010!s#$20000PNn10110300021010100%>6RO50H%5K12K@#7PAf<RPf;RQPJPAf8RR#@#?PKF<94K>3=RS]0]4P5f:RT!tw$T!tw$=P<PHA;55@135>'9PIP!tL2%>K50HA;::@13:>'9P<1Y<2A;99@139>'9=0<2P<A;77@137!s7+!uu$O!su5PRI50Hf=R=#512=@RU!u4$BfARV!u2$>RW!u2$=F<94=>3=RX]0]1P5A;88@138>'9R8#1%>7RY%>QRZ50HPHP3!w;$3P2P2PK!vQ%2!vQ'400X;HPOPIP2E\1D6P1DK=P3PR%52%7MPAfDRMfCR6!tQ$@R[!tQ$2F<942>3=X:3A;RR@R\13R>R];T9%1\%1]'8P1A;LL@#113L>#1%5T12T!wX%ER]PMPJPA%@V#?PTF<94T>3=P2A;QQ!sY$P>#1%M=R=%ZURU;T5%1=%1U'8P1%MW#11SW@#1f?RU#512U!s~%JR=fIRP!ty$F!tw$UF<94U!t%$%M[#11SV@#1P11G52#11A:5[RV1A521G:5#1R[[1A9:\[1k52P5n20!wk'1!wl$000X23X33PV^23^33P2P4P6P:O3%56P11I!s}$D:5[R61D521I!s}$V[1D9:\V1j!s}B6!s}'12]@R]P4P9O3%7]P113!t%$C:5[R]1C5213!t%$6[1C9:\61i!t%B]!t%'fGR]P>PTO31C]>fSRTfRR6/:JR9%66RVfHR[P]Dh1A[;944[AJAT9AJATV'g;e[P11AP;944PPAfTR1PTPJ%6T9JA1PPEX%5=12=!wV%URPP1!wT$Q!zx1P2fKR=1A=;544PAfWR4fVR=PJ%6=9JA4fLEXPBfXR;%64'LRTfNR[#512[!t#%YP;PJPAP2P[F<94[>3=X9BfMRB#512B@#7R@1CB>R>PAP;P4!sS$TPBF<RB'8RT'8PLP@PTPKP>PBP7P2CPCPCP%@1#?P?PCPDPEPFPG!sc$=PPP1P6M<dEcW?WAP5P2O2!w10!s/&bBb8b0b7b0b6b0W7W6!sR>1W8W1!sF?PWP2EOW0P2O1b5W0W1g01<]90<8A0HNZPHPNP0P3p-0P2g00c1R0g00^C!~C0!xr%;HRZg00cNR8!~J$OP01WX2!s}%n01!sN%20100P2P:O2b1b9W0W4XD3P2O11:RJ%6R'F=0HNA0HNY!tL$ZP8PO!su'S!su%4!tM/1104!sy+4bFW0W>X:3WEW=W@WCW<o"). Qed.

(* [comment removed for export] *)
Lemma brk_base_ok_sound : ltac2:(zQ "h70!jb!hn8!r7!j0!j6!h9!hl4!hnd!u4!ho4!jn0!jo3!jof!iua!mp4!mm6!mpa!mq8!ml5!hj6!jkc!hla!hm0>1E$h3>2cs$f>1R@2$d@1$0#5@1$1@1$0#k0>4FULL>0@1$1@1$0#k0@1$8@1$1@1$0#8>5model$a>1d$5>0@b$h2?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^6^5^4^3^2>0@3$4$7@3$h0?1A^6^2$9=1b@1$1@1$0#k0@1$c@1$b^4@2$3@3$4$5@2$h6@2$2@1$0#k0^1+hgg0Z@2$3@2$h5Z@2$2@1$0#k0^1@2$3@2$6@1$h1?1A@2$2@1$0#k0^1@2$6@2$h4@2$2@1$0#k0^1^4$e").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "##RNp'0h01Hh12H0h23Hhih33Hloh41bi001bh51mh61nh72Hhh82Hih92Hkh:1Lh;1Ph<4__x1h=4__x2h>4__x3h?4__x4h@4__x5hA4__x6hB4__x7hC1oi011ohD1EhE4FULLhF2HChG2HKhH3HalhI1RhJ7__arithhK4__ffhL6__sat1hM8__varmaphN5__withO2cshP1dhQ1ehR2hii022hihS2loi032lohT5modeli041xi051zp&0p;1p;2p;;p;3p;<p;6p;4p;8p;7g005`j19Tg00g^j1ZTg006Ej1R!s/$cj1]Tg01=Wk207Tg002HR0j1dTg02Y=l;yTg04n[j3tTg01G;j1KTg01H2j1GTg03RXj13Tg03G:j12Tg00fRj2[Tg04ofj2BTg050lj2@Tg0488k100Tg011Ej28Tg01;=j25Tg01blj3TTg009KR1j26!s1$fj24Tg00=\j1sTg00XAj20Tg00>Wj2:Tg008Oj2\Tg0042j3!u8$Uoj2kTg01O[j2STg00DXj2NTg01WFj2jTg014=j2iTg04hdl<hTg03lij6MTg00eBk406Tg0522k805Tg007Fj2LTg053Dk804Tg054Vk703Tg04gXl<YTg013_j6XTg01VUk20!v'$@Tj2gTg01L:j1J!s/$Yj2eTg01Mkj2QTg01[Sj1~Tg01\1j2}!s/$Rj3|Tg00EXj1{Tg00F8j1xTg00lbj2W!s8$Xj1wTg01^;j4OTg00G6j1v!s/$Tj1uTg00H?j2`!vC$ij1_Tg00m@j2^Tg00IEj4P!se$Yj3aTg00J0j2r!s/$Rj2qTg00K>j3p!s/$]j4zTg00BDj6oTg00NZj2c!u<$Bj3nTg01:?k301Tg001dj7fTg00nGj8m!tD$cj7lTg00aRR2f0R3g00b2R437p=1g00\8R5/S3p=<f1R6/:3g055iR7'8p=;g00X]R81g63;75p=>1N53p=A1037p=Df2R91663'6p=C1e83p=IAn863p=Eg00^_R:@0163p=F1^83p=HP9g001ER;g00_KR<P<g00_kR=P8P6g017NP3CPg00a2R>Ffp==f3R?P;P<P<P=P9P6P3Gmp=?P6!s;+3P!sP$UP9!s9+6P3Flp=VA7835p=bg00\Vg039Mg00]^R;#9R>#ZR@#R%9>RA#9RB#9#9#9RC#RRD#]RE+07%RB#]#d\Eg01`4p,4SEGSRFp,1ARGp,5LIMITRHp,4SINVRIp,4argHRJp,3FS0RKf5RLf4RMP?P9P6M;yAtGL6#1%K?#GPEf7RN#3RO%2NRP'[RQP0P8P21BOP!s0%f8RP!sG%PRR'@%<6&00GRS/86'5RT1;3L'5g01<]RUn10110400021010200P!s:3300RV;T6%1Q%1V'6P11[OR#1!tE+R!tE&9RR#3%2R'@f6RO,;3,5TP!t0J#114D9RV%9C!vq%!s$$sRC'>%AV10SV1:VL#D'63CP3f:RV#3%2V'[!tV'f;RQ#3%2Q'B!s7&<RW#3RX%2WRW'@1;3R!t^QBXW%d8RW1\W3RXf=RY#3%2Y'B=7W3P0P8f?RZ#3%2Z!s9,P2P6!tM&A!sC'@R[f>R\,;3R]!v0SVRT/>C%AT10ST1:TY!ux%RT]0]3P6f@R^#3%2^'B1k83R_57W!tU&[%<918S9'5/5]!tB7#1fBR]#3%2]'@PWPXfCRX#3%2X'@!uX+E!sH+!uX/%<N18SN'5R01;3X'5!t-914D^R[!u6$[10S[1:[X!u6&[]0]2P6fFR`#3%2`!t-$_1;6X,50#1%<P18SP'5R0fDR_,;9Ra;T3%10%1a'6P1%<R18SR'5#11;?]!t:$XRa!t:$a10Sa1:a`!yD'%<Q18SQ'5#1fHRa,;O#1%<YR`18SYR0!{A$`%10!t#%\#118S\!sy$aR0!sy$010S0fKR`,:0!s|,^!sP$Z#1P11S63#11N96[R^1N631S96#1R0[1N?9\01j63P6n20010!s#$12!s-%0X58X68P^^58^68P3P5PXP9O3%AXP118!s}$096[R1106318!s}$^[10?9\^1i!s}AR^P1!t#%R1P3PSP]P?O310S]P^P1P3fSR1,:ZRZP7PVO3%DZPFPGPHPIPJPKfYRZfXR^fWR]fVR0fURbP1M<hPFPZPGPJPZP^PbP0EM%3^H06PFfZRb!s@$bPZP0P]EM%3Z%2ZR0fI!tQ$aL051Lb0,4D,01PFf[R1!sW$1PbP]P^EM%3b%2bR0P_P6PXL041L10,4D/0_PFf\R0!sU$0P1P^PZEM%31%21RXP9fPK031L0X,4D/>CPEf]RX%20'LfM14D3Rc'0X4EP9%KZ#GRd!ua/PX!sx$bPZP]M<YEXfL14Dd'0PEf^Rd%2X'L10ca!sf&b#GRa!sf0d!sh+^!sf$14DafG!sf$_Ra%2d'L1>cC!sf&1#GRE!sf0a!sh+Z!sf'E/>C%K0#G,4DR0002C1050105CR0%Kd!s>%d/gCRE,05[[g01aaRZ#JRa#JRK#JRJ#JRI#IRH%Ia1e8ZRZ'E'Eg01b@Ra'QRG%IK/EZ,EH/QaRH%JIRI#I%IJ/EZ'E/QaRJ%~;,}8%JI#I5|8/EZ/Qa%{:'F,FG,FH,FJ'F'F'F%x:P8P8P81W8NPM%w8R:COP9P:COP6!s=$LP?1W8OCOCO%v8%u8ROPO1`85RL%H>R>5=O%_<R<!s;$C9=OLP<1^8;R:9=OLC?C?P<POP8P:g016gPLCP,UOR:P<PO%HBRB9=O>!s3$Z;R;#Z#HRJ=!s9'HARA9a8B%H@R@5=O!s;%;R;==OJ!s~&Lg00`KRBPJ!t$$P<P8PLPBP>!s5$A=O;>Aa8>A==O@5VO5VO9VO:C?!s$/1rO=P3P91\241q39#1dAp856CzbKbMbNX<8X=8X>8X?8X@8XA8XB810561059\0[%b610?P10PM1:VN/0P10NV%AQ%bN%AP10RP1:PV/0Q'63C[!s#%^<8^=8^>8^?8^@8^A8^B8P3P`fQP7PXPSPdPEP6P9P?PMPRPQPYO>bJbL14D^R^/>C%A^10S^1:^1!#56$eb;b7b:!s+&Gb9b0b8b0b1b0W8W1P6P3O2!#4#/!s/&b0W9W0!sF@0W2XR8P3O1%3_%2_'@%_8R_57WA72U4R^P2PUP2p-0P3g00c1RUg00^Cn01!sk%20000XQ2g00cNP4P3EoR4PU1c[3b1W0W2!#:+$100021110500P3P9O2b2bCW0W3XS!tM&\%2\'B=7W_P!sg$T3b1X0^W3!sh<3!sh$H!uW?b4W0WFXP8WTWEWIWOWDo"). Qed.

(* [comment removed for export] *)
Lemma brk_req_val : ltac2:(zQ "h60!jb!hn8!j6!h9!u4!jm0!td!hnd!ho4!jn0!jo3!jof!iua!mm6!mpa!mo4!ml5!hj6!jie!jkc!mr1!r7>1E$h1>2cs$d>1R@2$c@1$0#5@1$1@1$0#k0>4FULL>0@1$1@1$0#k0@1$4@1$1@1$0#8>5model$9>1d$3>0@b$h0?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^6^5^4^3^2>0@3$2@1$4$3@1$f^6@2$6$3^2>0@3$2$7@3$e?1A^7^3$8@3$2@1$1@1$0#k0@2$h2^7@2$5@1$0#5@1$h4Na@2$5@1$0#k0@2$h3@2$h5@1$0#k0@1$b@1$a^5^4").
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "##`Ih02Hah14__x1h24__x2h37__arithh44__ffh57__sat13h68__varmaph75__with81Hh94__p1h:!sN&1h;!s0&2h<!s0&4h=!s0&5h>!s0&6h?!s0&7h@4__x3hA4__x4hB4__x5hC4__x6hD4__x7hE4__x8hF4__x9hG2b1hH2b2hI1nhJ2B1hK2B2hL2B3hM2B4hN2D1hO2D2hP2D3hQ2DmhR1EhS4FULLhT2H0hU2H1hV3H10hW3H11hX3H12hY3H13hZ3H14h[3H15h\3H16h]3H17h^2H2h_2H3h`2H4ha2H5hb2H6hc2H7hd2H8he2H9hf2HChg2Hbhh3Hbrhi2Hrhj4Hr10hk1Rhl1bhm2cshn1dho5modelhp1qhq2q0hr2q1hs1rht2r0hu2r1hv1zp%0p&0p;1p;2p;;p;3p;6p;4p;>p;8p;7p;<g005`j12Tg00g^j1MTg006Ej1i!s/$cj1ITg01=Wk20[Tg002Hk101Tg02Y=m;0VTg04kBk10PTg00Uok20LTg0042j39Tg04n[k30?Tg00=\j1GTg00@Tj20!s/$7k204Tg00XAj26Tg01L:j14Tg02>GR0k10TTg00?Qj2STg01?Sj2gTg00>Wj2CTg0488k10KTg009fj28Tg01K4j1uTg00DXR1j25Tg056lk30=Tg04lIj2<!sD$0j2~Tg00E4k307Tg01VUj2XTg057Pj2tTg00kAk10!sh$81j2>Tg012Bj2QTg00LOj2s!sA$Nj2r!tQ$KR2j2PTg0595j2q!s/$[j2pTg01[Sk10ZTg01\1k20Y!ud$Yk203Tg05:Ak202!s0$jj3mTg01Mkj2lTg05;Sj2_!tx$Xk10XTg01:?j3nTg00F8k10WTg00lbj2!s/$FXk10UTg00G6k10S!s0$Tk10RTg00H?j2NTg008ik10QTg02P6j3fTg01^Yj3!w7$Hbk30OTg01h3k60!sV$m@j2z!vD$2k30JTg00J0k20D!ss$Oj2\!s9$Rk20CTg00K>k30B!s0$]j4vTg00:Pj2[Tg01NWk20ATg013_j6}Tg02bmR3j2yTg02cEk60G!s0$nk40HTg05<?m>0ITg05=Nk80<Tg05>`j7{Tg05?ek80MTg01G;j1dTg01H2j1eTg007Fj2]!w<$Rk30;!vw$Bj3h!uf$;k40:Tg00IEj4!vQ$1dj7b!vm$>k609Tg00nGj8`!ux$ck70\Tg02?bm<06Tf0R4#2#2p=Rg00\8R5/54p=:%2!s=$#2p>08g00X]R6?945p=Af1R7%d4#e'8p=1f4R8f3R9f2R:/<7']'8/[4p=jA9674p==f5R;1<9:,]8'8!s^$,87'[p=B1<74,]:p=x!s=$p>0E1657/P4p=H1]74,8:p=K1654p=31C74996:p=?20364p=7B0;!t2$OAh6749h6:p=;!u0+!s$'p=L!sF$p=kP6P:P7P4H0:p=FP:g001ER<g00_KR=P=g00_kR>P6P7g016gR?P4CUg00a2R@Fbp=JP7P<P=P=P>P4J09p>001z64p=DP9!s@+!t2$G`p=^!sp%0`KRAP4CUp=a!t&&7N!s6%V!sw/P!t2$|P:!s9+7P4K0\p=oP8!s:+!t6/@Fb!t:'@%M4#Mp=E!se-6P7P!tG$!t$%Y!s7$!uJ$p=wf6R?!sP+;P8!u75G`p=c%44#4p>0@!s/$#4#4p=Zg00bRR@P6P3P0P1g038kRAg01aaRBP5P9!si%N<06p>0>P!sP+PA!t9&!sF/Fg00\Vg039Mg00]^RA#2R1#MR0#iR3%21R@#2RC#RS00#2RD#iRE#IRF+0[%iC#I$01\Fg01`4p,4SEGSS01p,1ARGp,5LIMITS02p,4SINVS03p,4argHS04p,3FS0S05!tc,N;0V&016&0P;20L6739g00aRRHB0?G?:g00b2RI39%:9RJ%RD$08RK#GRL,09#A%G1RM%20RN#R#GRO+04RP,69PEf8RQf7RR%4BRS#4RT#4RU#4RV#4RW#4RX#4RY#4RZ#4R[#4R\11E8R]Djg00[0R^'0/=9&0T\,S3R3,g?1C]9,SE59F108L#A16;PPEf;R]f:R_P\PEPREB/0^/=?11EQR`/0L#AS06%:`&0KGRa/6`1C`RR`g055iRb'61g_31SE`59FQ06f9R`,1E#:11E_,6a11E]/C_/6bPFf@S07f?Rb;x\Raf=Rc$0ERd,8ERef<Rf'C,SE99F4XlF%ua18EaRa%GDRD-04MRF,5a'H%ud15eF,Heg05A3Re%I4Rd%I7RaP2%I:?974189:1897'=Rg[18:718:4'=%I9?9:7[Rh%I8?99:\gB0=:74P4n20010!s#$12!s-%0WHWGWIPh^Ha^Gd^IeP4PEfCRefBRd!u9$11EbRhf>Rg'CRi,SERjP6PifDRk1<e\5KE/=4Xv61~MOS08%:MRl%3O%:P[[S09%3MRmg00^CRnB07MO7UW0S0:%3P\n^0mS0;1~MDS0<%3D%:FRP[\lS0=B07MD7VnX0mS0>%3FRD!sV&?11EeRe/XL%3e%3LRefERm,1E/0L#3[[PEfHRnfGRlP\11EkRODjRo/XF%3oPEfJRofIRpP\fFRq,1ERrDj/0F#3\D[1XkLS0@%3k10qLRD#3\e[S0A1tmL%ALRs$05Rt1>qL,QL=?qD[1sqL%:LRD10lLRu15uL'H[1rlL15L5Ru10nLRv,5L16v5'P[1qnL1>pL#A\s1ppL10oL/=o\s1>oLP6fK/0LP6PEfQRofPRvP\PEfMRwEB/tF%AFRx$05PEfRRyPo!sC$NS0BEBRz1>zF,QF10zF3?[1szFPEfSRzPy!sM$OR{EBR|/0FR}15}F'H\P1r|F15F5PEfTR|Pz!|'$vEBRv!sM$,5F16}!u+%vFPEfURvP|!sK$oEBRo/>F#A\x1poFPEfVRoP!t}$PyEBR}/0F/=}\x1>}F!uG$WR}!u$%PzEB/0FP611E|/tL11EvRv1>vL,QL10vL3?\t1svL11EoRo/0LRv15vL'H\D1roL11E}R}/0LRo!vv$o5'P\u1q}LfX,1ER}/>!v}&}LfYS0C!s;%0L/=}\s1>}LP6fZ!yF%P6P2f[R},1ERu#315uFf`Ruf_Ro/<\5KEf\S0D,1E;?}Pwf]S0E,1E#3f^,1E/5FP2fcR2fb!sS%Rw#315wFfdRw1<2\5KE11Eu;?oPyfeRy1<w\5KE#3ff1<y!|I$5FP{P;O1%3`\ep-0R{g00^_R2&0ZA-0Y6RD%7\'ORv%7U,ODRU2036BRt3;%2KRK#2#R#L!s$-G-026=m6tR|%4\Rz#7%7ZRZ%7Y%7VRV3;3;g01b@RY'l'_%4zRz#7R~,OD%7[,OD1ODV%7TRT,OD7;U7;Z7;v!sM&%7X%7WRW'kRX'kA;~WT2026LRW=m6T%7SRS9m6W!sT&1k~X5;|3;/lY'_'_'_&0X2R|5n23n&0W2RX1W6?&0U6R~7F`1W6Q?F8~7F:1W6R?F`~1W6`?F;~7F97F7&0S6RW&0R6RvPv1N6LRZ1N65RU5Jv-00vRD&0Q=RV%D1R1%M0#D9f6Z%DCRC5T65JvC^PVPvP!sd%M>0O6ERM,aUPV%MAR0#M#DR[,VU,|vPv!#>5']J0N5ovD@!sc%AJvMU-00vPV1z6ARA>0J61%DN9f6M=T6[!t7/DPV%D0RD%M@!t\&20#DR0!t^11aAM!s0&VUA!t5&T61DRZ%EK#E!s$02#R$08#L#GRK,N6R@'VPVPvAYvU1R=!s1$JvCU!sv&w[D!s0'0!s:'aUDPVAJvAZD@D@D@Fc!s-'Fc20Dv>R>P4P:1\HIRZ20C4:=9HIdB0B657RICvRHb4b6b7X16X26X@6XA6XB6XC6XD6XE6XF6W9g00c1RD\sRs1QL`=?:?[1H?]\PPD\x1[981QF_;?R[1QL_=??R\s158F%3;1CRQ/6K%:Q%AcRs1=c]%:cA?fcg[\s[!s#+^16^26^@6^A6^B6^C6^D6^E6^F6^9{P4fAR{/5FP]PdPpP_P{PnPw11Eyfifh!}j%Q07PqPlQ0BP:P9Q0CP}Q0DQ0EPoPuOFb3b5W]W\P7P4O2!#<0/!s/&W[WZ!sD=bubrbYbXbWbVbebtbqbdbcbbbab`bsbpb_b^bUbTb8b:b;b5b<b=b>b?!#>V$/=ie18Ej1[ahRa/X^%3a165^PEPmPkP\PEP{EB/0^#3[[Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?1XOL%3O10rL#3\e[Q0@Q0AA;TSt/lY=n2|PX1W6:?F7~PW!z9&A1R1/V@!yG+!zS%=PV1VU1,|vAYv1M5ovC^D@D@P>P!y$01C47!x-$71C98RK15KF'H\J!wx'P4Pq11ElP]PcPdO5b3!ut25iF,Hie-0AiE}O4b8bhbj1gg3Q01PGQ02Q03Q04Q05Q07PbPgPcPfP\P_1yB\RB&0@z#Z!s$%Rz,y\Rc'P%GNRN#:RgQ00#GRb,5NRG'PR3PBPcPgPG1\65P\PN1\6NR5H0>P\PNP5PzPb1\6bJ0FJ0GP|PXP~PW1N6NRN9YvU1N6b9YvN5ovP!|F$PZPICv!v-%P3P4b3H0HN>0IE}WMWLWKWJPfP]P_P`PQPRP?P8L0<F{WQWPWOXNJ!s<&!#HK'L0MF{WgWiWfXn6WoWSWkWmWRo"). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem node_sys_sound_YBrk : ltac2:(zQ "20!mrb!mk9@a$1?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0$0").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "#%iWp'0h02Hnh13H17h21Hh31pi001ph47__arithh57__sat18h6!s0&9h7!s0%20h8!s0&1h9!s0&2h:!s0&3h;!s0&4h<4__x1h=4__x2h>4Hblkh?4__x3h@1mhA4__ffhB8__varmaphC5__withD1bi011bhE2HmhF4HreqhG3H10hH1xi021xhI1zi031zhJ4__x4hK3HokhL2HahM3HexhN3HnfhO2L1hP2L2hQ1oi041ohR3G10hS4POSThT3cs'hU1whV1AhW2B1hX2B2hY2B3hZ2B4h[2D1h\2D2h]2D3h^2Dmh_5Hbaseh`3Hbrha3Hm1hb3Hm2hc4Hminhd2_Hhe4__x5hf1ahg1di051dhh1fhi1lhj2oki062okhk1Ehl2E'hm4FULLhn5FULL'ho3G17hp2HChq2HEhr2HFhs3Hecht2Hhhu2Hkhv4Hpc0hw4Hpc4hx1Rhy2R'hz1Th{2a7h|2csh}1eh~5modeli076!s/$'i082p0i092p1i0:2p2i0;2p3i0<2p4i0=2p5i0>2p6i0?2p7p%0p%1p%2p%3p&0p&1p;1p;2p;;p;4p;3p;6p;@p;<p;5p;9p;8p;7p;Ep;:g005`j19Tg00g^j1ATg006Ek10P!s0$ck10cTg01=Wk21^Tg002HR0k10ATg02Y=m;0]Tg02ZJk21ITg03;7k41CTg03<?k30ETg03=Fk11=Tg009KS00j2HTg02i4k10!sz$42j30Tg037dj4DTg02\^j17Tg00=\j1TTg00?Qj2CTg02]`k20mTg00Uoj2^Tg02^bk10lTg02_bS01k206Tg02`<j6aTg01L:j1[Tg02aHj2>Tg008Oj2f!s/$ik10FTg04kBj16Tg05AQj33Tg00NZj2MTg02bmR1k20RTg00DXR2j2YTg02cEk611Tg00EXk110Tg00F8k10}!s0$Xk1!tD$0G6k11Z!s0$Tk11XTg00H?k20uTg00J0k21!w5$JRk21NTg00K>k31L!s0$]k41K!t<$nk40qTg02dYm@0oTg02>GR3k10nTg02mFm<1JTg040Ek11HTg03G:j15Tg00>Wj21Tg01A7k30kTg01Bbk308Tg04Jkk20!wY$jLk11GTg02kPj5{Tg03M;k41FTg00BDk60?Tg05Bak20iTg00M6k41ETg05D5k61DTg04Knk31BTg013_k604Tg01@Tk2!yt%XAj22Tg05EAm@1@Tg05FUk30GTg04n[k301Tg03RXj1;Tg00<6k20eTg04;Sj!yy$1[Sk10dTg00:Pj2!yx$?Mj!u-$1blk30!{6$@Tj2\!s/$7k21>Tg0488k11aTg05G\m91<Tg03hXS02k30!y?$85j3wTg05Hhk31`Tg05IKj3ZTg01:_k10_Tg03KRk11_Tg05JUk118Tg03lik60VTg04hdm<0ITg05K[k80JTg05M1j2!x[$7Fj2_!{o$fj2BTg04<Zk10!vL$G;j1vTg01H2k10UTg04gXm<0TTg01K4k1!{x$1VUj2b!zH$0k2!zp$0E4k3!xV$1LYk20QTg01MBk30\!s0$kk21!wL$:?j3!vV$lbk20OTg00m@k20<!zP$bk31]Tg01NWk20fTg04=`k10!wt$N@m<0~!tl$gk10gTg01Iak10s!wk$Vj4eTg05OMm<0|Tg05PZk70hTg01hWk30jTg05Qmk50{!u;$2k31YTg05RKm<0zTg05SgmE0yTg05=Nk80pTg05>`k70KTg05?ek80xTg0311k41WTg0326k41VTg033:k31TTg034Mk61STg04Pdm:1RTg05UBk20LTg02?bm<0wTg00IEk40tTg001dk70r!v'$ck71!v\$?Sk21UTg02lQk21OTg01;=k207Tg04lIk20!wq$^;k41M!s0$Yk31!z-$nGk80bTf0R4#9#9p>0Yg00aRR5g00b2R6704p==f2R7f1R8g039MR9/^430p=?f5R:f4R;f3R<%77P8P4Eap=Jg00\8R=/24p=41178/Y4p=r%[4#[p>0Z!s/$#[!s3$>1>78=0<4p=:%57:0G;<1184+0L,^9p=N1^94p=8g00X]R>/^4p>0C%78/14p=s%58:0G<700L4!sV$~P;P<P7g00cNR?P8P4J0?p=O%T4,^>p=V1^>49078p=j!sQ%P?1^9!sN'm!s:&8CD/M4p=k%94#Tp=l%A4#9p=|%A4#Ap=X1Y=4p=Kg00bRR@P>P1P3P2g038kRAg01aaS03P=!ss%P4N<0wp>13P!sQ+PAP:!t;'!sF+220u>4p=h!u8$1ERAg00_KS04Q04g00_kR2P>P8g00`KP4H0tg00a2R3K0rp=RP7PAQ!sR$P2P8P4K1Qp>0`21U!w&'qB0G<7800L4p>0[%v4$0Up=]P;P<21O78P4CDp=<A0>84p>05P:P;1C<!ts$D{p=z%74,C8p>0XP:P;%77,C<!sC'W1184-0L7,^9p>1?&184$0_p=ng00YgR1P>P;P<CeP1P>&0B8P=Ce=d745d:p=cP1P>P!s:+p=@AZ784-07<p=g!sC$7P8Ce=d<4p=og04T<R@@0a!tx$0A0546,H8p=L!sR$<P7Ce=d;8=Z:4p=Qf6RB!sk&!t0$<89Z:;+070074p=y%9!{j$!{l$DA0>4=p>0W!v@%,B8p=F20v78,_<,B;/E4g00[0RC'\p=t!u0&4Cep>1;207B:Ad<78=Z;4+07p>1:Aw@84p=`20784=056p=x!uV$!s2%p!us19Z;<p>19g01<]RD9054p>0:114=/1=p=S1_84,B7p=P11!tx$S&0U4,B8p>0@20v84,_7p>0M1B78/E4p>0N!v_%P4H1Mp=}B1\>84p=U!yL0!ys$17N!ys$P!yn%iPB!sH-!zt%!s6,!sy$L0bL0bp>0!sB9p>0=!xj%!s9%J04p>03g00\V!{J$]^S05#9S06#AS07$0PR3Q06#9RE#9RF$0YRG#9S08$0PRH$0cRI+1^RJ&0PF$0c$0A\IRKg01`4RLg04Udp,4SEGSRMp,1ARNp,5LIMITROp,4SINVRPp,4argHRQp,3FS0RRP;PB!tp%N;0]f7RS-1IM#=&0A9RTPNp,3nx0S09g05VHS0:f8RUH1C;?SQ09f;S0;<0E<f=RV$1=Q!s4%'HPMPNPOPPPQPRP;PV!t1,g04WlS0<&0^7f:RW$0^30PMp,2SCRXp,2fxRYPMP:f?S0=P;P<EJPWCD[[[`07L^nK^yJ^lA%7WRA#4S0>%TERE=rAC&0PG$0cS0?Q!s%$$0ARJQ0;#7RK,CH-0mMQ0?/^4RL30&0l4#=RZ'HWU+06PMPXPYPMPSPAPBP:EaP;CDQ0>ArKEC!sv%%7V!so+=0JLS0@/HZWU!sb'f9S0Af<RLPUPSEJPBCD!s_$@PZ!t,+WPKQ0APUEaPSCDQ0@&0l8#=Q0=Q03#[$0ZS0B#[S0C#[S0D#[$0>RK!s?$$0>RZ'>&0A>RJ1fJ4S0EPJf@S0FPZP4C:P0P>PJfBS0G!s7-TP8!s+$4&0F9RAg03:RR[PTP4PAP!s-%!s+/A!s4@AP5PT!s}$5fLS0H/>KP>P5P4P6!s<&NR\#6fOR]=3N4PDn10110200021010500R^P^n01103000300101!s'&!sh%Q0H#6fMS0I!sh;!s82300Q0HPKQ0HQ0H#7R^PEDNPA!t3$600!sP$0!s4$>00031010?!s'$00PA!sN&=!s@'>!s'$00!s>&<!s>'=!s'$!sX-;!s@'<!s'$!sX+:!s>';!s'$!sX-9!s@':!s'$!s@-8!s@'9!s'$!sr+0!s>'8!s'$00R_!s@&!v[5A!v57G#8S0J50T!zb+AS0KfDS0LQ0FQ0=EJf>S0MCDS0N]0]1P8PJfCS0OPZ&0C4S0PC:!y[&AP!tK<Q0O5?T!z<$FS0QPZQ!s^0!z+f1>]!z$3QS0R#6fRR_!z%<`P`!z%?%6]fPS0S!z#MP]PKP]1s]EC~!yx~!yx~!yx'R`!yz;!xS=Q#8Ra!yc/ES0TfHS0UQ0LQ0OEJQ0GCDRb!y`$7PJQ0TPZ1^>=S0VC:Q0T9?TAPTPAP0P9p-0P4g00c1Rcg00^CRd!w7%4!w7%!s#$X}TRePaP4DOPc1Mb4b2W0W1fGS0W/>ZS0X%V4Rb50J!yL$8PAP!uO<Q0W#8S0Y50TP[PJfJS0ZPZPbC:!sb+!z``_!z`3TS0[#6fUS0\!za]_fSS0]!zaN_PKP_%7_S0!#5_~!zepR`!#5aTQ0Z#8S0_!zN/IS0`P^Q0UQ0WEaQ0QCDS0a!zL%fKS0b/>ZR^%A4Ra#T5jJQ0b#8Rf90!zT&eQ0HP4DmPc!sy'Q0bP\Q0ZQ0`EJQ0UP4Dk!zA%X3[P4O1%94S0c#VRg90J^!y_&!uE>=0TfP[PJP\PZPg!z9+!z1XQ0\!#<o4WS0d#6fXS0e!z3<gPg!#<q@\#6fVS0f!#<qN\PKQ0\Q0\/s!#5t~!z5TRg!#5vV%8\S0g!ys-Q0IQ0SQ0HQ0bEJQ0ZCDS0h!yr%1>]ZS0i%9aRf#VR`!#4=+!tJ>%8]S0j!#4;%P_PZP`!x}2!xwNe!xw5ZS0k#6f[R`!xv]e#6fYS0l!xvOePKQ0eQ0e#7Rg!#40~!xy=R^!#42T%8_S0m!x_0RQ0[Q0SP]EJP\CDS0n!x]%Q0]/>ZS0o%AaRa#9Rh#VRi!#9z-!tN<Q0]#8S0p!xe&Q0fPZPi!#9x9!#9d?`!x^3]S0q#6f^Ri!#HIZ%6`f\S0r!x\MP`PKP`1s`!~P~R^!~RUQ0f#8S0s!x=0\Pg!x?$]EaP_CDS0t!x='d/>ZRg%Aa#l5jJQ0d#8Ra!#8d-e!#8d2dQ0kQ0fQ0\EJQ0[!#8e3Q0c#ARj#|#VRk90Jg!xO&!uB>=0Ta!y&%kPZPk!~jB!xz0i!xz3`S0u#6faS0v!x{<kPk!x{Aif_Rk!xzNiPKPi%7iS0w!~UgRa!~WUQ0k#8S0x!xf0lQ0rQ0eQ0dEJQ0fCDS0y!#7^&`ZS0z%AfRf!wq$^!}{/!tN<%8`S0{!}y&PiPZP^!}x<!#7L/v!#7L4cS0|#6fdR^!wo<aPa!#7L@v#6fbS0}!#7LNvPKQ0vQ0v!#=DMRa!}tU%8iS0~!wV0qQ0uQ0rP`EJQ0kCDS10!wU'k!}=$hRh#A!}A$%8kRl!}?/u!}?1PkQ0}PiQ0qEJQ0r!#B|5jS11!}@+m!}@-!uB>=0Tl!}@%}PZPm!}@4!}20^!x@3fRm#6fgRl!x?[%6^feRg!}0N^PKP^%7^Rn!}/7Ro!}1SQ0}#8S12!w}0vPnQ0uPkEaPiCDS13!#6<&|/>ZS14%9f#A!w,$f!|T/AP!tM:Q0|#8S15!|V'mPZPf!|V-!w+0l!w+3iS16#6fjS17!w-<fPf!w-AlfhR!#FbMPlPKPl1sl!|@L=?Tm!zj+gPfP^Q0|EJQ0}CD!{Z'lZRo%9h#X!{X$A?TAl!{T%Pf!{S2lQ17PmPgEJP^!{Q'Rh!{S/#X#l9jJoP!s<,PJPgPZQ05#AS18#9S19#AS1:#9#X#lRh$0CC:!w1/m!w12%6fQ16!w'<o!xN&!w'5a!v`6mPKPm%7mS1;!zi7=?Tg!#gb/gPl!vR$!}A%hQ0uQ0300RZRa%[Z!#dD$!s%%Ro-0RZRj'H%AF#TRF#KRn%TGRG,YFRp'HRqPaPjPnPp1f>=S1<PZPF1f>FRpH13PZPFPpPoPG1f>GS1=J12J11g00^_S1>$10S1?Q1>$0}S1@&1[>S1A&1Z>S1B&1X>Rp20u>=Rn%hFRF5Rp%hGRj9RpF40`21Pp2S1CP4P71f5621N47#=dB1L>=8H1KS1DbAbBbCPqP4b4H0qP8N@0oPIP^&0nZ,C3Rq1CHhR2Cq%4h1YhC'HS1E'HQ00PIPgPqP2CqQ1E!yD+mQ16PgP^EJQ0|CDP4PIPl!sM/!w++Q17flR2Q16PfPlPgN<1J&0AI&1Hl&0FI30!y6$4fnRqPKPq%7qS1F!x-7fmRh5?TRFP5!sY&pRaPK%5a%7aRr/1EH0[Rs#8!s_4oRt#8S1G!#3y'Q07#9S1H#TRu>0k3?Rv%]2608qfqRw#7Rx,CH00HES1IPh&1GMRyD{P2fkS1JD<Rz]KP8PtPKPt%7tR{PEDN%8qR|50TP9PsPtP4H1FA09stPI11xERs,CH!tK%%]h:08tvS1KP4PqPyD{PhP2D<XDIP9PwPK%5wPsH0[S1L%74frR}/sER~+05XT91f>sPaP4J0?205rsP>Px!t#'q:08avRvPHP4PtPyEzPqPhD<XI>PfPaQ1KPqPhQ09@0Eaa&1=}Rs!s1$Q0900ia20isaH1EP9P}PK%5}P~!vr$!|E0wP4PvPtPqN;0]XT9PaP}Pt!t#$1JJ1DPwP8J0?Q0<&0^h'fO7P~!t}$b2Q1IB1BxmgJ04bKWKA0TA|!#<m%1G!#_o&z4b2WK!x2$1!x2$100P4O1WKXj5!zA&?21A3ud:0k3uS1GQ17#]60821CH{00HEQ1JPyD{Q17Q16D<\F^j51>qKPJQ0EPJ!x&$!#o='Pw!s4&!#4X'P8!#8a1tS1I#6S0<fuS1K!#4_;FPF!#8d@}S1MfsS1N!#8hL%8s!#4y5w!v#&aPHQ1N#7Rs!x_/]0]G!u:$JQ1NPK!#jQ$5PT!uR&!uL&Q1K#6S1OfvS1P!uJ<qPq!uJ9Q1IPKQ1IQ1I!#Co7Q1N5?!}$&P}PHQ1K#7RFPw!tv$aPt!tv&4PJP}PKQ0VC:!t}%1NPsPEDN=?T}!z:0}Q1IPwPa!x-$=Ph!#7W$KRs20RKoR{'H%KuR?1YuGRz'HR|PsP{P?PzQ1<PKPu1f>uRzH13PKPuPzPoPGQ!#75&Q1?Q1@Q1AQ1B%huRu9RpnARpuj60`pQ1CQ!#6G'|!#6G2w&0nK,C3S1=1CH=R3Cq12==1Y=C'HR|!#6H&}Q1=P3CqP|!v4%Q1NPHQ1P#7S1<P}!v6$wPaD<P4PI!vx$!sU%YPMPXQ1PfyS0V-0XHQ1KPyQ1IP2Q1NQ1JQ17PLQ0MP8Q0;P6P:O2N@1@Xd|WRP8P4O2n20!|\$0001!wd$000bfW0WGQ1I/>KS1Q=0Jb!y;$qQ1KPKQ1KP!#7/7Q1I#8S1R50TQ1P#6S1S!|e$fwS1T#6=0J4P0P>Q0V!s3&!|e-f{RF!z$;fzS1UPKQ1UQ1U!yh90V#8S1V!#7o'fxS1WPH%7FRqQ1TPyEzQ1PQ1KD<S1X]0]FP8Q1U#6Q0P50JP5PTA3NF8PFPKPFPqPEDNS1Y!uX5U#8S1Z50Tf|S1[=3N7P51f54S1\f}S1]=3N<=054P5p+01@Rq=3N:!s7%PTP8p+01AS1^PKQ1^Q1^#7Rb!vi7%8qS1!#h5+f~R|PHp+01BS1`Q1]PyEWQ1[PFD<S1a]0]>P8A3N|;S1b#=%5qS1c:0GqK%7qS1d<1?E%8|S1e50TQ0GP6P4O2!z&']Q1G%]F4081CHb!#5|$[PyD{PFQ1UD<Q1`>01NSRb%n4S1fp+01CR2#;S1g20e1>R1%I4R3Q05$0dRuP1P4&101RjEcS1h%52S1i=@1jCgS1jQ1gP1Q1iQ05#TRG,EUS1kPjCoA@13jS1lCgX@@Q1`#GS1m+00R3<097%=b/L3Q00B01N2U#=Q!tW%DS1n#;R3Q1hP1Q1n#5RbPjP3P1PbQ0A/EGS1oPjQ1lEQFyX@@%G2+00#=!ut'^PHQ1nPqPyEWP|Q1]D<P4p+01ES1p>01NW!t:+GS1q#;Rb!t:&q#5R3PjPbP1P31ELGS1r!t8/p+01FS1s#G!t?$%KLS1tQ08$0Y$0DS1u#TR3,\L$0WS1vQ06#TRbQ1H#9#lRo+1>S1w,2LS1xPHQ1pQ1qPKQ1`,FHS1yDt005L!u;'nPHQ1qP2!y-%`Q1^D<S1zQ1t1\V3!t/${Q0MQ1w'2S1!yb&HS1}p+01JS1~PKQ1p,FHS20DtQ0=+05Q1s!s7$1/\!sh$22Q21#K&1aNS23Q21'2Q21Q0F'1g055iS24'!yj+}!t1%KS25Q1!vz$Q1sQ1pD<Q22Q1q,FH#KQ23Q1},FH'2p+01IS26,FHQ0O'1Q24!s;%MS27p+01OS2!|L$LS29Q25Q1~Q0LQ1}Q0OQ0AN91<PIQ29Q1=Q1~!sl$L'1,CHCqQ02p4p710RzP5\4R?&0}8R{!ya$a784#=Aw;47P<P4O1'LXH<-06<[RsAw<48P7!s='7-067B0a<78#=Rx[Aw:4<P;!sE';-06;\xB1`784P8!#6V6WiWhWVS02Ps^i{^h?^VzS2:P4P@!yx&RS2;#;S2<Q1hQ2;#5S2==@1jS2>3ZQ2<P1Q2=Q0W/EGS2?+1;!z-$K1:Rz!z/&QS2@#GS2APWO4Q2;#GS2B,`4/LzXH@-06@Q01P!sQ$SS2C#G,`4Q1fQ2C#;Rz!{@%2C#5R?PjPzP1P?Q0U!t=$D!{B+'LXH@!xX%p+01PPHQ2CQ28PyEWp+01NS2EQ27D<S2F!|Z%US2G!t9,G#;S2H!uY$G#5S2I!uY%J3ZQ2HP1Q2IQ0Z!tB$K!uY-'LQ00p+01VR?#G,`8%n8S2L%;?S2MP1%I8RzPuP1P8PjEcS2N%5?S2O!t&%PCgQ2MP1Q2OQ0b!t&$QPjA@1zjS2REQ'x!uF,TS2S!z}%WS2TQ2C!z}$2;Q2@!~z'XS2U#G,`<%n;S2Vp+01YS2W#;S2XP1%I;!tY&;!tY%YQ2W#5R{!tZ%ZCgQ2XP1P{1E\GS2[!tW+\EQ'x%n:S2]p+01ZS2^#;S2_P1%I:!sy&:!sy%`Q2^#5S2a!#6W$R{Q2_P1Q2a1E]GS2b!sz+cEQRz<094%={/LzQ00%nBS2dp+01[S2e#;S2fP1%IB!t/&B!t/%gQ2e!u&,h3Z'xQ2fP1P{Q0S!v_$i!#7\%zjS2j3p!~Y&2W!vZ%\S2kQ2U!vZ%TP?D<P4%nUS2lp+01]S2m#;P1%IU!tC$U!tC%nP1Q2m#5PjI19'xp+01^S2o#;P1Q2o#5Q0]!tI$pPjCoQ0A#!yQ&q3p%nWS2rp+01_S2s#;S2tP1%IW!t,$W!t,%uQ2s#5!sY%v3ZR?<098Q2r#=S2w/L?Q00Q0;#n#=S2!tK$`R?!tJ$0;#IPu!s/$!sp%y%5?=@1!um-o!um%aRzQ2m!ul%kQ2e!um%V#=S2zp+01cRV#;S2{P1Q0M!s{'M!s{%|%5VS2}!s~%Q00&0_4#=&0:8[R{&0:4&0_8#=Rs[&0:7\s&1_!#3p9XD5S2~P{^D5S30P4Q0F$18R{P7O2S31&0:{S32PMp+01dR{PNPQP{p+01fRsP!tv$bRxJ0V%;sP1Q0K!tw'K!tw$33%5s=@1jR!#Y/0{PsPVPxPzQ2sN<0IP7L0J1u{gQ33,u{'!t?&eRg!t?$gp+01gR~PxPV!t:$~P1%5~Q0r/EGS34PjCoRvQ0G!xT&35!#ZE1~P{!t>$?!t;$UL0JQ35,ug1ugv'2PIp+01hRv#5,_s1BH4S36#SS37Q0L#IS389PH~S39/1uQ0L$0BS3:9PH~#S'1'2XDIP8%vVS3;$0URr!tJ0sPvPg!tL$zN<0TJ041BHrS3<#SQ0O#IS3=9PHs!t$$O!t$$>9PHs!t$%!tg%iRr#5,_~Q0T#IS3?9PHv#SQ361EkG'1$0SS36!tU']{Rk!tO0~PrPs!tQ$x!tO&Q39#S1BHkS391EiGS3@!sl$'2%]gRi$171BHiS3A#4Q3AQ08#TRi-1>bRk'Y'H!#Jj$Pvp+01kS08-0XHP~PyPsQ2o%vsS3B-0@HS3CQ0u'1S3D,CHS3EPgQ2mQ2kPhPtQ0bQ3D%K4S3FXI>S3GQ08>0MrKQ3C60NHRt/bCS3H%4t12=CS3IPHQ08p+01mS3JPK1FHvS3KDt#4[[S3L216boS3M%KbR=%4oQ1w#K[[S3N%4bS3OB15bo8VdWLRoQ3OQ1w#4\d]LRt216biRh%4i%Kk[\=R=Q!sU%i!sU%iQ3O%4k!sS$dQ08#vS3O!uX$1w/b3S3P!ss$%43S3QQ3J,FH/\3!te%R1bm3S3S%4mQ3Q1\f!s>&TQ1>Q0C-0Q>Q0B!s,%3-0Q>60\>S0360\>g01b@S0B+14Q1?3dS0C!#Pl$20O>;7}7S3U20O><S3VQ1A7};7}8S3WQ1BPpQ05-0<>S059RpnS3XQ04$0FRmPpQ06!sA%6!sA$04P!s;$7!s;$3Y%hES3Z'UQ19!s8%[5RpS3\!sL$3Y9ipnS3YPmQ05Q06'US3]9RpnK0;K0;!#RB-X<>X=>X?>XJ>S3^Q3F%K7S3_Ar;E:%4:11;:#K[[[[^<>^=>^?>^J>S3FP4PCp+023#7S3`Pfp+01nS3a,FHS3bQ0fP`P~PvO8b4b5b6b7b8b9b:b;Q3E,BHS3EQ3DQ3HQ3LQ3MQ3NPoPtPhP=PiPdQ3PQ3RQ3SQ3TQ!vp%!vQ'3]Q1u#9#X!s$1!#HS$!s%%#lS1u#h5ipS3W!v0%X!v]%!vd%!vE+PmQ3]9ipnQ3]%hb>1]>HS3Y5Rp60`pH0=!vNC\1148Q1u'2S1u%K8S3X%K<Ar:EB%4B11:BS0C#4Q0C/Yk'H[!vf40CP4PCQ3`PfQ3bQ0[!vW,9!vW5D#4Q3D!sq$e+0fS3`I03Q3D%v~S3c$02,BH/24XI>!#3c/rQ08PvP~PsP{N<0~Q3B!sR%Q3C!#Hd$jS3Cp+01lS3d<0MKQ3c!~|%c60NHS3e/bCQ3e#4Q!~A$3dQ3a!~<$rS3a!~<%!x37d!x{$d/b3Q3d#4Q3QQ3b!},&1bl3S3d%4lQ3QQ16!}D+e!}+$D!|}&60\>Q!|m,!xx$U!|m&:7}<7}8!|Y'Q065ip!xW/18-0<>Rl9Rpn!xa%[Q!|D%8#AS!sD%5R!sY%3[9ipn!|@'/UlS3[5i!xsEXe>S3Z1248Q3_%K;ArBES%4S11BS,2:!xa4^e>S3_!|L'4#7Q16p+01oS3U#vRB-0@H&02B,BHPUQ0dQ0rPvPrO:!x}3b2Q3EQ!xq'Q3c!xh%!|aH1?Q1@20O>7S1>Q1A7}8S1A!vg&4!u{%3]!uu%!uo5S04Q3X1187RB,28!uU&S3XP4!{,$P`O3!~T6!tz%PsQ0uQ0Q#IS3`,_rS3EQ0Q$0BS0B,_rS03P]P_Q0]P\!uAMQ!u3'3W!~2$%h3'UQ!~$$!u893YQ1uArB3k!u4'1u!u4&Q0[!u57Dg01_<S3];rke20eIIRB!|W$gS3D!s/$sS3BPIPIQ3EQ03CeS03Q!wb$5wB!s/$B5wB!}C$#GQ3BQ0Q!}\?|Q0GP:K0h40jI0{!v&O>Q3V!x@$>!|%'/Un/UnS3VQ06%hu'U1Uln/Un'U!|@$!x]$!#98$[!vN8X?>S05%S4S08118u%S7'1'2117<,Y8S3B!{I,S03P4p+021S3D&0B\S3E5PHQ3D%I\S3W5PH!vO$bPWO4!w,5!u\O!x`%!uJ%G:1Y>l'U/Un!uI%!u@>1DQ081E7G,18$0S'2Q!u7/Rm!xw'3DQ0A!ts5N<0zQ0lNE0yb`bPbO!s&$Nb2WaWN!#e\5!s/&bEWbWE!sF@EWc!sF=W2X@@!sE7!#e4$bMb2bRWZWYWXWWQ26Q25Q1}Q1qQ1sQ0FQ1nP:L0pK0KW^W]W\W[!#\s$Q1nP2Q1`PLPqQ0;L0xK0KWMW_!ty>>bSW0W>Q1b$0:Q1e!$0,,1_!#r>$Q1a/M!$S1$>!#rB2P7O2b>bDW0WFXg>P4O1Q1W#6&0F>Rp50JQ1W!$TU'eQ1V!sy'X!sy'F!$TU-!#ns$!s}&FbQW0RnWG!$;L&1Q&0d4$0CRl50JP!s@,!#oT,111100!s'$XI!t^$PJPaPKPp!#s4-%6wA3N}!#iK7Q1L!#z04=?TaQ1MPJQ0EQ1N!#jR,1O!#jP2Q1T!#jO:Q1PPKQ1PQ1<!#kn8K#8RD!#{<+1IPHQ1T#7R0Q1NPyEzP}PwD<Rw!#jH&S!#jF+!tF%8Q1TPKQ1TP0!t19P5?TQ1W!#j@$Q1\Q0V!#j:+A3NF!#j4,Q1[PKQ1[Q1[#7R5!#j/8FR0!u$-UPHQ1]Q0V!#b9$WQ1TD<R}!#j$$Q1U=3N;R;#=Q1YQ1Z50TQ0M!#il/0VQ1GQ1T#]!#in$5!#in$W!#xl$TQ1PD<Q1]!#io$SQ1f%;|REQ1hP1%5|R5PjPEP1P5Q1k!#fr-Q1]#G+00R5!#i'$S/L5!#i'%|!#i'$%;qR5!#gh%cPjP5!s/$Q!#hs2|!#hs/[PHQ1dPF!#o/$UQ0VD<P4Q1^!#ho'!#jv+1rPjCoQ!#jg'm!sp$Q1tQ1vQ!#gr$^P2PKQ1],FH!#gn-PqPHP2P|!vr%]Q1[D<!s^${Q1|PHQ1nQ1sPKQ1^!s_$!#gM&y!#gG$R5Q1y!#fS%y'2Q1yQ0F!#fH%Q1z1FH2!sD&n,FH'2Q20!#fi+!#4-3LQ1n!#fZ/1}Q1=Q21!#fW/Q!#dl'Q2E#;RS!vw%2E#5REPjPSP1PEQ2?!vz+REX@@Q27#G!#dN$E#G,`4/LE!#dK-Q28!#c3+8#;!xf&Q28#5RS!xh&SQ!#d@8Q29PHQ28Q25!vf%~Q26!wt$2A!sz'@!ty-@!ty1K!sz-Q00Q2B,`8Q2LQ2<Q2NQ2>Cg!#g-'2QPjQ!#cD$Q2FP4Q2S#G,`<Q2VQ2HQ2YQ2JCg!#e&'2[PjQ!#bB$Q2]Q2MQ2`Q2PCgR<!#dJ'2bPjQ2cEQRE!#aj$</LE!tV$dQ2T!v%$2gP1Q2T#5R<!#`5%P1P<Q!#aE$Q2j5pE!v$'GPHQ2UQ2S!v$$2CQ2;!v$%lQ2XQ2nQ2Z!#b6$!#cA$Q!#`f%2q3pQ2rQ2fQ2uQ2h3Z!t\$8Q2w!t\'xQ2k#;Q2yQ2k!#``$!#_p+^PHQ2mQ2W!tD%UQ2T!tD%zQ2tQ2|Q2v3pQ2~Q30Q31Q32PMP?PNPQP?Px!s`$oJ0V%;xQ33%5x=@1jR!$4&/!sN%sQ2o!sT$e!#^&,?EQ33,u?'2PMPz!s{$zPV!sP$sJ0VQ2{P1Q2}Q!#]t%jQ!#]k1zPVP?!t&'k!#]n0z1uzj'2PI%5{,_xQ37Q389PHVRj/1uQ3:9PHV!#]S,Q2s#]R1!t-0xP{Pz!t0&m!#]Q+1#SQ3=9PHx!sp$>9PHx!#]C&%5g,_VQ3?9PH{#SQ!#]+,?Ru!t+0VPgPx!t-%o!t'&%Sj1BHuQ!#\|,zRu!#\|$uRu#41Yuk!#\m'{20XH~PVPyPxQ2^%vxRy-0@HRuQ0u'1Rj,CHR1PzQ2!xG$16Q1JQ0bPjQ3GB0Mg~K>0NHuRz/bCRE%4zQ3IPHP~PrPKQ39!#Q0$Rr!#D_6c/b3RzQ3c!#Q-%a!#Po%R<!#Du%3^Q!#Wl$Q3U#7RSPfQ3C,FHR6!#T2$VP{!#Wc41BH1R1PEP!tB6PzP!t&+\Q!#U0$PSPfP6!#U-'VP{!#U-4%4j1Yjk'He-0fjRSI03PjQ3;!#T~;!#dX0~&02y!sO$uB0MsvKQ3<60NHRs/bC%4s!vQ%vQ3CPKQ3A!#T\<K/b3Q3K!vN$1\6!vL$Q3dQ3eQ3ZQ!#Qj+0#7!wp$wQ3O!tr%!#Q_'{Pg!#Q_6P1P!uL'<!uF&!v`C04Q!#P^$P6!#P]6!sx'xQ0uQ3`,_gRSQ0B,_gR1!#PN'!wmEYQ!#O]$!wi$!#O\6]=rjkePB&0gyRj&0syRyPIPIPSP1CeR1AwB1jAwB1yPg%G~Py!#O<2!wr1!#O;1!u|E5Q03P4Q3JQ!#M\%JQ3W5PHRHP6!#MW6!sxD1DPm!vu&H!#LL~!#LL}XW5!#L$0Q0FPq!#LK4^P2PqP|Q1]PLPF!#LIQ&0:;Q1Z!#LG+P0!$?^&}!#LDM0<=0JpQ1R!so-D!so'w!#L:GWG!sF41P4Q0AO2bGbQ!$R{'1JQ1F!$@W$EaPfCDebSbtWdWo!ud>fW0W1!$u30!$=K$01!s\%!$b--14Q0c#9Rf#ARw!$Nz$5jJQ15!uS-^!$c+2|Q1;Q0}Q0vEa!$Y2$!$Xm0PJQ0vPZQ1H!$Th$C:Q0v!#Oc-2!#Oc&3!#Oc&!u#/1!u#+0!u#4PJQ0qPZQ1:!t#'q!t#-0~!t#'0!t#70!#Ow&!t#6Q0z%Aw!ut%0{!$[b-r!uu1P`Q0wQ0kQ0lEa!$fA$!ut5lPZQ07!tq'l!tq/x!tq&0y!urW\PZQ18#9!t#%\!t#/s!t#'t!urUoQ11!$zY%p!ur/[!xi3]Q0fP_Q0REJQ0S!ur8RPZQ1!to&R!to/m!to'n!upSQ0i%Tf!tm$j!tm/S!wa2]Q0^P\Q0IEa!$|a$!tl5IPZ&0CbC:Q0I!tk/g!tk'h!w]W`!s|$GC:Q0`!s|/!#Y/&0a!wZUX=0JlQ0Y!ug/U!wV3WQ0ZQ0QQ0TEJQ0L!ui4!$I5/!u<+!t<-{>!u:'KPZPpC:Q0K!u8/J!u8'N!u8,!#526UO2b1bQWqWrH1WWUH1VWwWvB1TMW7J1SWuW0WsWpWzW~WmWxWkXT9X|9!#E+%NQ09!$V6'0:N:1Reo"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vis_add_shape : ltac2:(zQ "hb0!ob!j6!hn1!j0!mm6!ij5!h9!ms2!msc!mt5!mtc!mmc!mu4!mud!td!hnd!loc!mv9!u4!ik4!mi3!ho4!mvf!ng6!ngf!nh4!hta>2cs$4>1b$0>1n$0>1k@1$2$ha>3cs2$4>0@3$1@1$h2$4@6$h9?1A?5LIMIT^5^4^3^2@2$e$4^1@2$3@3$1$f@4$h7@1$h8^6@3$h1$0$6@1$d^5@3$h4$0$6@1$d^5^4$h5@2$3@3$1$6@1$b^2@1$b^6@2$3@3$1@1$2$0@1$c@1$9^2@1$c@1$9^6@2$3@3$1@1$2@2$5$0$0@1$a^2@3$h0@2$5$0$0@4$h3$0$0^5^4@1$a^6@2$3@3$1@1$2$h6@1$8^2@1$8^6@3$1@1$2@2$5$0$0@1$7^2@1$7^6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundB"] "#$26p'0h01pi001ph12Hch22Hvh32_Hh41Hh54Hnhih63Hshh76Hsplith81ei011eh93cs2h:1oi021oh;5Hflath<1bi031bh=2b0h>2bbi042bbh?2bki052bkh@2cshA1khB1nhC3nhii063nhihD2sbi072sbhE2ski082skhF2sni09!s+$:1ai0;2pbi0<2pki0=1xi0>1zp&0p;1p;6p;2p;3p;4p;7p;5p;<g00F8j1mTg002HR0j1zTg05WOj6sTg05XVk606Tg05Yak603Tg00BDj6lTg05Zkj1jTg00<6R1j2pTg008Oj2YTg0042j34Tg03RXj11Tg05\7j4^Tg050lj2XTg00g^k105Tg00=\k104Tg05]@j40Tg03=Fj17Tg03W=j2!tG$0hj3wTg01fUj3uTg05^Fj72Tg03Cfj1<Tg05_Wj3>Tg01;=j25Tg03Dkj16Tg03B_j1BTg03F2j1ATg05`3j1LTg02\^j1:Tg03?Mj19Tg05a;j5NTg03@Sj1TTg03AZj1WTg00>Wj2@Tg03G:j1VTg03H?j1OTg03L3j1PTg03ICj1UTg04S7l<J!v7$ij1y!vK$Vj4iTg00Uoj2oTg00?4k601Tg01blj3cTg009KR2j2QTg00M6j4gTg00NZj2rTg00iXj2fTg011Ej2_Tg03>Ij1}Tg03PEj1|Tg05bGj5{Tg01JWj3xTg04R2k402Tg01:?j3qTf2R3f1R4g039MR5f0R6'o34p=Mf7R7f6R8f5R9'f'_f4R:f3R;/f3'_'5/54/56p=H153!s0%=1@;3/@4/_6p=F1389,57/5:A>;34'5!sJ$K%}6#|p=8g015\R<P9P:P;P3P4D{;x6p=RP:P;Ax<34P6H02p=Sg00YgR=P=P3P4Ci=q;6p=I1o56p=Gg00X]R>=w=6p=aAu=>6p=`%1!sy$P6C0p=eP!sb+%<65q;p=]A49:;A4346'Qp=EA489:A4;34/Q!s8$Dg00aRR?g00b2R@74;A4>!sD+CP=P>!t,$ip=\1f46,_3p=;1f;3,_:!v8'h1_46,53p=v%<69>34p=ZA4?6@p=?A4?4@/Q6p=d15;3!sZ%=4?@p=[1f34,_;!sk$b15:;/5!sG&p=tP8!vR,P6F2,57p>00154!se&k!sB'C0!s7%nA4>46p=~%m<%z5R<p,1AR@p,5LIMITRA!su'Es;M6P<P@PA!t2'EsAM<63X:<P6!s>/J06RB!s713ElAM<B4%j91p=>RB1YB6%j8=4B6P1P=P>f8RC#j!s6,P<P4P1PBP=P<P@f<RD#1f;REf:RFC^!sJ-0P>P<f@RG#1f>RH'XP?P<g00]^$05$04RIfARJ#1RKPGPIPKf?RLPK!vH$LC0%7JRM/3GGHPMPL1p==RN!t'&?Aw==6#jROfDRP#1RQP4P6Au==3RRC0RSPQf9RTPCfBRUP4P6PRF2PQ!uk$8!s6'RQ3=n200110=00012010;10<X0N%<JRV3>P!t>+PO15SQ!sT;6JRQ%BJRS%AJRW%L6RXPACFGK%:J%8JP@PK%9JRYPGPLDNP@PKPGPLPVPHERPMDSPY%TJ%WJPSPN!s@%CIPQ1@WX%VJ%OJ%PJ%UJM<J#G%y5RWn010!s#$20000PWn1!te'21110600!tx&0!tx$1107108!u401100109!s:34105=M<8PE%a3%`3PTCe%:7%:E%m=RQ%87%8E%mNRV%<7PNPFPTPEC]g04T<#mRS%97%9EPV%67%6EEEFDCC]2]7P4%jE1\4654B!yQ-=RY#1PDPE!yM51XKLP?P<PI%1URMPJPIPMPGPMP7P8PGC0%7URZ/3JGHPZPG!wo,fER[#1R\!xU%C0R]P\PFPTfCR^!xy+\!xy2_!xy>UR`5>N!xz1]_!xz<UR_%BUR]%AURaP!xw+U%8UP@PM%9URbPJPG!xw$MPJPGP`PLERPZDSPb%TU%WUP]PN!s@%CIP_1@aX%VU%OU%PU%UU!xw$P!xtn=M<TP@%1HPYPDC^1pB=Ra1Ya6P@%1LPHPYC^=4a6!x$&!z~&!s:0!~q%!~W1FRK#1/XP!x5%fGR_#1R`PKPIP`P[P`PDPEP[C0%7_R]/3KGHP]P[!x8-JRb#1RZ!x8+MPZPLPHfHRc!x8+Z!x82d!x8>_Re!x84Md!x8<_Rd%B_RM%A_Rf!x8,_Rg%8_RhP@P`%9_RiPKP[!x<$`PKP[PePPERP]DSPi%T_%W_PMPN!s@%CIRePd1@fX%V_%O_%P_%U_!x>wHP^1\C7Rf#a%`fPJCe%:L%:^RfPQ%8L%8^RMPV%<LPNPUPJ%<^R]CIPS%9L%9^RjPV%6L%6^Rk!}{+6!xQ+@P\PPP^C^!xi$4P6Ci54a!xn+3!xn%%1cR\/XK!xm&IRl#1RmPcPIPmP_PmPHPYP_C0%7lRn/3cGHPnP_!xm-LRo#1Rp!xm+qPp!{{$b!xk+p!xk$7!xk+r!xk>lRs!xk4qr!xk<lRr%BlRq%AlRt!xk,l%8lP@Pm%9lRuPcP_!xg$mPcP_PsPKERPnDSPu%Tl%WlPqPN!s@%CIPr1@tX%Vl%Ol%Pl%Ul!xe`=M<UP`1\DER`#a%``P[C0PfPgPQPMPhPVP]PePSPjPiPVPkPd!x5,^8=P6!x2$_PK!x2%1\3!x4+!#6|%m_!w~%PZPl!s+$c!}3%PcC0%7bRm/3lGH!up$!wx,MRa!#6y/dP\PUPJfKRk!#6y,7P8P9!wz+i!wz>bRj!wz4di!wz<bRi%BbRd%AbRe!wz,b%8bP@PZ%9bR]PlPc!wz$ZPlPcPjP_ERPmDSP]%Tb%WbPdPN!s@%CIPi1@eX%Vb%Ob%Pb%Ub!wzL=M<[1XZc%z>RZ1YZ6%1k/Xl=4Z6P0P>1X\k!s2'P<P4!|2&OR\#1RefNRiA;IeaPePPP^PaC0Dh%7\RjPi13ja!v//fRRd#1R]!w:+mP]P_PKfPRh!w:+]PDPEPF!w:+F!w:>\RM!w5/mF!w5<\RF5>NGKRm%B\Rg%A\Rf'@R`/@X;vA%:\Rt%8\RrP@Pe%9\RsPiPa!wB$ePiPaPMPoERPjDSRjPs%T\Rq%W\RuPgPN!sF%CIRMPF!#6,$\RX%O\Rn%P\Rv%U\Rw!wRL%GbRx54<Pe1\P^Re#a%`ePaC0%:kPtPQ%8kPrPV%<kPMPS%9kPsPV%6kPF!|C%Rr]2]5P4%1i/Xo1o>654ZP?P<%L4Rt,@`=vmAPjPsPqPuPgP!u&%tPXPnPvP!tv9=M<kPI%1hRwP\PIPwPiPwP[PPPiC0%7hRw/3\GH!s>$!xZ,SRw#1Rv!xZ+nPvPcP_fQRX!xZ+vPY!x\$!xZ'E!xZ<=ZNh!|j1nE!x[<h%Bh%Ah%L3!|e%P?1Y?6PI%1XREPhPIPEP\PEPKP[P\C0%7XRE/3hGH!s>$!u9,TRE#1Rn!u9+tPn!|}$d!u7+nPH!u9$!u7'f!zk>X!zA$!u;1tf!u;<XRf%BX%AX%L;!u=%=4?6P?PIPvPd!s+$X!vq%PXC0%7wRt/3dGHPtPX!u:-VRM#1Rg!u:+uPgPkPb!w;,PgPGPLPH!u:+G!u:>wRq!u:4uG!u:<wRG%BwRu%AwRs%L9R9!u@0<P4%:E%8EP@Pn%9ERjPwPd!}+$nPwPd%<ERnPXER%7EDSPj%TE%WE%BEPNPwPdPnCI%6E%AE%L8'@%VE%OE%PE%UEM<JR8#GRn!{23%GhRj54<fURm#1R`1\bl!|t'wC0%:X%:mRePQ%8X%8mRyPVPFPNPEPw%<mRFCIRzPS%9X%9mR{PVPf%6mRf!}3&|]2]1P4PIP]PX!s+$h!#58$PhC0%7dR]/3XGH!s>$!v`+P`!#Iu,`PbPlPw!wc+`!wa$Y!wc+Y!|0?d!w_1]Y!w_<d%Bd%Ad%L:!wW%R:#?%:w%8wP@Pv%9wRYPdPX!wQ$vPdPXPqPhERPt!#Og$w%WwPuPN!s@%CIPG1@s9%Vw%Ow%Pw%U!#3O$%G\R954<P<P5P0P5P5P6P6PePyP@P`P{PEPw!#Ec%EPwPFPdER%7mDSP{%Tm%Wm%BmPzPf%Am%L7'@%Vm%Om%Pm%UmM<JR7!#6>$200021010:00X8<PnPjP6J01A458hA457XP5%:MR7%8MR8P@Pg%9MRnPmPE!tL$gPmPE%<MR@PwER%7MRfDSPn%TM%WM%BMRzPNPmPEP@CIR{%6MRF%AMR`%LCRC'@%VM%OM%PM%UMM<JRyfWRe#1Rs1\okRG#a%`GPmC0%:6%:!yp$6%8ePV%<6PNPMPm%<eRG!#FO$6%9ePV%66%6eRq!yl%X95PIPgPmA;IgE!}u'C0DhPfPm13fE!xe/fYRf#1Ru!yj+YPuPiPaPe!yj+uP^PUPJ!yj+J!yj<P@!yf/YJ!z9;>NFGKRJPzP`PCPACFRC;c;%?C,dJP2PIPsPM!s+$mPsPoPk!v,$7eRs/3MGH13sm!u7-ZRs#1RJ!u7+CPJP\PifXR;!u9+JPP!u;$!u9'U!{}=>NG!u;/CU!sO=qC[%Be%Ae%LTPACF#?P;PaPoPMCe%:;RTPTPQ%8!s/%VPNPePMP;C]!s6$S%9!s?&%6!s/$!x+%P6PIPuP;!s+$e!wR'C0%7fRu/3;GH13ue!uu-\Ru#1RT!#Jh,TPXPhPs!us+TPKP[PP!us+P!~r?f!us/qP!~p<f5>NC[%Bs%As%LD!uu&If[RA#1RDPsA;IDfCbPDPhP\PfC0%7ARD/3s13D!t3-f^RD#1RP!u6-PPwPdPu!u6+PPcP_PK!u6+K!u6?ADtR[!u:0K!u:<A5>NRK;c4%?K,d[!z8$TPAA;ITs!vd'!#Eu$uRT/3A13Ts!u0-_RT#1R[!u0+KP[PEPwf]Rq!u2+[Pl!u4$!#Z'D=ZNuC!u00K!#Z#<u5>N#?PqPdPXPACe%:qR_P_PQ%8!s/%VPNPuPAPqC]!s6$S%9!s?&%6!s/$!z+-PPqA;IPu!w?'!ui%DRw/3q13wu!ui-aRw!ws/PPPMPmPT!wq-kPbPl!s6'!uc?D!uc/fbR_#1RK!t#+K!~U$!#Rl%L!#P6'!v$5T!v$$f`Rc#1R[=;ITA;I[DP[PmPEPDC0%7cR[/3T13[D!y21fcRU#1RC!tC+CP;Pe!#<;,C!~'$k!uDGcRG!y^$G!y^'PPcA;IPTCb!vC'!#BS$m/3c13mT!ut0dRm!vu2fP;!yL,PP!~d$o!tWGw#?PKPePMPcC0%:_RMPMPQ%8!s/%VPNPwPcP_C]!s6$S%9!s?&%6!s/$!y,-CP_A;ICwCb!v7'!#bw$e/3_13ew!u80gRO#1R1!u8+1PuPAfeR!#9<+1!|^$\!u:Gm#?PI%1eRRPmPIPRPUPRPsPfPU!#8U$f/3mGHRR13fURf!w>$f,dRP2ffRR#1Rf=;IeA;IfmPfPAPs!#95$RRs/3eC[13sm#?!tp%PeC0%:ORAPAPQ%8!s/%VPNPRPePOC]!s6$S%9!s?&%6!s/$!vC'fhRA#1R1=;IOA;I1RP1PqPuPRC0%7A/3OC[fiRu#7/3O#?PIfjRq!vD$uA;I1AP1PTPDPAC0DhRD%7q/3uR1!uE$1,dDP2PIfkRD!sX$qA;I1uCbP1PcPTPuC0'k%7D/3q#?flRT!xD$qCe%:TRcPcPQ%8!s/%VPNPDPqPTC]RqPqPS%9T!s/$V%6!s/$!x`,fm!tm$cPTA;IcDCbPcP_PwPDC0'kfnRD#7!t>$PIfo!~f$_PDA;I_qCbRcP_PmPUPqC0Rq!u9$q,dcP2fpR2#1Rc=;Iw!s|$'kPcPePmPDCnfqRD!w0$wCe%:DRePePQ%8!s/%VPNP2!tL$]RwPwPS%9D!s/$V%6!s/$!wL+r!t[$e=;IDA;Ie2'kfsRe#1PAPO!t5$tRD#!x]%wCn%:DRA/~ARu%8DRO=4QOR2PN!~W$!t:$=4VwRe%9DRN=4SNRI%6DRD=4VDRR'QRm'QRc'QRq'QP6PuPq1Y>AP2Pc1YQOPePm1YVwPIPR1YSN1YVDCg!s$'W;W!|0$O2!{b$0!#^5&!s/%b1W3!sF~!sFfPg1\kbRk#a%`kPEC0%:yP7PQ%8yP8PV%<yP{PS%9yPnPV%6y!#Vc&ePdP6ElW4P6O1b4W2W1g01<]94?:A4<W9P<PWP0P5p-0P6g00c1R0g00^C!#I#/!s#$X8<R9g00cNR:PjP6ElP01r|6!s}%n0110301020101P6P3O2b1b=W2W5XC>P6O11Xpb%y>54ZAM<Wl!tI$9P:Px!sr'r!sr%5!tJ'1!#Yc$>00!sv&5b:W2W6XF=XE>XD=!vQ-10001!#cP$110>X0B!sC9!tl-6b0W2W7X?>X>!sq>!sT&7b0b2W2X95WAXB=X<=X@5o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem node_brk2_sound : ltac2:(zQ "10!nhe@9$0?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0").
(* LPS 727298f3 port: written out (rule 11g); the zQ statement above is untouched.  The
   recorded replay rebuilt [cs_ok] with the old one-equation [co_res].  Text of
   boost-beast/http_request's As/AsanNodesMmB.v [node_brk2_sound], with this tree's
   [co_res] arm (one existential over the kernel build). *)
Proof.
  intros cs csa csb E R FULL model T HC Hec Hn HkA HkB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE).
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (U0 & U1 & U2 & U3).
  unfold node_brk2 in Hn. rewrite kn_grant_filterM_eq in Hn. (* [comment removed for export] *)
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
  destruct (brk_grow_admissible A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10))%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hposs _].
  destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
  set (csB := ACS _ _ _ _ _ _ _ _ _ _ _ _) in Hn.
  destruct (vis_add A LIMIT csB (a_brk cs) (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)) as [csB'|] eqn:Hva; [|discriminate].
  apply Some_pair_inj in Hn as [EcsA EcsB]. subst csB'.
  (* [comment removed for export] *)
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 214 HC ltac:((first [clear; lia | lia])) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  unfold brk_grow_admissible in Hposs.
  apply andb_prop in Hposs as [Hposs Hbudget]. apply andb_prop in Hposs as [Hbase Hnf].
  unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
  destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm).
  destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4).
  pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
  pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
  pose proof (proj1 (APS.maps_match_exact nx0 (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as Hmaps.
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ HC) as Hlim. pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
  pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP. pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as HSP0. unfold CEIL, CEILMAX in HTOP.
  set (h := m_vmmaps model) in *. set (b := vm_brk h) in *.
  pose proof (u64_range b) as Hbr.
  assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).
  (* [comment removed for export] *)
  destruct (vis_add_shape csB (a_brk cs) (ELit d) _ _ Hva) as (Hflat & HpcB' & HregsB' & HvisB' & HmapsB' & HghostB').
  rewrite Hsplit in Hflat. cbn [fst snd] in Hflat.
  set (dw := Z_to_bv 64 d). assert (Udw : bv_unsigned dw = d) by (unfold dw; apply u64_lit; unfold KHI in *; lia).
  pose proof (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) as HAwf.
  unfold cfg_of.
  eapply (srz_brk_grow_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w d T HF HE Hh G17);
    fold h b; [exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI in *; lia
    | lia | exact G10 | |].
  - (* [comment removed for export] *)
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
    apply (HkA E (regupd R 10 b) FULL model);
      [split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity].
  - (* [comment removed for export] *)
    intros Hadm.
    destruct (brk_grow_ok_aligned_elim model d B1 D2 D1 B2 ltac:(fold h b; unfold KHI, page_size in *; lia) Hadm) as (HadmT & Hrfg & HadmB).
    fold h b in HadmT, Hrfg, HadmB.
    (* [comment removed for export] *)
    assert (APARTG : forall m, In m (a_maps cs) ->
              bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
              \/ bv_unsigned b + (d + 4096) <= bv_unsigned (edenot E (am_base m))).
    { intros m Hin. rewrite region_free_app in Hrfg. apply andb_prop in Hrfg as [_ Hrf2]. rewrite Hmaps in Hrf2.
      pose proof (RefNodes.region_free_In _ b (Z_to_bv 64 (d + page_size)) (edenot E (am_base m)) (edenot E (am_len m)) Hrf2
                    (in_map (amap_den E) _ _ Hin)) as D.
      rewrite (u64_lit (d + page_size)) in D by (unfold KHI, page_size in *; lia). unfold page_size in D. lia. }
    assert (APART : forall m, In m (a_maps cs) ->
              bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= bv_unsigned b
              \/ bv_unsigned b + d <= bv_unsigned (edenot E (am_base m))).
    { intros m Hin. destruct (APARTG m Hin) as [Hm|Hm]; [left; exact Hm | right; lia]. }
    assert (MAPART : AsanNodesMmLib.maps_apart E (a_maps cs) (bv_unsigned b) d).
    { intros m Hin _. destruct (APART m Hin); lia. }
    (* [comment removed for export] *)
    assert (HKdisj : forall M, know_ok SEGS E M (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)))).
    { intros M. unfold kdisj_new. apply Forall_flat_map. apply Forall_forall. intros m Hm.
      destruct (is_fog m); [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
      cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite Eb. rewrite (u64_lit (d + 4096)) by (unfold KHI in *; lia).
      pose proof (APARTG m Hm). lia. }
    assert (HKf : know_ok SEGS E (Mr A argH E cs model FULL) (kn csB)).
    { unfold csB, kn. cbn [a_ss mk_ss s_know].
      assert (HKf0 : know_ok SEGS E (Mr A argH E cs model FULL) (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)) ++ kn_grant_filter A (kn cs) (a_maps cs))).
      { apply Forall_app. split; [apply HKdisj|].
        unfold kn_grant_filter, kimg_clip. apply know_ok_filter. apply know_ok_filter. exact HK. }
      apply Forall_app. split; [| exact HKf0]. apply (APS.brk_range_facts_ok SEGS _ E (Mr A argH E cs model FULL)). cbn [kn a_ss s_know]. exact HKf0. }
    destruct (flat_x_sound SEGS E _ (kn csB) bb bk (ELit d) HKf Hflat) as (Fb1 & Fb2 & Fb3).
    cbn [edenot] in Fb2, Fb3. rewrite (u64_lit d) in Fb2, Fb3 by (unfold KHI in *; lia).
    assert (Hest : estart E (SA bb bk) = bv_unsigned b).
    { rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). lia. }
    assert (Hrf : region_free (vm_reserved h ++ vm_maps h) b dw = true).
    { apply region_free_intro. intros a sz Hin.
      pose proof (RefNodes.region_free_In _ b (Z_to_bv 64 (d + page_size)) a sz Hrfg Hin) as D.
      rewrite (u64_lit (d + page_size)) in D by (unfold KHI, page_size in *; lia).
      unfold iv_overlap. rewrite Udw. apply andb_false_iff.
      destruct D as [D|D]; [right; apply Z.ltb_ge; unfold page_size in D; lia | left; apply Z.ltb_ge; lia]. }
    assert (Hused : vm_backing_used model <= a_eager cs + a_abytes cs).
    { pose proof (vm_backing_used_le _ _ HAwf (co_minv _ _ _ _ _ _ _ _ _ _ _ HC)).
      pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
    set (req := Z_to_bv 64 (bv_unsigned b + d)) in *. fold dw.
    assert (Ureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; unfold KHI in *; lia).
    set (h' := mkVmMapsFull (vm_reserved h) ((b, dw) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    set (model' := with_vmmaps h' model). set (FULL' := zfill b dw FULL). set (R' := regupd R 10 req).
    assert (Hvm' : m_vmmaps model' = h') by reflexivity.
    assert (Hlz' : m_vm_lazy model' = m_vm_lazy model) by reflexivity.
    assert (HTOPEQ : TOP model' = TOP model) by reflexivity.
    (* [comment removed for export] *)
    assert (V1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 vis A E csB model' x = vis A E cs model x).
    { intros x Hx. unfold vis. rewrite HTOPEQ, Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw.
      replace ((bv_unsigned b <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned b + d))%bool with false
        by (symmetry; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      reflexivity. }
    assert (H1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 hid A argH E csB model' x = hid A argH E cs model x).
    { intros x Hx. unfold hid. rewrite (V1 x Hx). reflexivity. }
    assert (F1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x -> FULL' x = FULL x).
    { intros x Hx. unfold FULL'. apply zfill_out. rewrite Udw. exact Hx. }
    assert (M1 : forall x : word, bv_unsigned x < bv_unsigned b \/ bv_unsigned b + d <= bv_unsigned x ->
                 Mr A argH E csB model' FULL' x = Mr A argH E cs model FULL x).
    { intros x Hx. unfold Mr, mrestrict. rewrite (H1 x Hx), (F1 x Hx). reflexivity. }
    (* [comment removed for export] *)
    assert (NA : forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d ->
                 in_ivs (bv_unsigned x) (vm_noaccess h) = false).
    { intros x Hx. destruct (in_ivs (bv_unsigned x) (vm_noaccess h)) eqn:Hna; [|reflexivity]. exfalso.
      pose proof (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC (bv_unsigned x) Hna) as Hm. fold h in Hm. rewrite Hmaps in Hm.
      apply (in_ivs_true) in Hm as (iv & Hin & Hiv).
      apply in_map_iff in Hin as (m & <- & Hin). unfold amap_den in Hiv. cbn [fst snd] in Hiv.
      destruct (APART m Hin); lia. }
    assert (Wf : ivs_wf (vm_maps h)) by exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)).
    assert (Wb : iv_wf (b, dw)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite Udw; unfold KHI in *; lia).
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csb) by (rewrite HpcB'; reflexivity).
    apply (HkB E R' FULL' model'); [split; apply env_agree_refl | | reflexivity].
    apply (vis_add_sound SEGS A LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SHADOW_ok SINV argH argH_sp0 FS0 0%nat
             E csB (a_brk cs) (ELit d) _ csb R' FULL' model' Hva).
    + (* [comment removed for export] *)
      assert (HK1 : know_ok SEGS E (Mr A argH E csB model' FULL') (kn csB)).
      { unfold csB, kn. cbn [a_ss mk_ss s_know].
        assert (HK0 : know_ok SEGS E (Mr A argH E csB model' FULL') (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)) ++ kn_grant_filter A (kn cs) (a_maps cs))).
        { apply Forall_app. split; [apply HKdisj|].
          apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK MAPART);
            [right; exact B3 | unfold KHI in *; lia | lia | exact M1]. }
        apply Forall_app. split; [| exact HK0]. apply (APS.brk_range_facts_ok SEGS _ E (Mr A argH E csB model' FULL')). cbn [kn a_ss s_know]. exact HK0. }
      subst b. subst h.
      destruct HC; constructor; unfold csB;
        cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_vmops kn mk_ss s_regs s_log s_know s_pc s_next];
        fold csB; rewrite ?HTOPEQ; try assumption; try reflexivity.
      all: try (change (m_halted model') with (m_halted model); assumption).
      all: lazymatch goal with
      | |- regs_ok _ _ _ =>
          apply regs_ok_regupd_same; [exact co_regs0 | exact G10 | intros X; apply (f_equal bv_unsigned) in X; discriminate]
      | |- know_ok _ _ _ _ => exact HK1
      | |- maps_match _ _ (vm_maps _) =>
          rewrite Hvm'; unfold h'; cbn [vm_maps maps_match is_fog am_kind mkind_eqb];
          exists (vm_maps (m_vmmaps model)); split; [|exact co_maps0];
          unfold amap_den; cbn [am_base am_len edenot]; rewrite Eb; fold dw; reflexivity
      | |- seps _ =>
          rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_seps0];
          rewrite Hmaps; apply Forall_forall; intros iv Hin; apply in_map_iff in Hin as (m & <- & Hin);
          unfold iv_disjoint, amap_den; cbn [fst snd]; rewrite Udw; destruct (APART m Hin); lia
      | |- model_ivs_wf _ =>
          apply model_ivs_wf_with_vmmaps; [exact co_wf0 | apply ivs_wf_cons; [exact Wb | exact Wf] | exact (proj1 (proj2 co_wf0)) | reflexivity]  (* [comment removed for export] *)
      | |- Forall _ (vm_maps _) =>
          rewrite Hvm'; unfold h'; cbn [vm_maps]; constructor; [|exact co_bounds0];
          cbn [fst snd]; rewrite Udw; unfold CEIL, KHI in *; lia
      | |- forall z, in_ivs z _ = true -> _ =>
          intros z Hz; rewrite Hvm'; unfold h'; cbn [vm_maps]; rewrite in_ivs_cons;
          rewrite (co_nasub0 z Hz); apply orb_true_r
      | |- Forall (hole_ok _ _ _) (_ :: _) =>      (* [comment removed for export] *)
          constructor; [intros Hk; discriminate|];
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps];
          apply Forall_forall; intros m0 Hm0 Hk0;
          destruct (proj1 (Forall_forall _ _) co_holes0 m0 Hm0 Hk0) as [HF1 HF2]; split; [|exact HF2];
          intros iv Hiv; apply in_app_iff in Hiv as [Hiv|[<-|Hiv]];
          [ apply HF1; apply in_app_iff; left; exact Hiv
          | cbn [fst snd]; rewrite Udw; unfold uE; destruct (APART m0 Hm0); lia
          | apply HF1; apply in_app_iff; right; exact Hiv ]
      | |- Forall _ (_ :: _) =>
          constructor; [first [intros Hk; discriminate | intros [Hk|Hk]; discriminate] | assumption]
      | |- sum_sizes _ <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_reserved vm_maps]; rewrite sum_sizes_app in *; cbn [sum_sizes snd]; rewrite Udw;
          cbn [sum_sizes] in co_totsz0; lia
      | |- vm_brk _ = _ =>
          rewrite Hvm'; unfold h'; cbn [vm_brk];
          rewrite <- (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 ltac:(constructor; assumption) ltac:(lia)); symmetry; exact G10
      | |- bv_unsigned (vm_start_brk _) <= _ =>
          rewrite Hvm'; unfold h'; cbn [vm_start_brk vm_brk]; rewrite Ureq; lia
      | |- eager_used _ <= _ =>
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He; lia
      | |- MInv _ _ =>
          eapply MInv_transport; [exact co_minv0 | reflexivity | reflexivity |];
          pose proof (eager_used_cons_le model _ dw h' Wf Wb eq_refl eq_refl) as He; fold model' in He; rewrite Udw in He;
          rewrite Hvm'; unfold h'; cbn [vm_limit]; rewrite co_limit0;
          change (allowA A E csB) with (allowA A E cs); lia
      | |- forall a, hid _ _ _ _ _ a = true -> _ =>
          intros a Ha Hm Hna Hlz Hgh;
          rewrite Hvm' in Hm; unfold h' in Hm; cbn [vm_maps] in Hm; rewrite in_ivs_cons, Udw in Hm;
          destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)))) as [Hlt|Hge];
          [|destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned (vm_brk (m_vmmaps model)) + d)) as [Hlt2|Hge2]];
          [ rewrite (F1 a ltac:(lia)); rewrite (H1 a ltac:(lia)) in Ha; apply (co_zero0 a Ha); [|exact Hna|exact Hlz|exact Hgh];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [Hm _]; apply Z.leb_le in Hm; lia
          | unfold FULL'; apply zfill_in; rewrite Udw; lia
          | rewrite (F1 a ltac:(lia)); rewrite (H1 a ltac:(lia)) in Ha; apply (co_zero0 a Ha); [|exact Hna|exact Hlz|exact Hgh];
            apply orb_prop in Hm as [Hm|Hm]; [|exact Hm]; apply andb_prop in Hm as [_ Hm]; apply Z.ltb_lt in Hm; lia ]
      | |- SINV _ _ =>
          eapply SINV_frame; [|exact co_sinv0]; intros a Ha; apply F1; pose proof (argH_high _ _ Ha); unfold CEIL, KHI in *; lia
      | |- vm_noaccess _ = _ /\ m_vm_lazy _ = _ =>     (* [comment removed for export] *)
          rewrite Hvm', Hlz'; unfold h'; cbn [vm_noaccess]; exact co_vmx0
      | |- exists _, _ =>
          (* [co_res]: the ledger, the kernel build and the mmap base are unchanged; the
             new heap mapping is apart from the whole ledger by the [region_free] over
             [vm_reserved ++ vm_maps] that the brk grow checked *)
          destruct co_res0 as (kb & Hkb & Hmb & Hrest); exists kb;
          split; [exact Hkb|]; split; [exact Hmb|];
          rewrite region_free_app in Hrf; apply andb_prop in Hrf as [Hrf1 _];
          let tac := (rewrite Hvm'; unfold h'; cbn [vm_maps vm_reserved]; constructor;
                      [ apply Forall_forall; intros [rb rs] Hin; unfold iv_disjoint; cbn [fst snd];
                        pose proof (RefNodes.region_free_In _ _ _ rb rs Hrf1 Hin); rewrite ?Udw in *; lia
                      | assumption ]) in
          first [ split; [destruct Hrest as [Hmr _]; tac | exact (proj2 Hrest)]
                | (pose proof Hrest as Hmr; tac) ]
      | |- _ => fail 100 "unsolved cs_ok field"
      end.
    + (* [comment removed for export] *)
      assert (INB : forall i, 0 <= i < d ->
                Mr A argH E csb model' FULL' (Z_to_bv 64 (bv_unsigned b + i)) = Some (Z_to_bv 8 0)).
      { intros i Hi. set (a := Z_to_bv 64 (bv_unsigned b + i)).
        assert (Ua : bv_unsigned a = bv_unsigned b + i) by (unfold a; apply u64_lit; unfold KHI in *; lia).
        assert (Hargh : argH E a = false).
        { destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha). unfold CEIL, KHI in *. lia. }
        assert (Hvis : vis A E csb model' a = true).
        { assert (Hal : in_allow A E csb (bv_unsigned a) = true).
          { unfold in_allow, in_vis. rewrite HvisB'. cbn [existsb fst snd]. unfold uE at 1 2 3. rewrite Eb. cbn [edenot].
            rewrite (u64_lit d) by (unfold KHI in *; lia). rewrite Ua.
            replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
            replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
          unfold vis. rewrite Hvm', Hlz'. unfold h'. cbn [vm_maps vm_noaccess]. rewrite in_ivs_cons, Udw, Hal.
          rewrite (NA a) by lia. rewrite Ua.
          replace (bv_unsigned b <=? bv_unsigned b + i) with true by (symmetry; apply Z.leb_le; lia).
          replace (bv_unsigned b + i <? bv_unsigned b + d) with true by (symmetry; apply Z.ltb_lt; lia).
          cbn [andb orb negb]. rewrite !orb_true_r. reflexivity. }
        unfold Mr, mrestrict, hid. rewrite Hargh, Hvis. cbn [negb orb]. unfold FULL'. apply zfill_in. rewrite Udw, Ua. lia. }
      assert (Hfl : flat E (SA bb bk) (elenZ E (ELit d))).
      { unfold flat. rewrite (elenZ_lit E d) by (unfold KHI in *; lia). rewrite Hest. unfold KHI in *. lia. }
      constructor; [|constructor].
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros off m Hoff Hm.
        rewrite (elenZ_lit E d) in Hm by (unfold KHI in *; lia). rewrite Hest.
        destruct m as [|m']; [reflexivity|].
        apply store_ok_of_all; [rewrite u64_lit by (unfold KHI in *; lia); unfold KHI in *; lia|].
        intros x Hx. rewrite u64_lit in Hx by (unfold KHI in *; lia).
        unfold wview. replace x with (Z_to_bv 64 (bv_unsigned b + (bv_unsigned x - bv_unsigned b)))
          by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); unfold KHI in *; lia).
        rewrite (INB (bv_unsigned x - bv_unsigned b)) by lia. discriminate.
      * (* [comment removed for export] *) cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi.
        rewrite (elenZ_lit E d) in Hi by (unfold KHI in *; lia). rewrite Hest. apply INB. exact Hi.
      * (* [comment removed for export] *)
        assert (HK1 : know_ok SEGS E (Mr A argH E csB model' FULL') (kn csB)).
        { unfold csB, kn. cbn [a_ss mk_ss s_know].
          assert (HK0 : know_ok SEGS E (Mr A argH E csB model' FULL') (kdisj_new (a_maps cs) (a_brk cs) (ELit (d + 4096)) ++ kn_grant_filter A (kn cs) (a_maps cs))).
          { apply Forall_app. split; [apply HKdisj|].
            apply (kn_grant_filter_ok E (Mr A argH E cs model FULL) _ (kn cs) (a_maps cs) (bv_unsigned b) d HK MAPART);
              [right; exact B3 | unfold KHI in *; lia | lia | exact M1]. }
          apply Forall_app. split; [| exact HK0]. apply (APS.brk_range_facts_ok SEGS _ E (Mr A argH E csB model' FULL')). cbn [kn a_ss s_know]. exact HK0. }
        unfold Mr in HK1 |- *.
        apply (know_ok_unhide SEGS A E (hid A argH E csB model') (hid A argH E csb model') FULL' (kn csB)).
        -- apply (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high).
        -- unfold csB, kn. cbn [a_ss mk_ss s_know]. apply kimg_in_hull_app; [| apply kimg_in_hull_app; [|unfold kn_grant_filter; apply (kimg_clip_in_hull A)]].
           ++ apply AsanNodesMmLib.kimg_in_hull_pure. unfold brk_range_facts.
              destruct (gaps_of _ 5 4096) as [gaps|]; [destruct (gaps_lohi gaps) as [g|]|]; repeat constructor.
           ++ apply AsanNodesMmLib.kimg_in_hull_pure. apply AsanNodesMmLib.kdisj_new_pure.
        -- intros a Ha. unfold hid in Ha |- *. apply orb_true_iff in Ha. apply orb_true_iff.
           destruct Ha as [Ha|Ha]; [left; exact Ha|]. right. apply negb_true_iff in Ha. apply negb_true_iff.
           destruct (vis A E csB model' a) eqn:Hv; [|reflexivity]. exfalso.
           rewrite (vis_mono A E csB csb model' a) in Ha; [discriminate| |exact Hv].
           intros z Hz. unfold in_allow, in_vis, in_sh in Hz |- *. rewrite HvisB'. cbn [existsb].
           apply orb_true_iff in Hz. apply orb_true_iff.
           destruct Hz as [Hz|Hz]; [left|right]; apply orb_true_iff; right; exact Hz.
        -- intros a Ha. apply (hid_hull A HULL_ok argH argH_high). exact Ha.
        -- exact HK1.
Qed.


End SoundB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundMunmap.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!hn1!hs0@1$0$1").
Variable A : ltac2:(zQ "10!ovf$0").
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : ltac2:(zQ "40!jb!hn8!u4!hj6>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
Variable argH : ltac2:(zQ "40!hnd!jb!hj6!hn8>0$2>0@1$3@1$1#k0$0").
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : ltac2:(zQ "80!jb!hn8!pva!pg8!ij5!j6!ps7!qg3@3$5$3@2$2@2$4@1$1@1$0#k0@1$1@1$0#k0@1$6?4SEGS@1$7?1A").
Hypothesis HULL_ok : ltac2:(zQ "80!j0!j6!h9!mq8!pod!hl4!hm0!mp4@2$0@2$5Z@1$4?1A@2$0@3$1$2@2$6@1$4?1A+hgg0Z@2$0@3$1$2@2$6@1$3?1A+hgg0Z@2$5@1$3?1A$7").
Hypothesis SHADOW_ok : ltac2:(zQ "40!qgb!hl4!j0!jv6@2$2@2$1Z@1$0?1A@2$1@1$0?1A@2$3+2+if").
Hypothesis RES_hullH : RES_hull_def SEGS A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : ltac2:(zQ "71!jb!hn8!u4!j6!hnd!ho4!hj6&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1E$6>1M~0>2M'~0>0>1a@1$1@1$0#k0>0@3$3$4@2?4argH^4^1$5@3$3@1$2@1$1@1$0#8@1^3^2@1^4^2>0@2?4SINV^4^3@2?4SINV^5^3").
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis argH_sp0 : ltac2:(zQ "a0!jb!r7!hnd!ho4!j6!ptd!o2!hj6!hl4!hn8>1E$7>1a@1$9@1$0#k0>0@3$4$2@2?4argH^2^1$3@2$8@2$1@1$0#k0@2$6^3$5@2$1@1$0#k0^2").   (* [comment removed for export] *)
Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
Variable FS0 : ltac2:(zQ "10!oo2$0").
Context {SC : StepCfg} {AF : AllocForced SC}.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH E_SP0 argH_agree SINV_agree FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_sp0 FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.

Lemma mmap_len_sound : ltac2:(zQ "ha0!jb!h9!j0!hn8!j6!o2!ij5!ob!nib!moe!hla!jm0!u4!ik4!hj6!hl4!td!jn0!iua!mm6!nje!ml5!jie!hm0!jv6!r7>1E$e>2cs$h3>1R@2$h2@1$0#5@1$3@1$0#k0>4FULL>0@1$3@1$0#k0@1$c@1$3@1$0#8>5model$h1>2ne$7>3nlo$1>3nhi$1>0@b$h5?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^8^7^6^5^4>0@3$4@1$c@2$6@2$6$7$1$1@1$h4^8@2$h0@2$6@2$6$7$1$1@4$d@2$6$7$1$1@4$d$7$1^4^3^2=3len$1@2$h9@1$0#k0@2$5^a@2$9^9Nb@2$2@3$4@1$3@1$0#k0@2$h6^9@2$b@1$0#5+b@2$b@1$0#k0^1@2$2@2$2@2$aZ^1@2$a^1@2$h8+2+k0@2$2@3$4@1$3@1$0#k0@2$5^b^6@2$b@1$0#k0@1$8^1@2$2@2$aZ^5@2$2@2$2@2$f^5@1$8^1@2$f@1$8^1^4@2$2@3$4$1@2$h7@1$8^1+hgg0Z>2E'$e>0@3$4@1$3@1$0#k0@2$5^1@2$9^bNb@2$5^c@2$9^bNb@3$4@1$3@1$0#k0@2$5^2^8@2$5^d^8").
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "#%'qp'0h04__x1h12E'h23HMLh31Hh42Hah57__arithh64__ffh78__varmaph85__with97__sat13h:8RES_len0h;!s;&2h<!s0&4h=!s0&5h>!s0&6h?!s0&7h@4cstrhA5cstr0hB7heq_lenhC4__p1hD2H0hE4__x2hF4__x3hG1zi001zhH2HchI1ei011ehJ!sz&8hK!s0&9hL!s0%20hM!s0&1hN1ni021nhO3H11hP3HxhhQ3HxlhR!sK&2hS4__x4hT1bi031bhU1mi041mhV1oi051ohW2nehX3nhihY3nlohZ3Halh[4Hdivh\3Hhih]3Hloh^2_Hh_4__p2h`4__x5ha4__x6hb4__x7hc1ai061ahd7defaulthe1li071lhf3leni083lenhg1qi091qhh1xi0:1xhi2B1hj2B2hk1Ehl4FULLhm2H1hn3H10ho3H12hp2H2hq2H3hr2H4hs2H5ht2H6hu2H7hv2H8hw2H9hx2HChy3HE'hz2HKh{4Hlenh|3Hlzh}4Hmodh~3Hpri0;2Hqi0<2Hri0=2PBi0>1Ri0?3R11i0@4R11'i0A!vo&3i0B2b0i0C2csi0D2hii0E2loi0F2lzi0G5modeli0H2q0i0I1ri0J2r0i0K1yi0L2a'i0M8a_abytesi0N5a_brki0O7a_eageri0P4a_fdi0Q7a_ghosti0R6a_mapsi0S4a_ssi0T8a_tidseti0U7a_totszi0V5a_visi0W7a_vmopsi0X5a_yloi0Y2b'i0Z2l'i0[3nthi0\1pi0]1si0^6s_knowi0_5s_logi0`6s_nexti0a4s_pci0b6s_regsi0c!s0$svi0d2x'i0e2y'p%0p%1p&0p&1p;1p;2p;;p;<p;6p;4p;3p;8p;5p;7g005`j1CTg00g^j1UTg006Ek10L!s0$ck10XTg01=Wk21bTg002HR0k10OTg02Y=m;1GTg00<6R1k207Tg07W7k10`Tg01L:j!sE$4hdm<1aTg03lik60CTg03RXj1BTg00eBk41TTg02bmR2k20iTg009KS00j20Tg00=\j1MTg00DXR3j26Tg008Oj2gTg02cEk611Tg00EXk11!sW$F8S01k10[!s3$Xk10}Tg00G6k10|!s0$Tk10{Tg00H?k20VTg00J0k20s!s0$Rk20qTg00K>k31`!s0$]k41^!t?$nk41[Tg02>GR4j1!t%$?Qj2DTg01K4k11W!u8$fj2!sa$@7j2:k11ITg07X?k11RTg07YKk11PTg00BDj6\Tg02aHj2!td$42j32k10TTg07ZVj1HTg00:mj1=!us$ik10NTg04lIj21Tg04ofj2uTg050lj2cTg011Ej2LTg01P8j1ETg00Uok20;Tg07[]k21!vf$XAj25Tg07\?R5k314Tg007Fj2@!s;$ck212Tg07]Dk20_Tg01[Sk10J!xd$Vj4!vY$>Wj2Q!wp$6k20\!s9$:k10I!u+$Pj2r!si$ek20~!vL$4j6qTg01?Sj2jTg042Hk10yTg02Mak20xTg07^Fk10wTg04G:k20v!s0$]k30uTg02?bm<0FTg02@Gk40tTg02OQk10STg0472k10rTg01VUj2y!wM$Tj2?!y\$0j2m!yG$4j3iTg0488k10pTg00m@k20o!y/$bk31!ug$NWk21]Tg013_j6lTg07_Kk21Y!{J$Yk20nTg01Mkk20PTg01:?k30!v^$`^k11VTg07b3k1!|n%NZk20?Tg01;=j2|Tg01blk30!su$O[k20<Tg01WFk21OTg014=k21NTg0522k8!{p$53Dk81!}[$hCk61KTg00iXk208Tg00jak20KTg012Bj2;!u}$2k30eTg01^Yk30B!}C$Lk8!yp$7c@k51FTg00l>k6!yD$7cck3!~y$7dDk3!}b$7dgk21ATg0581j2^Tg07eXk31DTg02_bS02k21@Tg057Pk20dTg00kAk11!w?$LOk20b!sd$Nk20hTg0595k20^!s0$[k20gTg01\1k21>!s0$Rj3zTg05;Sk204Tg02P6k30GTg07f=k21!vJ$UVk41;Tg00IEk402Tg001dk70A!xB$ck71:!uS$bk219Tg01h3k61!vJ$nGk80!}q$MBk317!vA$;k41!{,$M6k40aTf6R6f5R7f4R8f3R9g00X]R:g00YgR;P:f2R<f1R=CVf0R>CV+0;32p=[%G>#Gp>0z11=>,@<,`9p=>!s<$#G#Gp=~g00\8R?/6>p=71g:>p=Wg00bRR@P:P2P4P3g038kRAg01aaS03P?P9P<P=P>N<0Fp>15P!sQ+PAP7P8!sF2320V:>p=pP<g001ES04g00_KRAPAg00_kR3P:P=g00`KR2P>H02g00a2RBK0Ap=sP<Q04PAPAP3P=P>K1:p=Zg00aRRCg00b2RD72>p=A!u[&p>001j<==29>p>0115?=/0>p=P20<?>p=RP9P:P;P:P<P=CVP>CV-0;8p=8208=>,L<p>0M1|<=/|>p=a1@9<1@=>528p=9f7RE15671589'01?<==2:?/0>'0'0p=d1@891D<=527!tD$e16?916<='0!s6$t1j!sG1]1D<=9289/0>p>0:%U>#Up>09P:P:P?P>CVp>0]!s4$=!s4&HA2:=>p=316!uS&Y1?=>=2:?p=b1@=>929<p>0Z159</0!sJ%T1@9<=28!s4$>0W10=>,0<p=X1@!vN&=N1j!sJ/U!uW-p>0616<=,0!ty&515?>p=4219:>p=kP=!wp,>J18p>0E!x+/!xT$17NRF!xT$P!xO%OP6!sI,!yU$!s5,!y^$L0DL0Dp=hA278910<=!w4$p>1Z1@=>,`<p=J!s\7p=n1Q<=/r>p=K159<15=!s_$0R1D!vA'1X16!u}%>0Q20n:>p=_B17!v~$I!y;%P>H1\p=F20o:>p=fA2:=!v0&mP6!{Z/H0aH0ap=xP:!s;,E\p=o1j78=26916?!wW&!tX$l%B=008!z4$=S20<?!z4$>03!z`$!x_&1SP<!s4'-0;9p>0k1L=>,|<p>1Q!sj&p=<15!wf,1J!w8&6g!w6$p=w!wh0!wF&v!t#$!wY%p>0cP8!sJ,!vs0BK0A!vx'>0>A2:>?p>0=15!v^'f!sq$2!sq'jA29!ws$p>1=g00\VR2g039MS05g00]^S06#CS07#US08$0LRBQ07#CS09#CS0:#C#CRF#CRG$0LRH$0XRI+1bQ0:$0L$0X$0O\Ig01`4p,4SEGSS0;p,1ARJp,5LIMITRKp,4SINVRLp,4argHS0<p,3FS0RMPE!x&'N;1G207;:RN007:RO$0ORP&0`EPOPN!x5%F[PHf9RQf8RRQ03#GS0=#GS0>#GS0?#GS0@#GS0A#GS0B#GS0C#GS0D#GS0E$0zRSC>P:Q0;PJPKPLQ0<PMf:RMPQPR!tW$<N<1aQ0;PMPJ!sD$PQP6PEJ0C%BQH1Tp,:reg_sound'f;RLP!sb'SP9Q0300iSRK%GS#~!s$'RT-0iSRU'0Q08#URV#MRW#7RX%MFRF,6WRY'0RZPKPUPXPY1g:?PSPW%WWRYH15PSPWPYPTPF%WFJ13J11g00^_S0F$10RTQ0F$0[RY&0}:RX&0|:RU&0{:RK20V:?R[%pWR\5sK%pF9sK\3Z20sK3R\P>P<1gCD20q><#AdB1`:?=H1^RDb6b7b8PZP>b5H1[S0GO8PIPQ%}S,DBRZB00LMSH01f<RF@00LSR]$1W1`H]R]Q07#MR^%MGR_':R`,6]'PPP&0`FPPP>!x:$!vQ$F[XVPP8&1RFR]&1PFE\PPP]!sG$!wT$F[f=R]/{S&0O:Ra1ga>S0Hf>Rb/{S=2a>P0P:f@Rc!s5'PP0P:PPP=PCPP%R!t:$%H>Rd#=PdPdD8&0NORdn010!s#$20000!sZ%fARe#BS0I11eSS0J'uS0K!sA&BRf#BS0L11fSS0M'c!t,%=S0NQ06#US0O#C#C#MRgfCRh#BS0P11hSS0Q40M%UVRV#C#MS0R,:^Ri,L>S0S3aPOPNQ0QP=P>D8P!td3dn10110:00021010D!s:6E00!s82800!v^$]PFPLF[PIPe1DBWRWPHPQ!s$$`PIPhPbPH%EQRB%7]S0TP]PBPBPFPB%CG!uA$!s$%MRGPIP>Q0QfDRBQ0QD9PIP=PcfERjPcD9[^12GdEeCtE]]2]OP=1{eS20;:>S0U52aPPPCPPQ0N!wQ%=Rk#=PkPk!ug6OPNPbP]PFF[216?<%7<S0V15<?%R<S0W414%R9PCP5%78158?PC!xY$!t#$6R5#=P5P5D8R5!t%8hPfPeD8S0X52PPIfGRkPWPHf?S0YQ!s%$P`PIfIRl/@BS0ZPHQ0Y#ERm%7hS0[PhPmPmPfPmP!v2$11lSS0\fJRmQ0\!v6%fFRnfKRoPn!v8'I0:!v9%P=%77S0]Q0X92P5PPP:P0POP:P>P1PNP:!s0$>n200110\00012010\100S0^!sE$1!s+$:P:207::R5!s3$RQ0O#US0_#U$09!s%+#MRp!sF$pPQ212=>Rq#MRr20_=>Rsn0110K0003001010e!s'$!sV+0_>=Rt&0JqRq!sQ9n!z2'!s<&d!s'$!#A`%?CVRuP:P5PG1QQp$0]Rv20\=GRw!u:&5%M>-0\=Rx!sM$>P:P:&0I=!sa$yQ06#MRz,Q<$0IR{1QG=+0HR|P|!tE$I!tE,\!s'$!vR3910IR!sR%3!sR2Y!te%Pv!tW'Pw!tP&y1rG=-0H{R{P{!t6N{!sp+x&0I>-0H=!sN8x!t^9!s<$6!s<,L!s'$P!sj5000P?!t8$GP?20~=>Ry#MRv&0JyRy!wl9R}!sW'PyPv!sJ:v!x:9!#3]$5!#3]&\01XIP!|y%ERy#=PyPyD8!|g$BPhPfD8S0`P>Eq13yf!{D:1P;!#Ge&!uV31100!{b9a!{b1P!{]%QP!{E'MPrP!{7AMPtP!{-Q!z|+M!z|$pPwP!yfApP{P!xPi}P!wWURRv#=PvPv!wW&jPBPhD8P=Eq13vBPPP;!wT$;!wT+;!wT+;P=!tZ5!wT=b%HM#=R1!t\40!t\+QRv#=R}!t^-nPjPBD8S0cP<EqA2;}nA2;1kP;%HLR1#=%HFR}fHRv'3%H]Rx/3vR{PIfNRpPW1DHnH01R516n`,YnR|PIfPRwP<%EnRu,DHRqPmPu15ulRt1buGRs!#7G$wSS0dfQRrQ0dD9RyPI1@=8S0efRR~P8H0Z[^12'0CT,YmI0W3X[[XW;131kP}PIPw%HbR1#=PqCNRq%7=S0fP=PuPtPIP=%Hc#=RtP~PtD9\y^12,0sRsCT3X9X5|\{XY:13}kPx%71P1!to$>PsCT5Xq9X5|XX:p,>reg_lit!#E#&OR|PpfMR5fLRqPoPSP]PkQ0GPFO:PIP5PZ1DH]S0Gg00[0Rs,6],P]I0UQ00PIPp!sF$bH0116bs,PbPIP|PWPHPk%7kS0gPkP`PIPrQ0Y#H!uR$H%EkRxP1Px15x1!vW%rSS0hP~Q0h!#:v$%He#=R}fSS0iP}!#:z$:06xGCT,Y1EeH05E]P>PIPw!tO$cS0j!tR$es,PePI1j~WRs1`H>/3hXTIRZPI1DHfPZfTS0kQ0i/1SS0l'@S0m,`HRZ#W13mZRZePZ207IIQ0;$0y+0xRZ&0wJR152@%}ZRx%}1R}'3R{P@P:&0T@P4&0T:%}=%}>'3A2@=>20v=>40uZ0K@Xh@PZPx%WxP1P}%W}N<0Fp,7!#su%H0tS0nP{&0SZS0o%4xS0p&0S1S0q%4}S0r&0rJS0s/yGS0tQ0s#4%4GR}Q0s/?GS0u#4[[S0v%UV#MRV,m^S0w%7^R1%4V1:^VRx#7[[S0x%4^RZg00^CR4Ai^V=UW4S0y%4x\4^4ZS0z1m^_S0{%4_%7`[\1S0|Ai^_=V4X4ZS0}%4`!sQ&~&0pJS10/yGS11Q10#4Q10/?GS12#4\}[S13p-0RxPTPY%k=S14PUPK20EK9Q06-0o:RV%p^>1_:H5sKS155ZKS16&0NARyPKAsK[VS17PyAO!s0$8Q!sI&9FhP\P!#JP%X0:WC16>`Rt,0=S1:Q0f16<`S1;,P<[[^0:^CxP>%45P5PLPkO4b5b;b9b<b=b>b?bAb@b:bB-1]fPsP=ElQ0mPvE\13mfRsePsP:PhPIQ0k/jWS1<1DH>S1=%7>S1>PtPIfVRt%HBS1?!{C%>RsQ1?Q1?PsQ1?,5!~z&tSS1@fWS1AQ1@D9S1@!{O%n#=S1BfXS1CQ1B!{Q+sGCT'YEeJ1ZXf:fUS1BQ0k/1SS1D5JHRs#W13os!tp$Q0nP{Q0oQ0pQ0qQ0rQ0tQ0vQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q11Q13PTPYQ!w\%Q17PyQ18Cn!vw0Q1>%4=S18[^0:P>PpPvO2!v\;YhPh%EhS1EQ1Eg01_<=KhzH0RP:%EBRsPIQ1B!~w$j!s$$`PIQ1A%=>PH%EjS1FQ1>P>Q1FQ1F!s-$!#Fs$Q1A!uj$FQ1CQ1F!~|&=<S1GfYS1HQ1G!#J20XG:PIQ1<PHPBH1X%7BS1<@0QB`S1GPIPt%=s1DHsS1ICNS1J%7sS1K15ssS1LQ1L'0S1L1bsGS1MQ!wj&=uRuQ1C/@uS1NCN[^12S1O'0S1P'0S1Q'0Ru'0Rs'0P9Q1GPsQ1B!u+$G9JHt!wq%qsS1ReS1SQ1R!wve6Py!w}+7!|#'5!|#2XCxQ!{w$Q0VQ1;'0!{u/|P|P]Pl!{u;Q1JPuQ1I,gIQ1KQ1QQ!u0]Q0FQ0?#_Q0>#_Q03-0n:S03'IS0>'Ig01b@S0?+0P<0@TPY%k<S1Q%k9S1K?F9X?F9X7F=!uo$09#US09#fS1I=OKV20EK75ZK!v,%I9sK[!s1$07#fRu9OK[S0720EK6!v@$J!vN$Cn!vG3E:XF:XCxX_x15<>S1:/09%79Rs1P96Ps[!vX%E:^F:^Cx^_xP>Q0uQ12Q10g055i'5+0m+0mS0u%E|RsAK|Gz'5P|Q0sPsPLPlp,7HULL_okS12O8!w=;LQ1PQ!y<fAOKVVS1RQ1R5ZK!ue015>>!s@%'0!~8%sO1!t^;MQ1O&1VBQ1@Q1N,gIW^X12FxFxFxQ1?&1UBElc0=PoP>Elb{W|Y0@P=P>O2n20!#Rs$1012!#R|%bcPvP>DoWD!s-/E\WDP>O1b!s+0W2W3P>O1157?!#Q|$dPPPdP0POPxP>g00c1S0XP4!#DJ/!s#$XIPS1?g00cNS1@Q0`P>E\Q0XPIPvPWQ0jPc16c`PIPmPjPH%EcS0jQ1<PBQ0jQ0jPhQ0j!#S}&mSS0jPoQ0j!#W3%kPqPk!#3}+K0l00?>!u#,n2!tX$3!ur%211000!s'$P<O1c0BbTW2WOZ0F:P>O1Q0Y/{S&0N:S0`!#Wg$0P:PP%Bc11cS'u!s5%Q0IQ0J!#[P$Q0NQ0LQ0M60MgQ!#Zx+M!#Zx`POPNPFPLPMF[Q0KPaQ0H!t6%'u!#^;&%BB11BS!s7,PPP=!u#'n11nS'cS0M!tt&%BkS0L11kSS0K60MgS0J!t~-K!t~fePcQ0YD8S0N52PPIPjPWQ0GQ0TP]P`PIPkPfPH%E]S0TPeQ0TQ0T/5cQ0T!#\W$KPvQ0K!xH&BQ0Z!#8/$806GCT,YeEeH05I0US0T]2]QP=%Bj11jS'uQ!#\^&!wf&!uk&WQ!uZ2<!uZLOPNPfPePcF[!w>$K'c!wK$%Bv11vS'c!wL,mQ0j!s6,!#b`&11qSS0j9Sgq-03ES0HQ0S'|!tX%j01SES0jP>H0k!t^LkPnPjD8S0S!v}%oPWPHPhQ0[Ph!v~$5PvPHQ1EQ0gPkQ1EQ1EPnQ1E!|M'5SS1EPpQ1E!w'&mP|Pm!|M,H05E]S0g]2]PP=%Bo11oS'cQ!#`\/H@1Q=i!u>&P=!u77OPNPvPkPnF[%RRQ1E9Sg51L<i3aPC1gC>%RQ11pS9Sgp1L9i3a=2C>PC%RLQ0d9Sgw1L7!s<+!#`w&Q0hPFP6D8S0h!tA85PqPoD8S1E!v>%r!v>$l%7lS0jPlP`PIQ0iPpPH%ElRn%75S0HP5PnPnPqPn!vD%Q0lQ0mCN!v>$wQ1BPw!v?4m]2]HP=%RM11|S9Sg|1L8i3aS0U#A!ty%dPLP7!#Rb%qPoPmD8S0d52P!#Xn-Q0^PE!#SU7Q0hQ1E!#YJ$6o!sZ1aPb!#T1;11~SP]PE!tH&pP5Pq!#Ud&]5!#Ud-Q0b&0[;R0P;^d;]e^N@P@P;P<Q01P;P;P=P>P=!t7%7!w,%2010:10Z!sH'<P=P6P<P>P9O3!sP8n011!wg$2!#Wu$4Xd;Xe0XN@p?100110[PSg07foR@P0Q05P@Q0kPL!#Y/'1<010S10R10U10X10O10V10Q10M10N10P10T10WP8!sX$]00016010a10b10_10^10`10c%=?!tp'!vS6Q0lPbPR!vR&|PpP5D8P<EqQ0l=2;|Q1D=2;wP;Q1G13er13FrS1GPIQ1APW1DH|H01Rp16|`,Y|R|PIQ1HP<!#FZ$DQ0iQ0iPs15s~R@1bsGS0l!z$$1H/1SR0fZRn/@0S0kCNS05PIQ0ef[R0!#WL/'Y!#WK-cwPeQ!tP%HQ1C/1SS0iQ1DCN!t?$fP=PsP@!{1$5PIP=11nSR@1@0@S0e!#6T$'0S0l!#WW$p|[XY:13LwPFQ1D!#3V$s15s>Q!sI,XX:Q1AQ1F5Sg-03fR|1LFiRp<0YE%A|%Ap'0Q00Q1CQ0i!sJ%h#A1L]i#APIQ1C!}C$w!s$$!}?$kPH%EwRpQ1<PBPpPpPbPp!}:%P@Q0e!}9%110SRpf\RBPp!#jw1P>ASgn@-03j#A1Lci#A%RkRj11BS9SgBR@<0Y=%Aj%A@!tj$%Rv#Af]R@11@S5Sg#APIP@PWPHQ1B!s%%P`PIf_Rjf^Rn<00S!sA$#ERpQ0jPl!tt$h!tt'11jSRpf`R|Pp!#6N$11|SRpfa!ty6%Rm#AASg|p#AQ0020<=>#A16<=[Rp16=>20<<=#AR|[169<\|21O=>!#`,%!#5?$12!s-%0XU:XN:Pp^U:^N:P>P?P5P<O3Q0HQ001L!t$$5!t$%5=>1L!t#'5!t#%N!t#AR|!t%'RpP>PgfdRm11mS'<RsP9O315gs!|4$>PoPiPMO315oiQ0;fhR!#|$&fgRpPmfeRmJ0C%Bp11pSR|P~P@PrL1MAJHM|,5~Q0;fiR~!s[%~PMPmffR|!sY$M11MSR@P5PnPqL1LAJH~@/55Q0;fjR@!sY%@P~P|Pp!sW$~RJ11~SRnPjJ1K208JnRJ#4PJP_1:^JAJH@n+0KH1JQ0011@SRn,<@RJ15J_'P1:^JfkRJ=JHn+0K!y/'fbR@P@P@!y-$lRn@00JSPH%E@R@PtP@15@w!xz%nSRwfmRjPw!xz'jSRsfn/@sRL!}%%:06@GCT,Yt!y,+1<nwRw15w_'P1<js,:^1`HL+0KQ02P:fpRLfoS0</1SRs5JHRjQ0</<s,:^,;>'3XG:1bjGP>frRsfqS0;!~j$H'@S0j,`HQ0;Q0H'<!sV'P:11sSS0e,<sRw,:^S1<,;=1b>GS0kXG:S1C1rwgS0i/QgR_,:^fsRn11nSS1F'<S1A!s[$D,3>XG:P:P:&1I^!vC$_PwP:\:/g@Q0e,@nS0[,`HS0l#WQ0l,3~S1GeS05Q1G!#MgGR,m^R~Q0R#4%7i[\1RnQ0R=i^!#^C$R@%4i\4^4ZRif{Rw11wS'<Rw,m^S0Rf|R_11_S'<S01#4f}!s5%S0b'<S0a,:^S0h#7[\1S0^f~S0KQ0K!vZ$L'<R_!t4+S0J1:^_#4!#_T%W!#OO=%pgR_:0e:VS0M>0B:_/wV,v!#OY1r>g/Qg/3>^0:P>p+01BS0ZQ0Z!tL$G'<S0I!#Ok3JbKbLbM!#Os&L1HQ0i!wP$N1:^g';P^Q0iPgQ!v}KP~PnP@PiQ0RQ0^Q0JQ!uQ@PKPK20c_VPyQ0M9OK[I0>!uN15g>1r=g#4!#]:$Q0IPq!#];3!u>2PTPYPXPUAOK[_!su,%4gP>b5I1FDoQ1N/;GQ1<'3Q1A/rg,:^Rq/;GS1A1;9>/bG!zG$1;<qS1<!sR$CQ1<!t%'PK!$5W'%pGR3/w[,vKJ1ES04!t@,&0=GRAQ0X[S1CP>b581CGQ1A,;<B1B<qGElQ1DP>Dob3Q0lP>ElY0;Xg:!#Sf10012!#I1%1bmGRqePq%Wj13|jRjePj!w`NfxR!#LL$<,m^fy!s3'S0l#4fz!s5+1D,:^!{/$Ai^w!zs%1:^wS1A!zs&!#[M6KQ0b5JHRj/yG%4jp+01AS0Kp+01@Rj!zH$b5JHS1</?G#4\}[Q0L9JHjS0L?KGzRq01AG%4qQ0Z!|G&1N5JHRq?KGz/^!sZ'b,<j,:^Q1<<1DeQ0KQ1N'<S1N,:^/;>,3qXG:-1@:Q02P:p+01CQ0G5JHReQ0I!sK%'3XG:AKe!s~$/;G/3e!|F%ES0Ip+01DRe/1SRj5JH1<ej!s\'PHp+01FRjQ0IPSC>?KGz00dG&1?AS0I!sE%GS0GPj!sE'Rj1^jG,;G1?jG'Q'3[20bjG%7GRj!sV%HS02Q0G!sW'S0K/?GRe16eG'P[Q0K00hG16G?S0K!sX%IS1<Q02!sX,2!sX$,6G@0fe?[Q0200^G!sS%JS02Q1<!t^+e/^G$0=\A20ge!sJ&K!sw1Re/?G/3e\A1^eGP:!sK%L!so1/?!s@+MRe!sd&00dGQ!v#'NS02PePSC>Re1^e!u{%e!u{+!tK'OS0I!se&!u@'!ur%\j!u?$hGQ!uo'P!vI$!wA$S0I!uk3I!uk,Q!t`+R?!uf-?!sE&RR?!tg'!u`7SReP?PSC>!uZ$Q00!s=%T!s\,#416e`1;Q!sw&U!sX''3Q0!s:&V!sU'#4!s7%W!s{&6`PvP=O1%47S0G\}Q0FQ06$0J-1>:R?Q0D#_Re5z:Q0@#_S0@9z:?Q03'I'IQ0E#_S0EQ0B#_RA!s@%A#_S0A'I,Ie'IQ0=#_!sT$Q0?+0PS0=+04+04!t5$@!s@$,IeQ0E!sc%C#_Q0!so$,IA!t1%!sW&<0@T40@PY%k6?F8X%k77FE9FX<%kE?FEX?FEX9FX9!#f?%!#5n$yQ09#U#f:0G:3Q0_#C#fR?60B:,wu,vKCnPyPK!#8L$j[3!sV%C#fRe9OK[AsKe35ZKI0>!sM%!sy$B0B:u3%pz60e:B0G:3V>0B:e'w!sw+1w?[,v!#gR$07!s,%8#C#f9OK_!s5%O#fR?9OK[20EKQ5ZKPyB0G:V3/!tg&FhFh!#gd8S:X`:Xa:Xb!#k?$C1;GE/Q7,3<[16EG,PE\jQ1CAK8Gz1;G9/QR'3[&0=EQ0G15gR1PR]1;EG/3R[!s#%!#hC+S:^`:^a:^b!#l/$Q0uPEP]P6p+01YR6116SR6'<Q0sp+01Z=JH6PbPFPfPhQ1HP9fcQ12O?b5b9WoWn!#986!s/%c0Jc0Hbwbvbubtbsc0IbgbrbqbpbmbDW3Xh!#9v=b[!#<h7Rc0A!#<m&AK|!#6S+|e%E|/3|R|eP|P:PpPIPLPW1DHMR|PM16M`PIQ0jQ1=PBP>15>tQ0k!#Y%$eQ0[!#Nn$Q1FftRtQ1F!#Lq$!$&@$BH1=K0lXG:Q0</jWRW1DHpRB52I16p`,YpRMQ0;!$D<$S=2IBRz%70RhP0PpPpQ1BH0RR01bpGS1B!tB%HQ0jCNRf!tD$!tP&[^12RF'0R6'0R]'0RE'0Rj'0PIPSA2I>|XTIPIPBPS21<HSH1;RBPWPmElPMPj1`HSRS#W13pSRSeRHPS!#B$Ol,m^RjQ1D#4Q1A#7[\1RWQ01!#F1+IQ01,:^R|!#=1%R3!#=36L/yGRQQ0L#41?q!#<9$Re!~p$>,IAQ!#qX,Q1K?F8X?F<X%k8!s1%8X!~A-:#fRX00cV!|d$19!#qU&!|v&!~6%X!s<%JPyQ15CnI0>Fh!#Cf2!|j,!#tz$18@0Q=`15g7Q0]Q0G/0RQ0]@0Q7`!|@5!|7&Q1NPJQ0sPqPvPtPoP5Q12O:!#DS9R!zf'PMePzPEPBPhP]P!w]Q1yLG%4L1?s!vg%Q1D,m^%4w%7|[\1Q0a!we+Q0h!#Ai;!#}:47!#}:4Q0f!#}7%JP5!#Fz;!uM,0P6!uDRPjPWPIP!yM6PQPe!ts%QQ1K!xp&AOKu?R?Py!s1$VuRuPyAZKu?!#67715=<RDP<P9P9P8H0R\D!x4,P>PmPqPJPkPvO5!uQEeQ1BPFP=P>Xyf!#tV'%EpP>Elb~b}W[W^!#tL>bjbib\b3bZb3b]b3WZW]!sV>HW\WH!sF?PrP>DoW3!s-/E\!#s,$b!s+0W2WHQ0Ug01<]52CQ0d!#uG&Q1?Q1@!#ep$\Q0XQ0m00?>!sY%!$=Z%1020101P>P<O2bHbTW2WPZ0D:P>O1%BlQ0\'cQ0`52aQ0c!t$20S!t$+g!t$+P!#c@&1021!#tq$!t+&PbVW2WQZ0E!#tn%PQ0Q'u!t+%PPPdPOPNPcQ0YPbF[!t6/N!t6+T!t6+Q!t6<Q!t6$O!sF<ObVb2c0<c0?bzbfW2WxXX:XY:XW;Y0GWlY0>Y0CWko"). Qed.

Lemma bv5_10 : ltac2:(zQ "80!jb!hn8!ira!j6!mr1!jk0!jk5!jm0@3$3@1$1@1$0#5Kd@3$5@1$0#5+aKv$2@2$6@1$0#5+a@1$1@1$0#5@2$7@1$0#5@1$4Na").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "h02b1h12b2h21nh31Hp;1p;3p;2g006cj13Tg0042j32Tg009fj20Tg056lj36Tg005`j15Tg00g^j1=Tg006Ej1<Tg00=\j1;Tg01A7j3:Tg02>Gj17Tg00?Qj28Tg008Oj29Tg01L:j14Tf0R0#4#4p=1g05A3R1%30R2f1R3#3R4g009Kf2R5#3?230g00X]R6f3R7/05107332R8[10531050526%37?253[R9f4#3?275\8A6530P0n2001000000120000000W1W0W2P9^14^02^21P0g00]^#5#=R0#<R1%50#;g00cN5:1g01aa#1#1#1#1#1#7,81R01010,96O4b3o"). Qed.
Lemma bv5_11 : ltac2:(zQ "80!jb!hn8!ira!j6!mr1!jk0!jk5!jm0@3$3@1$1@1$0#5Kd@3$5@1$0#5+bKv$2@2$6@1$0#5+b@1$1@1$0#5@2$7@1$0#5@1$4Nb").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "h02b1h12b2h21nh31Hp;1p;3p;2g006cj13Tg0042j32Tg009fj21Tg056lj36Tg005`j1=Tg00g^j15Tg006Ej1;Tg00=\j18Tg01A7j37Tg01L:j14Tg02>Gj19Tg00?Qj2:Tg008Oj2<Tf0R0#4#4p=0g05A3R1%30R2f1R3#3R4g009Kf2R5#3?230g00X]R6f3R7/15117332R8[11531150526%37?253[R9f4#3?275\8A6530P0n2001000000120000000W1W0W2P9^14^02^21P0g00]^#=#5R0#;R1%50#8g00cN571g01aa#4#0#0#0#0#0#9,:1R01110,<6O4b3o"). Qed.
Lemma bv5_17 : ltac2:(zQ "80!jb!hn8!ira!j6!mr1!jk0!jk5!jm0@3$3@1$1@1$0#5Kd@3$5@1$0#5+h1Kv$2@2$6@1$0#5+h1@1$1@1$0#5@2$7@1$0#5@1$4Nh1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "h02b1h12b2h21nh31Hp;1p;3p;2g006cj12Tg0042j31Tg009fj23Tg056lj37Tg005`j15Tg00g^j16Tg006Ej1<Tg00=\j1;Tg01A7j3:Tg01L:j14Tg02>Gj18Tg00?Qj29Tg008Oj2=Tf0R0#4#4p=0g05A3R1%20R2f1R3#2R4g009Kf2R5#2?130g00X]R6f3R7/35137331R8[13531350516%27?153[R9f4#2?175\8A7530P0n2001000000120000000W1W0W2P9^14^02^21P0g00]^#5R0#6#<R1%50#5#6#;g00cN5:1g01aa#4#0#0#0#0#0#0#0#0#8,91R01310,=6O4b3o"). Qed.

Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "p'0h01Hh12H0h22H1h31Th41ah51bh61ei001oi011tp;1p;2p;3p;6p200R0g00?4R1p4p710p8P0P1p4p7210p8g002HR2j12Tg00Uoj20Tg0042j31TP1j63Tf0R1f1R3f2R4#21043104131f3R5#2R6P5P2f4R2f5P1P1P5n10110000021010100X6610541053P1E3A1543A1254P1W2P1O1b1W0W5W4X30o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma split_flat_estart : ltac2:(zQ "h90!jb!ob!h9!j6!o2!r7!j0!nk9!nke!hn8!hnd!hn1!u4!ik4!ij5!ho4!ng6!hj6!hta!mud!iia!jkc!hl4!hla!jv6>1E$h1>1M>0@1$9@1$0#k0@1$c@1$9@1$0#8>1k@1$b$h2>1e$1>1b$1>3off$2>1n$1>0@4$h4?4SEGS^7^6^5>0@3$3@2$e$1$2@1$h3^5@4$d$1$2^4^3>0@3$3$a@4$h0^7^5^4^3$f@2$6@3$3$2@2$8^a@2$7^6^5@2$5@1$0#k0@2$4^a^7@2$6@2$h6@2$h5@2$8^a@2$7^6^5@2$5@1$0#k0@2$4^a^4@2$h8+2+k0@2$h7Z@2$5@1$0#k0@2$4^a^4").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "##E$h04__x1h14__x2h22Hah38RES_len0h47__arithh54__ffh64__p1h76__sat4h8!s/%5h9!s/%6h:!s/%7h;!s/%8h<!s/%9h=8__varmaph>5__with?4__x3h@4cstrhA5cstr0hB1EhC2F1hD2F2hE2F3hF1HhG2HKhH3HflhI3HsphJ1MhK1bhL1ehM1khN1nhO3offhP1xhQ1yp&0p;1p;4p;2p;3p;<p;6p;9p;7p;8g005`j1ETg006Ej1T!s/$cj1OTg002Hk101Tg00F8j1YTg00eBj4qTg00<6j2RTg05Zkj1f!s8$Vj4cTg0042j36j1QTg05]@j4^Tg05h?j2;Tg06DYj2:Tg00>Wj29Tg00=\j1@Tg00@7j2WTg00XAj27Tg009Kj25Tg042Hj1hTg02Maj2gTg07^Fj1eTg02>GR0j1DTg04G:j2b!s/$]j3aTg008Oj2GTg02?bl<`Tg02@Gj4_Tg02OQj1NTg0472j1]Tg01VUj2M!tW$Tj2PTg00g^j1=Tg00D0j2LTg00E4j3UTg0488k100Tg01L:j1F!s/$Yj2BTg01MBj3K!s/$kj2\!s]$Xj1~Tg01:?j3ZTg00lbj2H!vz$Xj1}Tg01^;j4<Tg00G6j1v!s/$Tj1uTg00H?j2XTg00m@j2A!uO$ij1t!s\$Yj3S!sJ$bj3pTg01h3j6oTg00J0j2l!s/$Rj2kTg00K>j3m!s/$]j4n!uO$Xj2VTg06NIj6jTg01[Sj1iTg01\1j2r!s/$Rj3sTg00IEj4CTg00M6j4[Tg06M7l9wTg034Mj6xTg007Fj2y!x&$fj2zTg001dj7{!u3$cj7dTg00nGj8|Tf0R1#E#Ep=?g00\8R2/71p=0f2R3f1R4/y1'zp=21V21p=3g00X]R5?641p=8P5P4g00`KP1CCp=I!s4$1ER6g00_KR7P7g00_kR8P1g00a2F{p=1!s[%17N!s[%>P3P6P7P7P8P4P1Fdp=Jf3R9!s;+3P4P1G|p=4g00\Vg00]^R:#ER;#?R<#E#?R=#TR>#OR?%T<#O$01[g015\#Yg00YgR@p,4SEGSRAf6RBf5RCf4RDCq1R@5%fDP@P5P9P3Cc36g00aRREPBPD!s9$^g00b2RF36f9RG1;CD':RH#0RIA2>G9RJ,9H%@;RK%@=RL'WRM'7RN%3JRJA2>GB,8H15NJ'5f:RJ1;BC':A2>JD'9/7Mf;RN=2>C#3f<RHPGf8ROf7RPPDg00bRRQ1R??%hA'gR?p,1ARR#eRS36%D?RT%DSRU'8RVPQP5%QQP0%Q5%D4%D1'8A6Q411b413aXQQXPQP?PT1G5TPSPU1G5UM<`p,7!#6_%C_RQPV%N?R?%0TRT%NSRS%0URU%]RR0%?=#?#?#@R='MRW%00%0=RX1P0=RY#0[[RZ%=;#=!s$$@R[,LKR\%3KR]%0[1WK[R^#3[[R_%0KR`g00^CRaAUK[4UW2R[%0^\a^2`R^1LKLRb%0L%3M[\]R]AUKL4VaX2`RL%0M!sM%`&00RRR/M=Ra%0R1PR=R=#0\X[RXp-0Rcg00^_Rdg01aaRe#F#FRf#FRg#F,B51B5g1B5eRe5K55K5g01b@Rg'\%~dRh3Z%YdRiP5P5P51H59RjP9%}5RkC<P3PkC<P4PkC<%v5Rl%u5Rm1X52Rn1A5<R<'I,1m%t7RoPm1A5:Rp=S5<1X5K=p5>RK'>,1mPoPm1>np,1mR<!s3$A5;R;,>n,1mPm!{]+CEoR75JmPo1IpK,1m9Jm<C4!s$%1lm8R8P1P31GEF1k13=6EFdAm524CnRFb5b=b>X05X15X?5W6%331949/7M%03%0DRE/5B1VDM,5E[[[[^05^15^?5^6cP1A65Y2A65=2g055i,7R'5'5RRfFR=f@52>P0fBR2fARY';,:=PJPNPHp,7HULL_okR=O8b4b7b8b9b:b;b<bAb@b3EjA2>HG1;OP,:H'8f=RE1;GO':RBA2>EJ'8A2>EPRE,9B/7MRB%3ERE'5PQPVP?P!z}$PWPZP\P_P[P^PbP]PLP`PaPX%i:,r51B5f5s5=K5e/\g=ZdhPi!x9$3RdP4PjC<PlPmP5P;g016gRjPpCC!w]&%=:,A5!wP%=Jm7PoP5PpPjP;!sI$C4C4P8P!v{3X6c1841%09/5D1839!vl3PRP0fGR0fD52>fC/;2,:0R2PJP=O6!vE7PBPE!uhGP!uR$Pd!zR%PlPmAS5p;/>K,1mRKPoPK!u$51914/7M1943/7M!ty&P1A2>0YR0P2PHO3!tc8!t_J1H54PlPm1I!{J%!vx$!tU2%31%34[^05P1P0PNO2!t@7C[C[bFWEWDXCIPAPGPOPPPC!#7@$P1M9wExWHWIWGXN@XO5XK@WLWMWJWBo"). Qed.

Lemma covered_maps_subtract : ltac2:(zQ "e0!h9!jb!lma!hn8!lt0!hnd!hn1!krd!ij5!j6!nl8!nm9!ln5!hl4>1l@1$6@2$8@1$3@1$1#k0@1$3@1$1#k0>2lo$0>2hi$0>1x$0>0@1$c^4>0@2$d^4^3@3$9$5@2$2@3$a^6^5^4^3@2$4@2$2^6^3@1$7@3$b^5^4^3").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "h01xh11Ph22hih31lh42lop;1p;2p;3p;5p;4g005`j10Tg006Ej1ATg006cj1:Tg00<6j29Tg00F8j1@Tg01iKj13Tg00XAj2;Tg07h=j32Tg01oIj25Tg07i9j36Tg01:_j11Tg01;=j24Tg0042j37Tg01n?j28Tg009Kj2?Tg07jBj5>Tg01Wfj3<j4=Tg00]^#0#0#0#0#0#0#A#:R0/90#@g00X]R0f3R1#3f2R2,;1g00aRR3\0f0R4f6R5f5R6f4R732R8'5f1R9P4O1A6564#1'4X00/55570]1R:18841854A6674#1'4573^00R3A2671#31?:3P6P7P1P9P4D>3<P2C=UUX00X20W4W3o"). Qed.

(* [comment removed for export] *)
Lemma len_eqb_sound : ltac2:(zQ "d0!jb!hn8!j6!o2!ob!hnd!hn1!u4!ho4!nn3!hj6!hta!iia>1E$a>1M>0@1$1@1$0#k0@1$7@1$1@1$0#8>1k@1$6$b>1n$4>1m$4>0@4$c?4SEGS^5^4^3>0@3$2$5@3$9^4^3^2$8@3$2@1$1@1$0#k0@2$3^7^4@2$3^7^3").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "h01Hh11nh22Hah34__x1h44__x2h52b1h62b2h72A1h82B1h91Eh:2H1h;2H2h<2HKh=1Mh>8RES_len0h?7__arithh@4__ffhA6__sat3hB6__sat4hC6__sat5hD6__sat6hE8__varmaphF5__withG4cstrhH5cstr0hI1khJ1mhK1xhL1yp;1p;4p;3p;2p;6p;8p;<p;7g005`j1?Tg006Ej1OTg006cj16Tg002Hj1wTg00F8j1LTg00eBj4aTg07kVj3]Tg07l]j2ATg00<6j2ITg00EXj1GTg05IKj32Tg01;=j2BTg06lUj3tTg01==R0j2jTg007Fj25Tg0042j30j1HTg07mhj3`Tg008Oj2=Tg013_j6^Tg01blj3\Tg009KR1j2ZTg05K[j8JTg05M1j2<Tg00XAj29Tg009fj28Tg056lj3YTg042Hj1XTg02Maj2WTg07^Fj1VTg02>GR2j1@Tg04G:j2UTg04G]j3TTg02?bl<STg02@Gj4RTg02OQj1FTg0472j1vTg00=\j1DTg01VUj2QTg00@Tj2NTg00g^j1;Tg00D0j2uTg00DXj2MTg00@7j2sTg00E4j3nTg0488j1iTg00lbj2hTg00FXj1fTg01^;j4eTg00G6j1dTg00GTj1cTg00m@j2KTg00H?j2bTg01^Yj3>Tg00IEj4CTg008ij1gTg00J0j2_Tg00JRj2kTg00K>j3lTg00K]j4mTg00<Vj4[Tg01:?j3oTg001dj7pTg00nGj8qTg00>Wj2rTf0R3#?#?p=:g00aRR4g00b2R5703p=1f2R6g00YgR7g00X]R8f1R9g00\8R:C[;o3p=319:3p=4P9g001ER;g00_KR<P<g00_kR=P3g00a2Fpp=Ef3R>P;P<P<P=P6P9P3Gqp=P1r3:p=7g00\Vg00]^R;#?R?#:R@#?#:RA#ORB#6RC%O@#6#w[g015\#Lp,4SEGSR@f4RDP>P6CaA]>69#11A>6RE1I78RF%GFRG73>RHA3F6GRI52DA2DIH'BRI;t3%1E%1I'jP01AD>#1f5R0A3FDGRI;2HA20HI'B#1f8RH/5015HD50CP31A0D#1f6RE?`03A07E0P7PEf;RJ/53f7RK,5JRL50CX17f:RM/5E,=CPKP3E^b0W0P3O1A3F0GR0=2EIA2EI0'B#1A3FEGRE=2K0RIA2K0ER0;\3%1I%10'ZP1A3FKGRK=2HE#1A2HEK#115JH=0CLP3f9RL=3FGRKA3FHG52M#1A3FMGRH92JK#1P@f>RKf=REf<R0A3FJGRJPHPLP9GJ1<KH1<KJ'9P@f?RHPKPEPJA3F0GR0PMP9GJ1<H01<HJ'9g05A3RH%63RJ%69R0P1%66?09318>618>9508R1[18691863508%6>?069[RG%6D?0>6\1AY693P3n2001000000120000000W6W5W1PG^60^5J^1HP3PBfARH/5K15HEg00bRRH1ICC%X@'WR@p,1ARC#VRE30%@@RK%@ERJ508R0PHP8%HHP2%H8%@9%@3508A0H931U933TXLHXKHP@PK1=8KPEPJ1=8JM<Sp,7RES_lenCRP0%F@%4K%FE%4J%vCRJ%:A#:#:#DRA'Q%4J%4ARE1NJA#4[[%D?RJ%;?#;#;#;#DRK'u1M:J%4K1sJKR@,M:[[%4JR0g00^CRHAnJK9UW2%4@\H^20%iCRC/QA%4C1NCA#4\E[g00^_RE#G%LEP81h86P9%f8Ce%d8%c8REP81K8;R;1b8:RC5>8=>8CRAg017NR01K8?R?=>8C=>8CRCCC,EE%g<R<PEP8PCP0PACC,EEP<P8P;g016gP?CC,EECPCP1_E=P3P61=451k36#1dAl8:9Cmb@bEbFX38X48%73#7%79#7R:'9%76#7/9:A086>[[^38^48P3fIR8fE'5,8BfF,58,8BPLPMO4b?bAbBbCbDbHbGb>O4b0b8b7W;W:P9P3O2n2001000000121000000b0W0P3O1n200100000021000011000b0W0W<XJ7X17WIW=W9o"). Qed.

(* [comment removed for export] *)
Lemma kzero_x_sound : ltac2:(zQ "h80!jb!hn8!nk9!nke!j0!hl4!hn1!u4!j6!ob!hta!nnd!iia!jkc!r7!td!hnd!ho4!h9!no6!hj6!hla!jv6!jm0>1E$h4>1M>0@1$1@1$0#k0@1$7@1$1@1$0#8>5allkn@1$6$a>1k@1$6$a>1b$9>3off$h2>1n$9>0@4$c?4SEGS^7^6^5>0@4$c?4SEGS^8^7^5>0@3$8$h0@5$h3^7^6^5^4^3$h1@2$4@2$5Z@2$3^a@2$2^6^5@2$4@2$5@2$d@2$3^a@2$2^6^5@2$b^a^4@2$h6+2+k0>1x@1$1@1$0#k0>0@2$4@2$5@2$3^b@2$2^7^6@2$e@1$0#k0^1@2$h5@2$e@1$0#k0^1@2$d@2$3^b@2$2^7^6@2$b^b^5@3$8@1$7@1$1@1$0#8@1^b^2@2$f@1$1@1$0#8@2$h7@1$0#8Z").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "#$Acp'0h01xi001xh13HKKh21Hh32H0h42Hch54__x1h64__x2h74__x3h84__p1h91ai011ah:2HKh;2Hbh<8RES_len0h=7__arithh>4__ffh?6__sat5h@!s/%6hA!s/%7hB8__varmaphC5__withD4cstrhE5cstr0hF4__x4hG4__x5hH1ni021nhI7!sh$10hJ!sr%8hK!s/%9hL2HahM4HinshN3HnhhO3HzlhP4__x6hQ2n0i032n0hR2zbi042zbhS2b0hT1ei051ehU1ki061khV1mi071mhW2zki082zkhX2zni092znhY1AhZ3Hzkh[2I1h\2I2h]1Ph^!tZ%2h_!s/%3h`!s/%4ha4__x7hb4__x8hc2b1hd2b2he2hii0:2hihf1ihg1lhh2loi0;2lohi1oi0<1ohj4CONThk1Ehl2F1hm2F2hn2F3ho2F4hp2H1hq2HAhr3Hflhs2Hxht2Hzhu2IHhv1Khw1Mhx2a1i0=2a1hy2a2i0>2a2hz5allknh{1bi0?1bh|1ci0@1ch}2k0i0A2k0h~2n1i0B!s+$C2n2i0D2nhi0E3offi0F1vi0G1wi0H1yi0I1zi0J2zli0K6a_basei0L5a_!sS$M2k1i0N1sp%0p&0p;1p;4p;5p;2p;3p;6p;<p;7p;8g005`j1>Tg006Ek109!s0$cj1VTg002HR0j1wTg00F8j1sTg00eBj4YTg07o<j5=Tg05h?j2;Tg06DYj25Tg00=\j1kTg00@7k200Tg009fj2BTg00DXj2!t4$?Qj2bTg00Uok206Tg0042j30k108Tg00EXj1~Tg00BDj6ok70;Tg00NZj2iTg01:?j3MTg000Gj3N!t1$KR1j2<Tg080Ck40JTg04Ehj3nj4:Tg05jTj2fTg06Ehj26Tg070Tj3vTg00>Wj21Tg00XAj23Tg00<6k20kTg042Hk10gTg02Mak20`Tg07^Fk10\Tg02>GR2j1mTg04G:k20X!s0$]k30WTg008Oj2cTg02?bm<0UTg02@Gk40TTg02OQk107Tg0472k10STg01VUk204!v[$Tk20!tZ$g^j1O!v[$0k202!v<$4k301Tg0488k10RTg01L:j1`!s/$Yj2_Tg01Mkj2j!x,$Xk10QTg00G6k10P!s0$Tk10!s}$H?j2|!t|$ij1{Tg00m@j2zTg00J0k20!v}$JRk20!w8$K>k30L!s0$]k40I!si$bk30GTg056lk30FTg00:Pj2]Tg01K4k10E!uT$2j3xTg00IEj4dTg01NWk20DTg013_k60CTg00M6j4uTg05>`k70ATg050lj2@Tg04ofj2?!xR$gj7LTg0821k30@Tg07l]j2gTg011Ej2PTg01blk30?Tg07mhk30>Tg014=k20KTg053Dk80!{&$22k80<Tg06BHj1}Tg06CQk105Tg083<m<0:Tg084Rk30VTg085]k20jTg086hk20iTg04BAk30hTg05iIk20!z%$@\k40cTg0883k30bTg089>k20!wf$<;k60^!wp$Bk30]Tg00lbk20[Tg01^;j4qTg001dj7rTg01h3k60Z!wg$ck70aTg00nGj8l!sU$Yk30YTg01;=k20dTg007Fk20eTg00aRR3f0R4g00b2R530p=2f2R6f1R7/64'1p=81367/<4p=Qg00\8R8f3R9'3!s=&'<p=Af5R:f4R;'31674,16,99'<p=J1384p=71974,<6p=t1;74,56p=41174,36p=a1167/34p=Fg00X]R<?074p=[B0]<74p=Z20[<4p=UP<P6P7P4Cqp=XP<P;P9!s9,Cqp=S1z<4p=HP6g001ER=g00_KR>P>g00_kR?P<P7g017NR@P4Cdg00a2RAFrp=CP7P=P>P>P?P4J0Zp=hP6!s8+7P4K0ap=RP9!s:+!tF$Glp=^P:!s;+;!s0+<P9P@P6CdPAFr!sQ'K1<!v$%>0HB0Y!uU$E138!w#%T!tR/P!te$\!u$%0`KP4Cdp=ef6RA!sK+:!uy$!t_2Glp>0B1g961P74+0dp=D!w%$P4p=GA0374p=W!wE$P6p=y20e74,B6p=Ig01<]R=9034p=pg00\Vg00]^R@#>RB#>RC#>RD#>#>#>RE$09RF#VRG&09DRD#VRH#wRI[g015\RJ#sS00Q00g00YgRKp,4SEGSRLPAP:P;CYPLf7RMPA!s2$JQ00PLf9RNf8ROP4CYPOP7!sQ%D=#2f;RP1;MARQ'5RRA8RP:%kBRR%kERS+00RTf<RU1;OMRV'5RW1BF4RXA8WUARY,9X3QPUP7O11bD8-06HRH50I[^0GCARD[]:WUPLPOPM%~JRZCYPMPZ!v|%D=#2P3POPZ!t['P3p-0RZP4g00c1S01g00^CR[n0110?00020000XT3S02g00cNS03P5P4EoQ011iD4b3W2W:!ug%:RDPN!ue$NP7PMPAP:!t@$WPYPTf=RY1;NORW'5R\PXPXP\PYPMEJPYP7O1=0IH!u:%[]:PLPPPDAMJ67CY!s/$96POPMPAD=#2g07U<p4p710R\PZ\4R]%s6R^P1AM9749N96P9P6O1AN;97'<[R_P6P7O1AN964'<AM;679N;9R`[P;P9O1AN:;6'<\`P9!z8%H0JP7n20010!s#$1!u~$000WgX97W]WYP_^g^^97^]]^Y\P4PJf>R\=nLYR]!w4$6O5PL!uZ$:C:ANJ];'<P1PLf?R]P\PAC:AnL]\=NJ:f@R^1;UPS04'5R_A8_^DPTfAR_1;YUS05'5R`!vQ$`P_PPEJP_!vQ1P4PLP_P^POC:fBR`=nL_=NJOPLfFRafERb1;67/f4S06C:S07P1fGRc1;96S0816c73v%74RdfHRe/66S097t4PefIRf1;:;Rg'5Rh/17,bF!tF'f<A4e;9S0:fDRifCRj54eS0;'3A4fbiS0<?8fjS0=16f9Rk7ahfJRh?4abRlA8lhiS0>PTfKRm1;caRn'5RoA8ombS0?,9X7QXPm!y/2[P4Avfgk16m:9td4PmfLRd/5VRV!tj315mQ/3oA4decS0@?8daS0A16dA7aVfMRV/5WRW#7S0B19WT16VMRQ#7AFWQTA4VfeRQA8QVcPTfNRQ1;hfS0C'5RW!wM$WPQPeEJPQ!to1Q0BA4QDN/9TfORW/6N#7fPRkQ04'516kD;FTfQRg?4VdRp#716gm=FpTRpfRRq?4QVRr!t-$rPqPdEJS0DPq!t1/Rr'<g00bRRs20kGG&0gL+0`Rtp,1ARu$0\Rv30%mtRw%mvRx'[RyPsP<&08sP2&08<%m7%m4'[A0s7420X7440WZ0HsX0sPtPw1c<wPvPx1c<xN<0Up,7!#N_%H0TS0EPy&07tS0F%7wS0G&07vS0H%7xS0I&0SuRx%>E!#6S$!s$$kRE+04S0J%7x%7ERv203xERw#7[[S0K%OBS0L#OS0M#O#O#kRt-02RS0N198RR2%7t200RtRz,98[[S0O%7RR{B01Rt7V[WLS0P%7z\[^L{S0Q202RSS0R%7S198T[\2S0SB01RS7V[XL{S0T%7T!sT&U&0RuRu004ES0V%7u203uERE#7\v[S0Wg00^_Rvg01aaR{#`#`R[#`S0X,_<S0Y1_<[1_<{S0Z'ZS0['ZS0\g01b@S0]'j%~vR{3MR[%svS0^%U6S0_P7%U9S0`&0Q<RS7X9P9PSDS&0P<R2&0O<RzPz1|<8Rt%OC#HR|%{>R>PzPzP|1z<@R}P>Pz%HBRB9CztS0a1hz:5RzP>ACzt}C^EKEK20Nz?S0bP4P61c3520M46#2dB0L<87H0IR?b>bBbCX5<X6<X7<X8Z%761397%79R~/<:P~[[[^5<^6<^7<^8ZP4A0<w8A0<E8g055i,3u40HS0cf[Ru/5nRnPxfWREfVR854uRwPYP]p,7HULL_okS0dO7b=b?b@bAbJbKbIbEbDb<PpPrQ0EPyQ0FQ0GQ0HQ0IQ0JQ0KQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WP[Q0^PSP6%U:S0eP:PSDSP7%U;S0f?X:S!v|%P2PzPzQ0L#>#HR[,E|R|1|<R>0G<FRRP!v}$1E}BRrP|!v}$O@S0g#HR@9Czt1hzM!w#'rR!w#%Q0bP!va4F<XG<X8ZAF9;TR|1176S0h11;:S0i'31T;MP|!vs0F<^G!vy%Q0c16ubPnPxfURn,6uPwPDP\Q0dO9!vS7Q0Dg05A3Rw%V4R|%V7RpP1%V6?0741B961B97'[R~[1B671B64'[%V9?067[S0j%V;?096\~B0F674P4!#;27dWcWHQ0j^dp^c|^HwP4PFfTRw1;^]S0j'5R|1BF6Rp/]|S0k'1R|,bFS0lP6P<P|1BF9,[4Z0I<&0E6S0m19pT,TpS0n!x`Y{Q0^Q0_?X7SS0oP2P<Ax<B},E}Rpg016gPBCd,\z!wg41]74,14/[7!wE%P41BFYS0pf_R~?4mhS0qO2!w07b3Q0l,BFQ0mQ!u,aoP2PzQ0a1eBR,\z!}l+p1ep!s7&C^!u0597T,T71]67,17Rp19pT'T!y\&P4Q0pQ0qPDO3!u39-0D|J0CO4b3fSR|1;]\S0q'5Rp1BF7/]p'1,bF=0G7PGQ0lPwP4!#9f$X0GPNQ0k!uhXQ0X#`Rp#`,_<Q0['ZQ0]'j1_<pS0[Q0YQ0Z'Z!s<&=Mv{5Mv!vA$fP6Q0ePA!~$%PSP9%UA?XA!}}&ACz[}Q0M#H,E[Rp,e}!vf'Pz1EB@9Czp!~-%PBP[!~&$HCS0M!}~&O!w9%x<}BRC!s:$eC@!w?'EKK0B!~7>P<X8ZQ0i,949Q;411699F:A139A1TAN1];:RC19CA'T[!~D6P!~G+f^RCfXR['6S0ZfZRpfYRR54CS0YPx16CeQ0C,5C1BFUPPP_P`Q0dO;!xL7O2P6P4Eob3WsX0GCuCuWoWnWmWlP9K0AW\W[WtWrP7P4O2!~A0!s/&W3XXKXW<XRKQ07Q08,5cA4cj`S08'3Q0;?8e`S0BQ0:Q093aQ0<Q0=PTQ0>,9X9QlXPh!#C'2[^XK^W<^RKPJPLPbPiP4C:PJP3P7PcP]!s8$jD=S07g08:IRl!s@$3!s$&aP7P4PbCDP0P<P31@ei!s0&?f91164S0>9Gc7P=n101!u>%21010J00!s:4D!s:$!um'20000P5!t5$ePa!tW$7P4P6FLP5PeP^!s:%D=S0!s[2!s441!s7$120104108Q07PaP\PiPjP`D=RiPiQ07PiQ0=!s-$!sX$A000:30!tp$G10F2!s1%9!s9&310M2010;10:201051073!s-%!s9'11034010=10B10>10C!sb,@!sG'#2Q08Q08?8c_PTQ0;Q0B!#Gw%e!wr1]2]1PPPLPhPfB0@674C:PfP_PcPaPbD=#2P_PNP4O2W2S0;W1Z0FKZ0GsX9l!#M>$O3PlPLPfPe1f!sd$lP3P6!x:+e!v}$c!x:,ha!x:'m;Q0>9Gf!x6chPe!t}$7P4P9!x6$hP`!s:%D!x3R#2PoQ0?PTQ0@Q0A!vR&d!vR5^HKP4PLPdPmQ06C:!uf+fP9P6Pe!uf,mc!uf'd611;49Gh!ugcmPf!uU$9P6P7!ug$mPj!s:%D=S06!uj?#2!vR&;P9Pf!tu,de!tu'V911:49Gm!tu]31c34S0@!t|&:P;Ph!t9,Vf!t9'Q;11A49Gd!t9\/W4!w?&VPMPAPd!t5,Wm!t5'kA11O49GQ!t5d7!wH&kPQPVPd!#W7$FLS0AP5PkPe!s=%!z4A#2A4|WQRoA8o|VPTA4wkWRoPXPXPoPwPQEJPw!z044!#5v%dPAP:Pm!u],Qh!u]'W:11M49GV!u]\S0?#2A0355S0>PQ!uU$VCDP3Q0@PWPNPOPQCD!v'%gPPPDPk!s5'3P7!t`'wk!t`'nP11Y49G|!t`\#2A4E|qS0BQ0B?8EgS08PTA4[w|!v_$[qS0=!}]&[!vS1S0<]4];P7PkPDPNPWCDS0:#2!tu'|W!tu'wD11U49Gq!tuL#21gqURb1PPgRi<0?7%2b%2i'<P11g|Y#21PUq!#3T$=PTA4RnwS0=PXPXQ0=PRP|EJPR!t~39P41gn]#21P]n#2B0>E_7A0KE_PKP[PLf]Rof\RY1;4`/f_C:Q0Y!#B$%1PTA4~upRi!y^$iP~PREJP~!y^21XRKPLPYPu1;[_/f^C:P11P74#21367[R[13741P67#2Ri[1396\i20K74!#^J8XV<XH<S0YP[^V<^H<S0ZP4PjPRP9O313jR1@oR%w<R[1c[4S0D1@Cp=0[4P0P<f`Ri/@Y!s5'!yZ,fb/?eS0C11h4S0X9Gi!w`NfdRY?4i~RbA8bYCPTfeRbfaS0k;4iS0l!wK%lPbP~EJPb!wK3l]4]NP7Q0k/@o206<4S0k50[!th%Q0CQ!t_$6!t_7#2fc/?fP[Q0D1?Yh!u_+fRi/?d!u_/11bMS0D?yW4!sp:jR0?4ibS0XQ0X?80YPTfkRTfgRY!u?$X!u?%XPTPbEJPT!u?1RG]4]OP71?YVQ!u7$Q!t<$7#2!yI%P411YNRH11g9RIP7O313HIPLfmRIflRHPTPYPDPiPNL0=AIFIY/3DPLfnRiPIPHPqP:PYP;L0<AIFiq,3:PuPTPwP|P`!#O@_Q0`7X7!#Ta$PBP@P>1E}@9Czr!#S|81376Q0h?a79!#HA+P4ftS0hPCfyRifu5IFRYPhO4b=b^b_b`!#Gp%EbDb<foRH1;TwRI#}5IF&05I'1RX1;T0RT#}9IFH&05T'1R0'3e15HIRI15HTRT'3e!#M2Y[Q0\!#Lk,!#Lh&PSPA%UMDSP7Q0eP9%UO9XSO!#Wh+g#OR2#O#HRSQ0L#HR{!#L[%@%>2#HR2!#Wr&B2Q0M/ESP>!s]%>#H!#Lq%D5RzP>1Er@Q0M,E}/E{5Cz!#W|$!#W~?P<Xa<Xb<X8Z13M;139M11:N9F9O1TOPQ0i11;M/1O7FA!#Ln9a<^b!#Lt'P^PaPxAIFioPCfs9IFiQ0h!z4$PPUQ0dO=!wu8iRY9IFHAIFH|,1X5F0e16HYA8IH|5FTeO6bpb3b4b3W4WOZ0J<P4O11?bm%{<Rb50[A03=5RTP3P=Q02Q!#o7&R=Q011iG!s`&!}L%<!}L$110I00P4P6O2bObiW4WNZ0D!t$%@~u=0[bP=Q01Q0l/i4b3X4TWN!sh8PO2bNbibZb3W1P`P4P]K0;b;WZW;!#Ne<b;W4W;Q0:#p!t6&<!t6+;!#qb,1!t2$9O2b;bSW2W4Q0?#pP3P3PWPVPdPm!#qM$FLP5PWPc!s:%!#@@2#2Q0A!#>5$gPWPQPVPNPOPMFL!#>+$|PgPkPWPPPDPN!s;'!#AU$wPdPqPgPk!sz7<]2]MP7Pq!sd$QPDPNPOFLRO#2Q0>PLP8PnPw!sf%PU!t,$WP7N<0:Q04,58RUA48qgRq168kA8U8D5Fq3QP1Q05,5ER1Q0B'3Q0816EP7a1Q09P4Q0q,5RQ0='3A4p8n16pwQ0j,5p?8p\3FPcP_P^P]P\!wE$6W\W[!wO6!s-%0b3W2WM%pOP|Pm!u}%D=#2PmPj!#M=$WM!wU46O2bM!wU%!sB01!sB&4!sB$1!#T7'!tL&0110N!xs%10K10LX9l!sA%!#No&V674C:Q0;W1X}sXQK!#NU-LPePc20j!sI%7#2P]PM!tr%R]W1Xe<Xh<!sv+!sR$i74C:P]W1XV<XTK!t;1h!t;-!sb$XTK!t;3f!sg+!tZ%!sg'dPm!#vW+cC:Q06#2PjPP!vR&1Z0CKXylX~KXxl!sQ'O4!tJ'b!tJ-|<!u_9_!tJ7!vc$601!#S}01!s1$2!s9&2106!#S}D2!#S}72!#S}+2P6PMO2bjW:W1!~$>:!yY$:WuWUXvJP:P4J0^W:WqXHKZ0E<W{WUWzWwWko"). Qed.

(* [comment removed for export] *)
Lemma kentry_keep_foot : ltac2:(zQ "h10!jb!hn8!h9!u4!ij5!j6!np0!np7!r7!nq4!j0!nqc!hj6!hta!jkc!hl4!hla>1E$c>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>2M'>1x@1$1@1$0#k0@1$3@1$1@1$0#8>1K$d>0@4$7?4SEGS^4^3^1>0>1x@1$1@1$0#k0>0M3\1x@1$3@2$4$2$2P@2$b^6^3\1p@2$4$2$2M4\1p@2$4$2$2P^1\1s$2\1l$2@2$a@2$f^2@2$8@1$0#k0^4@2$h0@2$8@1$0#k0^4@2$e^2^1$9@3$5@1$3@1$1@1$0#8@1^5^2@1^6^2>0>1x@1$1@1$0#k0>0@3$5@1$3@1$1@1$0#8@1^6^1@1$6@1$1@1$0#8@3$5@1$3@1$1@1$0#8@1^6^2@1$6@1$1@1$0#8@4$7?4SEGS^7^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "#$c:p'0h01xi001xh11ih24__x1h34__x2h42HKh53Hinh64__x3h78RES_len0h87__arithh96__sat5h:4cstrh;5cstr0h<4__p1h=!sE%6h>!s/%7h?4__x4h@7!s6$10hA!s@%8hB!s/%9hC4__ffhD8__varmaphE5__withF!t+$1hG4__x5hH1zhI4Hdm0hJ1ki011khK1mi021mhL3HflhM1ai031ahN1bi041bhO1ni051nhP1ohQ2F1hR2F2hS2F3hT2F4hU1HhV2HihW3Hx0hX1dhY2nnhZ2Hah[3Hdmh\2Hxh]2Hzh^4__x6h_1yh`3Hw0ha4__p2hb!uC%2hc!s/%3hd!s/%4he1ei061ehf1vi071vhg1wi081whh1Ehi2H0hj2HAhk2HBhl2HChm3Hd0hn4Hlenho5Hnonehp3Hrdhq2Hshr2Hwhs1Kht1Mhu2M'hv2a1i092a1hw2a2i0:2a2hx1ci0;1chy2fchz3ihih{3iloh|2kbh}2m'h~2n1i0<!s+$=2n2i0>3rhii0?3rloi0@6a_basei0A5a_offi0B2hii0C1li0D2loi0E1pi0F1si0G3segp%0p%1p&0p;1p;4p;2p;3p;<p;6p;7p;8p;Bg005`j1VTg006Ek10C!s0$ck10:Tg002HR0k10QTg04Ehj43Tg00<6R1k20ETg08;Sj2?Tg009fj2BTg00>WR2j20Tg00DXR3j28Tg0042j32k10STg008ik10RTg0821j3uTg05h?j2=Tg01L:R4j1CTg03YSR5j2vTg02>GR6j16Tg070Tj3FTg00F8k10DTg08<^j2hTg08=gj4`Tg007Fk201Tg08>gk20!t\$Uoj2[!ty$KS00j25Tg06DYj29Tg00=\j1\Tg00@7k20<Tg00XAR7j27Tg02@Gj4RTg042Hk10UTg02Maj2gTg07^Fk10TTg04G:k20q!s0$]k30pTg02?bl<sTg02OQj1!vf$72k10hTg01VUk20L!tC$Tk20ITg00g^j1a!v[$0k20KTg00E4k30JTg0488k10c!s:$Xk10bTg00lbj2j!v-$Xk10!sa$G6k10!u~$GTk10_Tg00m@k20!vV$H?k202!s0$bk30^Tg00J0k20]!wb$Ok20!x7$JRk20!v1$K>k30Z!s0$]k40YTg08?ok40!xh$BDj6~Tg08A>k70XTg00M6j4ITg034Mj6}Tg05jTj2wTg06Ehj24Tg00?Qj2D!x`$Yk20!xj$NWj2]Tg013_j6_Tg05>`j7cTg084Rj3nTg08BBj2WTg02;Nk10;Tg08CGj4mTg085]k209Tg086hk20GTg04BAk30HTg05iIj2r!wY$Dj1xTg072ak40VTg02cnj4|!s/$Ej6zTg073Dk30ATg074Hk10WTg075Jk10tTg076Ik10!xE$fNk10rTg00:Pk20OTg077Gk10@!s0$ek20P!ts$ck80oTg078lk30mTg079ik60jTg06@\k40MTg0883j3tTg089>j2pTg01^;k405Tg01h3k60i!s:$Yk30gTg00IEk406Tg001dk70!}W$mck70!w'$nGj8yTg01MBk30f!s0$kk20eTg01:?k30kTg071ak40lTg02Edm<0NTg07QcmB0dTg00kAk10nTf0R8#V#Vp=ef2R9f1R:'7/58p=Xf3R;1[:8729p=M109:/78p=:g00\8R<!s3$1g00X]R=00B8p=;g00bRR>P=P5P6P7g04UBf5R5f4R?P;P9P:P8M<sp>08P=!s5%H05p=JP:g001ER@g00_KRAPAg00_kRBP8J0ip=i20F=8p=UB0g=:8p=>P9P@PAPAPBP=P:g017NP8H06g00a2RCK03p=<!sK-:P8K04p=qP5!s:+?!s0+;P9K04P:P8Gyp=Yg00aRS01g00b2S02728p>0[P=P!u=+E_p=T17?;10:8,89'5p=E18:8,59p=A!tc%0`KRD!te$p=fP;!t=+9P:!s2+8PCK03!tj$d!sI28Gyp>0>!t0$D9p=@!uk1P!t%%!sf$p=o20==8p=^B0f!vA$Hg01b@-0e8p=Sg00^_RC@0k:8p=Nf6RD!sq+5!uL$!tG2Gyp=G1=:8,99p=OP=!us'H05!w~+LQ01!v/'H0lQ0232p=K199:/08p>07P>P>!sb$4P6P6P;g07SP!sW%N<0Np=l!sF&=!sF$5!w#,!sE%b!sC&!s$%2P8P:P9P2P;P?P5PDf7R2f8R4f9R@NB0dp=Z!sO$7P2P7PD!sv/M<sp=k!sD$3P2P3!sD6{A29:8$0np=Pg00\Vg00]^S03#VR3#VS04#VR7#V#eRE$0CRF$0:RG&0C7RH$0:RI$0QRJ[PJ^0Gg015\RKp,4SEGSRL!t7$8C3P020E==RMp-0RN1?59P1!tc$NP81BF;S05Q0510:8S06'85X:n200110E00012010F10CR1g00c1ROn101100000210!sK$P?P:O1P5P:O1RP52J[^0GP5P8O1&0RIRQ52JA2JPQ!s>$KPLP2PD!th%PMPN1?@9P1P!t#74!t#$@P:O1!s}'LP@P2P9C3]5]4P;g08:IRKPKg00YgRPPLf=RRf<RSAu9:!t2+f?RTAu?;9RU'?!t;9f>RVP:O1S07PT!s/%852JS09!tF&TPRPU!tF%]f^g>P8PLf@RUPT1=;9S0:?u!t?-BRW1=5?RX?u;9S0;!tE<ARY!u\$W!u\&S0<[!x<%aaS0=#C#CS0>#CS0?#CS0@#CS0A#CS0B#CS0C#CRZ,v;S0D%6;9FWXR[&0DIR\$0QR]PLPY1hWXR^P;C`201W9-00;,[\R_32Q0DPLPUP!sC$=2]_,5['5Q0DfCR[1=D5S0E%6?S0F3FP]PLP[fDR_1=2DS0G'hP5C`P\201_?-005CM1vDZfER^1=42R`%6DS0H3FRaPLP[1h^`RbPD!tT$^5-00D,[\S0I52]R\'5P9PaP\P:!t6$_P!sP$PLP_fFR\1=@4S0J'hS0KP2!ty$8X!sO$DP[P_Pb19^`S0L%62S0M%\3R]%\ERa+0<Rc5:8XH=Q00Q0L#1Q0L/8cQ0H!s1$Q0H;:c'5'5Q0J,9\S0NQ0M;:cP:fGRdf:Re/=@Rf'9Rg#1S0OfHRhf;Ri/=eS0P'9S0Q/8cS0R%6@Rj#1Q0Q?:j!sx$1veZ%6eRk%\7R7'7RlPePk%;kPZP7%;7S0SJ08PDCRPl20EGG&0UL'gRlp,1ARk$0TRm52>%6lRn%6mRo52=RpP>P=&0S>P6&0S=%6:S0T%68S0U52=A2>:820q:840pX_>X0>PlPn%;nPmPo%;oM<sp,7!#Op%CRR6Pp%QlRl%1nRn%QR%6R#1%QmRm%1oRo&0hkRq%eE#e#e#\RE+0LRr%1q%1ERs20IqES0V#1[[Rt%a3S0W#aS0X#a#a#\Ru-0K]Rv18<]Rw%1u20<]uRx,8<[[Ry%1]Rzg00^CR{B0J]u:UWZRu%1x\{^ZzRx20K]aR|%1a18<c[\wRwB0J]a:V{XZzRa%1c!sP%z&0ckRk00LER{%1k20IkES0Y#1\s[Rs&0bCS0Z&0DCS0[1j=9S0\&0a=RC7J:&0`=S0]&0_=REPE1iE?1iE5Q03-0F=R}%U3R3'>R~202=]>0^=FS0^5<ER]5qE&0RARAP]EY20]EBS0_P8P9Q01Q02+0BS0220\89$0[dB0Z=<:H0YS0`bCbDbEX2=X3=X<NXaN108:S0a/7c,5;,5910:9S0b/7c[^2=^3=^<N^aNP8%6\RB#1fUS0c1=hdS0d'9R]/8cPBP]PSO5b8bbbcbdb9b=b>bFb;b:b7b`WiWUP:P8O2n200!#43$012!s/'BFbP^P`Q0HP:H0?DTQ0K,BFRb1BF8S0KQ0KPbQ0MDEP5P:P=1hdf,BF1BF9Rb,78S0e108j7AbXH=P8PgPdPf%64S0fP;H0?E~Pg1BF:R]P]PgQ0fDE1v@Z17j7RBP@Pj%;jPZP7Q!{}%5CRPBP6Pp!{#$QS%6S#1PmPoPrPtPvPyPuPxP{PsQ0ZQ0[Q0\1j=;S0S7J:S0gQ0]PEPEA<E}3PEQ03#aS0h#URB,>}S0i,f3CdS0jPAQ0jH0>Q0_Q!w^26=P8P:P:P8P9DE10:;S0k,899X:9!w['6=P8%6[1BFSfRS0l1=^_S0m'9PeO4!wO-!wK+b\O2W\X0GK0XQ0IP8E~CICIWpWLWrP:E}PLPWPUQ0;C3eW5W4XfPXg>XJ=XNP!x+&0110F!x&%10@10AWM!#?8$O3PKPLPiPe1w!#:$+1w;9R7,?R!#<R9S!#;2$;PR!s/%D52JS0I!#;;%RPiP7!#;;$^OPP8PLPVPR1=9:S0n/w!t4,=?;S0o/w9S0p,?U!t;9Q08PU!#;-'8[^0GQ00Q0o14U95FUS0q%18R714Y;RZ7A8S0rPYQ0E,9W=@F!tn$s1DH<S0t,[IRj52J[^1=AFYXZS0u14W?RZ9A78S0vPYQ0G,9[!s_'w=2Jj[^1='5P:Q0E=FWZS0x14_DS0y!s[%zP_Q0J,9^S0{!s^'|!s^'Q0y9F_`S0}14^2!sW%~P_19\fRf!sT&10=2JjRZ[^1=P:Q0~%1fS1118fcS1214\4S13#1S14Q13=:fcS15PZQ11Q0P,9dS0P/8cS1614he#1S17fIRZ1=RSS18'9S1914ZiS1:;:cS1;PJPZfJS1<1=VRS1='9S1>/05S1?,DFS1@O1S1AA2J8jXPJ!#EV$O2S1BPhQ!sC%CPeQ1@Q1?fKS1D1=TVS1E'9RjP8P8PjQ1D/4RS1FDEXH=!}F'!}>4|PwPaPz!}F/!}9'202=<Rj=<E3S0gAoE3BPA!}P%~PEQ0i,f~CdEY!}88S0i%1:Rf?A:9Q0b!s%$k'85X:!}8,S0kP8fTS1G/4\S1HPTQ1GQ0d'9S0dPV!}>$!#5a$AbBb@!}@%Q1@,BFQ1?!uII@#^S0@Q0?#^S0?Q0=-0==S1@'HS1I'H#SQ0A#^S0AQ0>#^Q!s?$0>!s?%Z'N'NS1J!#4T'?S1K?J?CS1L?J;C7J:!vI$Q04#a#US0\,>}Q0^5<ES1M!vJ&j}S1NPAPEPE!vy$\9oE3!s6%A<EjBS1O1iED!sT'!vx$^!vx$S1PEYS1QEYFG!w&8X?=X<NS1RA:8;c%1;S1S?A;5%15S1T/52S1U10?5S1V#1Q1V;Ac[[\f!wG,^?=^<NS1VP8Q0V=2=<Q0Y=2=<g055i,7k'5'5S0YQ1HPqPTQ0dPePRPVp,7HULL_okS0VO9!wm7']DTO2S1?E_WTWSWRWQP;FcWVX1=CIW]WL!#:p<PLPUPVQ0p!#6H&YP!#6E@XMK!sA%PKPLPRPSAn!#J`,An?;9Rk,?T!#51:!#JF-k!#61%J>!#64&UPTQ0:?n!sx/X;!#6+$W!sy;<[^0G14W;Rk9FWXS1W1WW9,gI#6=2=kRk14[?S1X9A78S1YP[Q0G,9_=@F:S1ZO1S1[PI&0;:S1\1W_?Q0tCm,[IR<!#67%Q1WQ1YPWQ1ZO1=2J<[^1=,5k'5Q1W1W[;!t:$Q1X52=14^DRk9A78PJP^Q0N!#5I$PIPIQ1\1W\D!t,$CM!#78$^`k1W^5!t{+S0N14\2S1!#7F$1]PJP^A@Fg:S1^!sm-d2!sm&Rk[^1=R<'5P9Q0NP<P:Q1]Q0O18gc14d4S0N#1Q0N=:gcPkQ0OQ0R14Ze#1Q1<Q18'9Q1</4iS18;:cPJ!s<$DQ!#5}$=/05Rk,DFRgO1PJP8PI!vI$DfLR</WSS1\!tV&XPJQ1BPZPgO1P@PgPkQ1E,9<S1EP8P8Q1E14<R!#5w'Q1\,gIS1\#QS0tQ1\#6#1S1\!#3lDiQ0kP8fVS1_/4dS1`PUQ1_?OZhS1_PT!#4x3!#?<%1BFg!tG$!t<$!t5D1JQ0[PCP9Q1LP:Q0SDL!#4-%W#V#URg,>}S0W!#40&LPAPEQ!#4',AoE3gPAQ!#3YCQ!~p%YQ1`Pq!uA$PiPVPTQ!~L6!uA&,]kDTO2!~L-?!~L+!~N$nWL!#A\-!~:+|>!~=H!#A]&LPeP@20!~=-209!}C&S!}C9PiP:O1Q0;52JS0;[^0GQ1S179cS0O188;9X?8RkPR1DF:R}!|\$Q!|q%SQ0OPSP!s:&\k^1='5'5!se$;c18859XD8PT!sH'S0O[^1=%1DS1Q175cS1J188D9X28RkQ!sD%S0O!|#$1JQ0OP:PiP}!uU&2O2XVk!vR'lWkWj!vR&SPe!vR-z=X{=!sX%!v/'G!v//G!#5F$!v-:Q!uz%P:!s~%Pk!s}'K=XeP!s}+SPiB0H!w/-B0H!#6G%V!t#;DQ07!#[5&:PLPVPS!t,+Z0>=Z0?!t2$!#Fs2r!t4,1r!t2%R!t2;!#F^-k!#F^3Q0n/r!ss+Q0o/r9S0D!#FV>!#FJ'qQ0T,09Rk14[5'7PLP[19_`=@F;P9CK[\f^K>^X=Q0uQ0y,7kPLP[Q0{!sG4!#E}$xQ13!sK%\Q0P!sl6}14d@,7kS0PPLP\1=SiS13,9h=@F;Rk!sT0P:Q0P!#ba+O4PLPdP!sJ$Q19#1S0{Q19/8cQ1:#1Q1;PLPdQ19=@F?P;CKQ0{Q1>!sF$F#11=UTS1F,9<14<V;:cP>Q0UfNRk/4U5:@PLPkfOS1>?O[W=@FeP:CK!s;$PS19?O_[=@FiR`P9CK]U][P2Q0=#6fMS1:/4T5:4PLQ1:AOkWY=@F@Q0=CKQ02WUW[%C8#6Q1>/4Y5:ePLQ1>P`%C!t/$%C9S02Q1>fQS0=Q0m<07SR`,DFS0mP`%C;#6S0y=:8cXH=Q02#6S0T,0`S07/7c%69S0;Q03#\Rk'0S03!sA$p/7cP8X0=R}17:8#xX_=X0=S0OQ07Q0pP}!s$$=P=g07VSQ06H0V#;XK=XO=S06P`P`%;`Q0TQ03P}P}Q0U#;X0>S0UQ02Q03108k!sx$pP9Q0;Q0;#;ClS07EbM:ZPcPc%;cS1JGk!yy$!#:A$=/4[S0t'7Q03Q0t5:SS03P}Q0OQ1\P}Q0pQ0;O1S!s'$1\,0S!tw%Q06PSPS%;SQ0T!sQ$!t`$!tX$;Q!tB&Q0t!s%%#;GkP:CRS0tQ03P6Pp%Q?S07Q0F#1S0;!#:{D?Q!#G7$S0?Q0Z'NS02Q0[Q1KP91j=5S1\?J5CS0T!#:2-202=kS1a,>BS1b,>3=<Eg!#:/$L!#:/&4#US049<EjS1L1iE2S1cPAQ1b,>~!#:c$!#:F?G=X<NS0^109k=::?10:5S1b/7cQ1U10;?105kS1d;:c[[!#Fs0G!#Fv$UP8Q0Yf]S1eQ1>'4S1>Pq%6VS1fPhQ1eQ0=Q193OS1ePiPU!#;E=bIC|Q0m,BFQ!w-+!ys$!v~IB#^Q0AQ0@Q1@'H'H'HS1@!#KI+0?!#>7&!w'$1KP5PCP;PCDLS0T!w8&A<EjgS0B!w'%a,>g,>3Q0\5<E!s9%M!#>N,Q0!wS&OQ1c5qEPAQ1PFGFGS1c!w9C%1?S0;Q1d=:9?A:95cQ1SQ1T%12/5e10D2S07#1Q07;Ac[!s#$!wC7S!#?I%fQ1>Pq!w6$P@PiPUP[P\Q0VO<!w1;,]`DTQ0l?O\^=@FR,BFR^Q!#^#$^Q0yDEP=fSS0y1=d\<07VS0K,DF!sM&e%C5S1e#6R`,08!#^4&!se%17^]S0e%C?S1>#6S1f,0^S07,8]S03'5Q0eQ0F/0k,0^7A]!|b$e!}u$e!}g&FO1S03O1S0m!sa$=,8]Q0e#xP}18!#4&-eP]P]%;]!y<$=!~8,^P^%;^Q1fQ0m!~8'1>!t2$pP?Q0FQ0F#;Cl!~D$G{EzP8CRQ0t10T`S0tQ1H'7%65R^/0kS0FQ1H5:T!#3_'0t!tv$P^O1S0tO1S1>,0T!tL,TPT%;TP`Q1>!tK+e!{9$pP5!th$ClS0tEbS0mM:ZQ1H!s%%#;GkP?CR!#3i'2Q0M#1!{cH[Q1\9JC5P9PCP:Q!{7+Q0h#e#UR^9<Ej!{<+^!{<-Q!zkEQ!y~&%6Yf`RYQ0l'4PqQ1DQ1GQ0y5OY!z3$[P\PZ!z3@bW']E~Q0KP]P]Q0KQ1fDEPJQ0yP9O1S1fP0PIPJP81[I8S0KP0g014]S1SPJQ05>0ALkQ01PJ&0W8S1c&0t8S0h1BF?&0s8$0rS0T+0O$0@+0PPQn!#Ru&20000PQ!#@I1G00!s82400=PJQXPJPLQ0y!w~$d/0TR],DFS0dP]%CDS0?#6S0M,08S03/7cXH=10]`RY/7cQ0F,0]S1H/7c!yE$PYQ1H!y3,!zo%S0=P`Q0F!y6/FQ0t!zO$S0tPcPcQ1JGk17]bR^18bYS1J'5!zK%,8bS1e,5^S07P^Q1JP^Q1>!tE$9,8b%x^S1gP}Q0ePbPb%;bS1hPYQ19!tU0Q!tR$1>Q!zD$!{l'S0m!|\$M,0US1>Q0c/4dR`'7Q0H/0k=:U`S0=!{o%1>!}g&H!{k$O1S0O,0U!t4,UPU%;UQ0MQ0O!ua'0?!tB$pPDQ0HQ0H!}>+!#>`%GkP5CRS0HQ0=!{m%4S0pQ0f#1R`!{rE^Q!#:0&aS1UQ0y'4S0yPq%6WS0^P<Q1UQ0cQ1G3OS1UPiP_!#:0?bWC|Q0d,BFS0dQ!v:&!ti'Q0pP!taFC!#^R%#SQ02'N!#Q6'\?JDCS1\!#:+$DPCP;1j=D!s<$02DL!}y+X#US0X!}x+0XQ1a'>Rj!#::/PEA<E~g1>~j9o!#>e&!#:M81iE4S0g!#:Q-!#>cB^!~f%T10DkS1P=:9?109;S1OPDPDQ1O102kDEA:;DcQ0;Q1Q%14/5S1024S1O#1Q1O!#:h'!#:i3^=^<N!w|$Q0^1BFTS1TQ0yPq!wv$P@PiPSP_PdQ1<Q0VO>!wt=,]]RdDTP;P9P]Q05!s%$3'85X!#{M$FQ!|A-eQ!|5-Q!|2%HQ0tG{Ez!xZZZ!#C\&!#7,$!#CP&!wc%BPEQ04!x'$,>~,fBCdR~PAP~!#q9:X?=Q0aP9P9Q0a10;kDEQ0bP;P;Q0b10?kDE!vj0P8!{g$T!vU%!#ud$!{=?PdDTL0o!#6t$Q1fQ0KP0Q1SPJB0ALb!#6j$Q1cQ0h!vg$!#6ZfeQ0lP9O1P_P9!w'Z@!#Gs%Q0AQ!#hO&Z'N!|i$!wC$Q!|c$029JC;!wH&1>gj=<EB!#G^&W=<E3!s/$/>j,f3Cd!|2%!#D%%LQ!|-'0jFG!|&Hd=:?9Q1b!wu$1bQ1PDEQ1QQ1Q/5@P?P5P5P?PDDE!{hDP<PqQ0yQ1TQ1UPiPS!{^&;!x==O2E_Q0l>0mL9!w+$b\W\X0GJ0jWUW[X}>P8O1n01105!wz%1110!ta$O2!#\]'DFcbUW[XmfXK>XX=CIWq!#h3FD!#h3TLPVPR!$:%+M!#Vl&!$82&H0MR>!#VpBP:!tP%P>!#Xn'=PXwKX~PXvK!#U>,!#iI&t!#iI-t?;9R>!#iII>!#Xt%x=!#iI1t!sx/X;9RX!#iHBQ00!#hG%JQ1[PI1DH?!#g]$Q0EQ1X5F[14_5R?!#h;%[Q0L!#h;&1DH5!sR%!#Xn$G=F_?Q1]PJP\Q!#go$1DH2!su'JQ1Z5F\Q0N9A78R7!sM$0Q!st-4CMR4!#wU&Q#1R\Q0R14h@Rh!$1F%hcP4Q13,9Z/8cQ18#1Q1=Q1D/4S!#g~%DQ1E/05R5,DFRc!#gv&1DHR!#ge&Q1<PcO1PePcP5Q1:Q1F'9RHP8P8PHQ1:/4V!#vaM!#gP$Q1`PTQ1_!#u;:1BFc!svH1R!#f&0!s{$ePRPVQ!#qP:,]5!#f$-XQ\P;FcXV7!#qPHWPUPX!|B'y=!#f;O!#`}&p!z6,1p;9Re!#`}Ie!#`}7p!#`}/p9RN!#`|JrQ0s=P!#fk%0uQ0vQ0w!s7'!#`S&0zQ0|!sL,}Q0~Q10=PJQRG!z;'~Q11Q12Q14Q15PG!s4$6Q17Q1;PJQ1AAPJ8Q!ye'CQ!#ul]PN!#4^S!sA$1000:311031081072!s1%5!s9&51!s_%D10B201061023!s-%!s9$!sL&4010910<10:10=!sb,;!sG'P9P:O2WoW5W4WsWuWtWho"). Qed.

(* [comment removed for export] *)
Definition sh_iv (E : env) (k : list kentry) (p : expr * expr) : Z * Z :=
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in (estart E (SA sb sk), elenZ E sn).

(* [comment removed for export] *)
Lemma fold_unfill_inv : forall E M k gone acc K,
  know_ok SEGS E M k ->
  (forall K', In K' acc -> In K' k) ->
  In K (fold_left (fun kk p => let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in kn_unfill kk sb sk sn) gone acc) ->
  In K acc /\ (kimg_b K = true \/ forall p, In p gone -> kfoot_apart E K (fst (sh_iv E k p)) (snd (sh_iv E k p))).
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "##T:p'0h01pi001ph12K'h22kkh31Hh41Kh51xi011xh63Hinh71Ah83HK'h93Hshh:3acch;1lh<4goneh=1qh>2HKh?4Hacch@3HaphA4HimghB4Hin1hC5HkeephD5HresthE1PhF1fhG2p0i022p0hH1EhI5Hacc'hJ4Hin0hK2HqhL2IHhM1MhN2_HhO1ahP1bhQ1ei031ehR1khS2sbi042sbhT2ski052skhU2sni06!s+$71zp;1p;2p;4p;5p;3p;6g005`j1CTg006Ej1U!s/$cj1PTg002Hj1[Tg00F8j1HTg00<6R0j2GTg00eBj4ETg05\7j46Tg08Dkj4ATg08F4j5B!s/$Rj1;Tg0185j33Tg08GXj32Tg01==R1j25Tg009KR2j27Tg00EXj1^Tg01hWj3QTg00M6j4OTg01:?j3NTg008Oj2]Tg0042j3=!td$Vj4>Tg06Haj3MTg08H^j4\Tg08I<j4:Tg08JGj6DTg06lUj3ZTg01i1j3LTg05h?j2KTg06DYj2JTg06Ehj2RTg08KVj5YTg08Ldj5dTg00BDj6XTg000Gj3FTg02W?j3WTg04Ehj3Ij4VTg021`j6cTg013_j6bTg01<;j5a!s_$hj3TTg01fUj3STg08N<j4`Tg02S7j2_Tg015\R3f1R4f0R533p=0g00YgR6?T65p=@AS665p=?g00aRR7g00b2R87=5p=4f3R9f2R:g00X]R;?T;4AS;;5C`p=1%;5==78p=8f4R8AN:45739p=9f6R<f5R=P8P9P:P4P5ED'_p=<g00\Vg00]^#C#C#CR>!s-%#U#P%U>#P#[[%H3R>1G66R?#HR@P?p,4SEGSRAP<P=P8CE1059RBf7RC,04[^13P>P?P01G6;RDP6P>p,1AREf8RF%@5RG%?5RHC6P0P6P;P>P4P=P4P5P:CAn2001102000120104105RI!s<&1!s<'2106X0?X2>P8P9DB,0:1098RJ%;9RK#4RLA3?5<RMf;RNP=f9RO=2N4RPPPC1[^0?'5'7[[[^43^:>X<@PAP!v;$CE104<\B!u:+P!u6$PEPCPGPHC6P!tZ>%^?RP!t]&PJA3?5PRPf:RQP=A2QF4RRPR!tM%RR,5LP5g00c1PNP<A2NO:RSPSC1P5n!t&$0000X3PX=?9QLRCOW6W?W>X43X:>PAPCP<P=!t|$F!t|7O!t|E!vX+f<RRP=A2RQ!v?&\M^0?,5L,7J!vB+PAPFPCP<!tA$O!tA7Q!tAEAN?<=!v?'EPO%@C%?CC61GD6RB1]B5PEPQ%@F%?FC6==B5!t-&EPR%@Q%?Q!s<&!tH0f?RJ!ueFQ!sX+4!z7-R!z7?!st7DB,0C10FO%8FP?P5P?f=RLPRD9fBRMPQf@RP=2M4!x<%!z&']6]9!tF+EPPf>RS#@%?SC6!tc$4P5C>5=B!uP2CRT!uPFS!uF+:PS!uF$9!uF9DB,0N10RL%8R!u2&ARUPPD9fFRVPSfDRW=2V4RXPX!u21^Q6P5PEPT%@U%?U!u+&6P;P:P4C>!u48PV!u2FUPJ!#4A$CADB,0SPU!}?&ARI,05RHg03hXp4p710RGP7\5RX%H:RYP2AM9:59394A38:4P9P:O1#4'7[RZA3945P:P4!s8%AM894938:R[[A3=9:P8P9!sA%\[!#5h&C\P4!tw$!}2%12!};&W;X54WFW7R[PZ^;Y^54^FX^7GRGP5P3%;5RXPWPW!|-&:RY!s0%P5F<X43P:PTP4O510:T%;:PTPT!}s&:!s-%P:F<#4'7P2109WPKPWP!sh'9F<#4fJRY,08P510=V%;<fGRKPKPNPQPOC:RZ!s0%P<!sR$ER\PCP4O2WNW8P4P5O2!uJ7b8b3W8X13104K\H^13PMPIPPPJP5!t{%PI%8PA3?5WPYPMfHRI=2Y4RHPH!y/,P2PM!#8Q%A,0U%8UA3?5\fKR\PTfIR==2\!sY010MT%8M!z9%PKPVD9fLRHPWA2HY4R]P]!t'-5!vq+A,0T%8WA3?5IfNRWPVA2WH4RTPT!sV'P[P!wT$PXPIPIPRPNPQC:RX!s0%!wQ'VPKP:O510VK%;VPKP!v['V!wI,KI%;KPIP!sa'KF<#410I=%8I!|B&MRQPHD9fRRNPYfPRR=2N!|B2!wt$Y%;YP\P\PJPSPLC:!s-%PY!sx%\H%;\RL#4RX!v/&RfORZD9fURGPQfSR[=2G!u\14PHPH!wm$SC:!s-%P\EDR\=ZL5%4\,5XP1%8HPQPQPUPPPJC:!s-%PHED#4%8QRH!t<&NfQRJD9fWRXPZA2XG4R\P\!t9+5%8WR\!sR&[PND9fXRLPRfVRS=2L!tf&RT[^0?;L5XAHP5O1!{o$MPUPPC:!s-%PQED#4P1P\A3?5NP!sW$%8ZRZ!vl&TRTP[D9fYR\PJA2\X4RJPJC1RJ!tX&O%8RR!#4^%PGPTD9ROfZRQPNA2QL4RNPN!u+%RN!tW$ZP5O1A3?5[P!si$P1A=?S4A3?4Gf[R1P[A21\:!ud%P5A=?X:P?PLf]R\PGA2\15R1P1C1X=?PB!#5?'=PIC>PKC>P\PG!#5<$1G;;R1P5!#6~%1P4P;P;faR11K45'J1R1:C>!#9PJR0P0C1X0BP7PGPGP=PIPKC:!s-%PTED%45XP7P<!sB'PTDYR!s4/dEX%4<p,Ckentry_apart_b_sem'P\f\R<PSPGPYP=PIg07U<!#6V%Yp-0\5RG%H4R7P2AF:45A385:P8P4O1[^59R2[A3954P9!s8&:AF9:4[RBAF89:\2AW:45P5!#6@8WEW7PB^;7^EG^7YP5P3f^RY=IA\PX105Lf`RGf_R75IARB=F3Y105GPAfcfbR2P4CV[^53[1057PAP2P1!s9'AIA1G=F37[AW3BYPXP4!#;I$O2EcW8X13O4b3PAP\P<PSCEeP5O9b@P<PTP;P;1K=I,J<1R<KC>RKPKC1e!#?i$L%?LC6PVEbP<PTA2<QLR<P<C1eP9P5EXW3!y|&:SP8P9P5O2WKP5O1!uw-21!xN$!#CP$OX=?9QRNWD!sL4!vK$1000W@!sB=bCCOWCWJ!#7{5!s/&bBb3WDWB!sH>ObIW6W9XU6XT;XS6!sQ-1!sQ'103107XGD!sC90103P5P:O2b9bG!#El-WLX<@X0?P5DaW<WRWMWHo"). Qed.

Lemma existsb_filter_split : forall {T} (g h : T -> bool) l,
  existsb h l = (existsb h (List.filter g l) || existsb h (List.filter (fun x => negb (g x)) l))%bool.
Proof.
ltac2:(KReplay.run1z (kr_t_AsanNodesMmB ()) ["SoundMunmap"] "##2Up'0h01xh11bi001bh21lh32IHh41Th51gh61hp;1p;3p;2p;6p;5p200R0g01<;R1p4p710p8P0g03hXR2!s7'g00F8j17TP2j31Tg01:_j14Tg008Oj29Tg00EXj1<Tg06Haj36!sJ$?j35Tg02S7j20Tg013_j68Tg0042j3:Tg06gfj1>TP1j5=Tf4R1f3R2f2R3f1R4f0R53631p=3g00aRR610457:3p=2A1345,02p=;P6\5P6\4%73P2%72A1135P1P3P1P2P5D3!s2&1P5O1#4X01P5D332W2g01<]R7,96%<2R89124P2P4P2P3P8D3!s2&2!s^'2P8D332e%71f5R8?125P8P2P8P!sx$!s2&8!sU'8!t5%P8P3O1P6P6f6R9P1O1R:f8R;P9P2C;P6f9R<#7R=P5f7R>=6;2R?95;1P?n010!s#$2000091;9P6P=%45P;!t2';!sV$=!sV$=!sV532P5P6A6>93R@91>8RAP>P8P>!sf'>=6>3RBC;RC10:5RDA1;9?R?,0:A1;9=R=32X16P8P2O1REP6P6P<P>P<P;P1D3RF!s4&<!sw'<!s=$<'0,05RG105F;2<P5g00b2RH,96RI10?=RJ,0HRK10H?;2=e196JRL107JRJ107!s:$n011!uD,b1A1>83RMP4E810EMRNA5>2!uK$P6%7;R;%4HA5>2BR@PB!v%3>832eP6PC10:=92D?X16P!uE$105<92GFP5P6PHA:6H5X16PI10?H%>?E810H=92K?ePL107=92J?!tj4P!te$P6P;%47P!tN892NA!s^/101b1A5934R49191P9P1P9P8P4D3!s2&9!vs'9P4!z7$W3W2X02P5D=W2W6W5X40o"). Qed.

Lemma node_munmap_sound : ltac2:(zQ "h71!jb!hn8!mm6!u4!j6!jn0!nr5!iua!mmc!nrd!ml5!hj6!og3!oka!td!hnd!ho4!j0!oo2!oo8!op6!oq4!ou5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2cs$2>3cs'$2>1E$b>1R@2$7@1$0#5@1$1@1$0#k0>4FULL~0>5model$5>1T$h6>0@b$a?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^5^7^4^3^2>0@3$4$f@2$h3?4SEGS^8$h0>0@3$4@1$3$2@2$h4?1A^9@2$e$2^8>0>2E'$b>2R'@2$7@1$0#5@1$1@1$0#k0>5FULL'~0>6model'$5>0@2$h1@3$c?3nx0^c^4@3$c@1$h5^e^c^4>0@b$a?4SEGS?1A?5LIMIT?4SINV?4argH?3FS0^5^e^4^3^2>0@3$4$h2@1$6^3@1$6^b@4$d?4SEGS?2SC@6$9?2fx?4SEGS^6@1$8^h0^5^4^b@4$d?4SEGS?2SC@6$9?2fx?4SEGS^8@1$8^b^7^6^5").
Proof.
  intros cs cs' E R FULL model T HC Hec Hn HK.
  destruct (AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
  rewrite node_munmap_eq in Hn. (* [comment removed for export] *) unfold node_munmap_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 215).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  subst z17.
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsp.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hgone]. apply andb_prop in Hcond as [Hcond Hhi64]. apply andb_prop in Hcond as [Hcond HFLAT]. apply andb_prop in Hcond as [Hhas Hpal].
  set (k := kn cs) in *.
  set (g := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) in *.
  set (ng := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) in *.
  assert (NG : forall l, List.filter ng l = List.filter (fun p => negb (g p)) l).
  { intros l. induction l as [|p l IH]; cbn; [reflexivity|]. rewrite IH. subst g ng. cbv beta. destruct (split_lit (fst p)); reflexivity. }
  rewrite !NG in Hn, Hgone. clear NG ng.
  set (gone := List.filter (fun p => negb (g p)) (a_vis cs)) in *.
  set (kept := List.filter g (a_vis cs)) in *.
  apply some_inj in Hn. subst cs'.
  (* [comment removed for export] *)
  apply existsb_exists in Hhas as (m & Hm & Hmatch). unfold amap_match in Hmatch. apply andb_prop in Hmatch as [Hb Hlen_eq].
  pose proof (len_eqb_sound E _ k ne (am_len m) HKN Hlen_eq) as Hne_eq.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & _ & _).
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (addr := edenot E (reg cs 10)). set (n := edenot E (am_len m)).
  assert (Haddr : True) by exact I.
  apply andb_prop in Hb as [Hnf Hb]. apply negb_true_iff in Hnf. apply expr_eqb_eq in Hb.
  assert (Haddr' : edenot E (am_base m) = addr) by (subst addr; rewrite Hb; reflexivity). clear Haddr. rename Haddr' into Haddr.
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
  pose proof (maps_match_In E _ _ m MM Hm Hnf) as HIN.
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  assert (BPOS : forall iv, In iv (vm_maps (m_vmmaps model)) -> 0 < bv_unsigned (snd iv)).
  { intros iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) HB iv Hiv)). }
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5).
  unfold amap_den in B1, B2, B3, B4, B5. cbn [fst snd] in B1, B2, B3, B4, B5. rewrite Haddr in B2, B4, B5. fold n in B1, B3, B4, B5.
  pose proof (u64_range addr) as Ra. pose proof (u64_range n) as Rn.
  destruct (xhi k (reg cs 10)) as [ahi|] eqn:Hahi; [|discriminate]. apply Z.leb_le in Hhi64.
  pose proof (xhi_sound SEGS E _ k (reg cs 10) ahi HKN Hahi) as Hahi'. fold addr in Hahi'. unfold two64 in Hhi64.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. rewrite <- Hne_eq, Hne. apply u64_lit. lia. }
  assert (HnZw : Z_to_bv 64 nZ = n) by (rewrite <- Un; apply Z_to_bv_bv_unsigned).
  destruct (split_flat_estart E _ k (reg cs 10) bb bk ne HKN Hsp HFLAT) as (Hest & _ & _). fold addr in Hest.
  assert (HelenZ : elenZ E ne = nZ) by (unfold elenZ; rewrite Hne; apply u64_lit; lia).
  set (lo := bv_unsigned addr) in *. set (hi := lo + nZ).
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP. pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as HSP0. unfold CEIL, CEILMAX in HTOP.
  assert (Hlohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= TOP model /\ lo < hi /\ lo mod 4096 = 0 /\ hi mod 4096 = 0).   (* [comment removed for export] *)
  { subst hi. split; [lia|]. repeat split; try lia. rewrite Z.add_mod, B2 by lia. rewrite <- Un, B3. reflexivity. }
  pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 215 HC ltac:(lia) H17) as [R17 _]. rewrite <- bv5_17 in R17.
  pose proof (reg_sound' E cs R FULL model 10 HC ltac:(lia)) as R10. fold addr in R10. rewrite <- bv5_10 in R10.
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  (* [comment removed for export] *)
  pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS.
  assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
            bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m'))).
  { intros m' Hm' Hnf' Hne'. pose proof (maps_match_disjoint SEGS A RES_len E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
  (* [comment removed for export] *)
  assert (DISJl : forall iv, In iv (vm_maps (m_vmmaps model)) -> iv <> amap_den E m ->
            bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv)).
  { intros iv Hiv Hne'. pose proof (seps_In_disjoint _ iv (amap_den E m) SEPS BPOS Hiv HIN Hne') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
  assert (UNIQ : forall iv, In iv (vm_maps (m_vmmaps model)) -> fst iv = addr -> iv = amap_den E m).
  { intros [ib isz] Hiv Hb0. cbn [fst] in Hb0. subst ib.
    destruct (bv_eqb isz n) eqn:Hs.
    - apply bv_eqb_eq in Hs. subst isz. unfold amap_den. rewrite Haddr. reflexivity.
    - exfalso. assert (Hne' : (addr, isz) <> amap_den E m).
      { unfold amap_den. rewrite Haddr. fold n. intros Heq. injection Heq as Heq. rewrite Heq, bv_eqb_refl in Hs. discriminate. }
      pose proof (DISJl _ Hiv Hne') as D. cbn [fst snd] in D. pose proof (BPOS _ Hiv) as P. cbn [snd] in P. subst lo hi. lia. }
  assert (MATCH : forall m', In m' (a_maps cs) -> negb (amap_match k (reg cs 10) ne m') = negb (amap_eqb m' m)).
  { intros m' Hm'. f_equal. unfold amap_match.
    destruct (amap_eqb m' m) eqn:Hmm.
    - apply APS.amap_eqb_eq in Hmm. subst m'. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq. reflexivity.
    - assert (Hne' : m <> m') by (intros <-; rewrite amap_eqb_refl in Hmm; discriminate).
      destruct (is_fog m') eqn:Hnf'; [reflexivity|]. cbn [negb andb].
      destruct (expr_eqb (reg cs 10) (am_base m')) eqn:Heq; [|reflexivity]. exfalso.
      apply expr_eqb_eq in Heq.
      pose proof (DISJ' m' Hm' Hnf' Hne') as D. rewrite <- Heq in D. fold addr lo in D.
      pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' MM Hm' Hnf')) as (C1 & _). unfold amap_den in C1. cbn [snd] in C1. lia. }
  assert (MAPS' : maps_match E (List.filter (fun m' => negb (amap_match k (reg cs 10) ne m')) (a_maps cs)) (map_remove (vm_maps (m_vmmaps model)) addr)).
  { rewrite (filter_ext_in _ (fun m' => negb (amap_eqb m' m))) by (intros m' Hm'; exact (MATCH m' Hm')).
    rewrite <- Haddr. apply maps_match_remove; [exact MM | exact Hm | exact Hnf | exact (seps_NoDup _ SEPS BPOS) |].
    intros iv Hiv Hfst. apply UNIQ; [exact Hiv | rewrite Hfst; exact Haddr]. }
  assert (INMAPS' : forall z, in_ivs z (map_remove (vm_maps (m_vmmaps model)) addr) = (in_ivs z (vm_maps (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
  { intros z. unfold map_remove.
    destruct (in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model)))) eqn:Hl; symmetry.
    - apply in_ivs_true' in Hl as (iv & Hiv & Hziv). apply filter_In in Hiv as [Hiv Hkeep]. apply negb_true_iff in Hkeep.
      assert (Hne' : iv <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
      pose proof (DISJl iv Hiv Hne') as D.
      apply andb_true_intro. split; [apply (proj2 (in_ivs_true' _ _)); exists iv; auto|].
      apply negb_true_iff. unfold in_rng. apply andb_false_iff. destruct D; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
    - apply andb_false_iff.
      destruct (in_ivs z (vm_maps (m_vmmaps model))) eqn:Hin; [right|left; reflexivity].
      apply in_ivs_true' in Hin as (iv & Hiv & Hziv). apply negb_false_iff.
      destruct (bv_eqb (fst iv) addr) eqn:Hfa.
      + apply bv_eqb_eq in Hfa. pose proof (UNIQ iv Hiv Hfa) as ->. unfold amap_den in Hziv. cbn [fst snd] in Hziv. rewrite Haddr in Hziv. fold n lo in Hziv.
        unfold in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; subst hi; lia.
      + exfalso. assert (X : in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) = true); [|congruence].
        apply (proj2 (in_ivs_true' _ _)). exists iv. split; [|exact Hziv]. apply filter_In. rewrite Hfa. auto. }
  (* [comment removed for export] *)
  assert (GONE : forall p, In p gone ->
            (forall z, (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)) = true -> lo <= z < hi)%bool
            /\ (0 <= fst (sh_iv E k p))
            /\ (forall x : word, fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p) -> MR E cs model FULL x = Some (Z_to_bv 8 0))
            /\ (forall z, (sh_lo A E p <=? z) && (z <? sh_hi A E p) = true -> fst (sh_iv E k p) <= z < fst (sh_iv E k p) + snd (sh_iv E k p))%bool).
  { intros p Hp.
    pose proof (proj1 (forallb_forall _ _) Hgone p Hp) as G. cbv beta in G.
    assert (Hpv : In p (a_vis cs)) by (unfold gone in Hp; apply filter_In in Hp as [Hp _]; exact Hp).
    destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
    destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
    apply andb_prop in G as [G Gz]. apply andb_prop in G as [G Gin]. apply andb_prop in G as [Gab Gan].
    apply Z.leb_le in Gab. apply Z.leb_le in Gan.
    assert (AL8 : forall e, 3 <= ealign k e -> uE E e mod 8 = 0).
    { intros e Hee. destruct (ealign_sound SEGS E _ k e HKN) as [_ [q Hq]]. unfold uE. rewrite Hq.
      replace (2 ^ ealign k e) with (2 ^ (ealign k e - 3) * 8) by (rewrite <- (Z.pow_add_r 2 _ 3) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    pose proof (AL8 _ Gab) as A8b. pose proof (AL8 _ Gan) as A8n.
    pose proof (xinside_sound SEGS E _ k pb pk (snd p) bb bk ne HKN Gin) as [I1 I2]. rewrite Hest, ?HelenZ in I1, I2. rewrite HelenZ in I2.
    unfold elenZ in I2.
    pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(pose proof (u64_range (edenot E (snd p))); unfold CEIL in *; (first [clear - RES_len B1 Ra HTOP Hlohi I1 I2 H; lia | lia]))) as Up.
    destruct (kzero_x_sound E _ k k sb sk sn HKN HKN Gz) as (Z1 & Z2 & Z3).
    unfold sh_iv. rewrite Hsh. cbn [fst snd].
    split; [|split; [exact Z1 | split; [exact Z3|]]].
    - intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold uE in *. rewrite Up in Hz1, Hz2. subst hi. (first [clear - RES_len B1 Ra Hlohi I1 I2 Up Hz1 Hz2; lia | lia]).
    - (* [comment removed for export] *)
      unfold shadow_of in Hsh.
      destruct (split_lit (eadd (mkSrl k (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
      assert (Usn : elenZ E (mkSrl k (snd p) 3) = bv_unsigned (edenot E (snd p)) / 8).
      { unfold elenZ. rewrite (mkSrl_denot SEGS E _ k (snd p) 3 (Z_to_bv 64 3) HKN) by (rewrite u64_lit by lia; reflexivity).
        rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
      rewrite Usn in *.
      pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
      apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
      rewrite (mkSrl_denot SEGS E _ k (fst p) 3 (Z_to_bv 64 3) HKN) in D by (rewrite u64_lit by lia; reflexivity).
      rewrite u_srl64 in D. pose proof SHADOW_ok as SO. pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn'.
      change (2 ^ (3 mod 64)) with 8 in D.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite !u64_lit in D by (first [clear - RES_len SHADOW_ok; lia | lia]).
      rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (first [clear - Rb SO; lia | lia]).
      intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold sh_lo, sh_hi, uE in Hz1, Hz2.
      unfold estart. cbn [a_base a_off]. unfold estart in Z1, Z2. cbn [a_base a_off] in Z1, Z2.
      (* [comment removed for export] *)
      rewrite Z_to_bv_unsigned, bv_wrap64_mod in D. unfold uE in A8b, A8n. (first [clear - Hz2 Hz1 D Z2 Z1 A8n E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & Wsp).
  unfold cfg_of.
  eapply (srz_munmap_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len T Hf He Hhalt R17 R10 B2 R11 ltac:(lia)).
  { unfold TASK_SIZE. fold nZ. unfold CEIL in *. lia. }  (* [comment removed for export] *)
  { fold nZ. rewrite HnZw. apply map_has_intro. rewrite <- Haddr. exact HIN. }
  fold nZ. rewrite HnZw. rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  set (model' := munmap_model addr n model). set (FULL' := unfill addr n FULL).
  match goal with |- srealizes _ (mkCfg _ ?mo) _ => change mo with model' end.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _) in HK.
  specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
  unfold cfg_of in HK. replace (pc cs') with (pc cs + 4) in HK by reflexivity. rewrite bv5_10. apply HK; [|reflexivity]. clear HK.
  (* [comment removed for export] *)
  (* 08b1429: munmap CUTS [addr, addr+n) out of the ledger (maps_subtract); on this ledger the cut
     removes exactly the entry (addr, n): every entry is positive (co_bounds), the entry at addr is
     unique and every other one is apart (seps), so MmapSim.maps_subtract_exact applies. *)
  assert (HDEN : amap_den E m = (addr, n)) by (unfold amap_den; rewrite Haddr; reflexivity).
  assert (PM : vm_maps (m_vmmaps model') = map_remove (vm_maps (m_vmmaps model)) addr).
  { change (vm_maps (m_vmmaps model'))
      with (maps_subtract (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)).
    apply maps_subtract_exact.
    - pose proof (BPOS _ HIN) as P. rewrite HDEN in P. cbn [snd] in P. exact P.
    - intros b s Hbs. pose proof (BPOS _ Hbs) as P. cbn [snd] in P. exact P.
    - intros b s Hbs Hba. subst b. pose proof (UNIQ _ Hbs eq_refl) as E1. rewrite HDEN in E1.
      injection E1 as E1. exact E1.
    - intros b s Hbs Hba.
      assert (Hne' : (b, s) <> amap_den E m) by (rewrite HDEN; intros Heq; injection Heq as Heq _; exact (Hba Heq)).
      pose proof (DISJl _ Hbs Hne') as D. cbn [fst snd] in D. subst lo hi. lia. }
  assert (PN : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PL : m_vm_lazy model' = maps_subtract (m_vm_lazy model) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PISP : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)) by reflexivity.  (* [comment removed for export] *)
  assert (PT : m_vm_materialized model' = List.filter (page_outside_range lo (lo + bv_unsigned n)) (m_vm_materialized model)) by reflexivity.
  rewrite Un in PN, PL, PT. fold hi in PN, PL, PT.
  (* [comment removed for export] *)
  assert (NOACC : forall z, in_ivs z (vm_noaccess (m_vmmaps model')) = (in_ivs z (vm_noaccess (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
  { intros z. rewrite PN, !in_ivs_covered. apply covered_maps_subtract; [exact W2 | lia]. }
  assert (LAZYOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
            page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model)).
  { intros x Hx. rewrite PL. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
    pose proof (page_of_byte_out_aligned x lo hi L4 L5 Hx). apply page_in_ranges_subtract_out; [exact W3 | lia | unfold page_size; lia]. }
  assert (ALW : forall z, in_allow A E cs z = (in_allow A E cs' z || existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool gone
                                                 || existsb (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool gone)%bool).
  { intros z. unfold in_allow, in_vis, in_sh, cs'. cbn [a_vis]. subst kept gone.
    rewrite (existsb_filter_split g (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs)).
    rewrite (existsb_filter_split g (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool (a_vis cs)).
    destruct (existsb _ _), (existsb _ _), (existsb _ _), (existsb _ _); reflexivity. }
  assert (VISLE : forall x : word, VIS E cs' model' x = true -> VIS E cs model x = true /\ (lo <= bv_unsigned x < hi -> False)).
  { intros x Hv. unfold vis in Hv |- *. change (TOP model') with (TOP model) in Hv. rewrite PM, INMAPS', NOACC in Hv. destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
    destruct (in_rng lo hi (bv_unsigned x)) eqn:Hr.
    - unfold in_rng in Hr. apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
      replace (in_hull A (bv_unsigned x)) with false in Hv
        by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      replace (TOP model <=? bv_unsigned x) with false in Hv by (symmetry; apply Z.leb_gt; lia).
      rewrite andb_false_r in Hv. cbn in Hv. discriminate.
    - assert (Hx : bv_unsigned x < lo \/ hi <= bv_unsigned x).
      { unfold in_rng in Hr. apply andb_false_iff in Hr as [Hr|Hr]; [apply Z.leb_gt in Hr | apply Z.ltb_ge in Hr]; lia. }
      split; [|lia]. rewrite (LAZYOUT x Hx) in Hv. rewrite !andb_true_r in Hv.
      apply orb_prop in Hv as [Hv|Hv]; [rewrite Hv; reflexivity|]. apply orb_true_iff. right.
      apply andb_prop in Hv as [Hv1 Hv2]. apply andb_prop in Hv1 as [Hv0 Hv1]. rewrite Hv0, Hv1. cbn [andb negb].
      apply orb_prop in Hv2 as [Hv2|Hv2]; [rewrite Hv2; reflexivity|]. rewrite (ALW (bv_unsigned x)), Hv2. cbn [orb]. apply orb_true_r. }
  assert (VISEQ : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
            (forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
            VIS E cs' model' x = VIS E cs model x).
  { intros x Hx Hnsh. unfold vis. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hx), (ALW (bv_unsigned x)).
    replace (in_rng lo hi (bv_unsigned x)) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb]. rewrite !andb_true_r.
    replace (existsb (fun p => (uE E (fst p) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p) + uE E (snd p)))%bool gone) with false.
    2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (G1 & _).
         match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
    replace (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) with false.
    2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (_ & _ & _ & G4).
         match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. exact (Hnsh p Hp (G4 _ Ht)). }
    rewrite !orb_false_r. reflexivity. }
  (* [comment removed for export] *)
  assert (MRNONE : forall x : word, MR E cs model FULL x = None -> MR E cs' model' FULL' x = None).
  { intros x Hx. unfold Mr, mrestrict, hid in Hx |- *.
    destruct (argH E x); [reflexivity|]. cbn [orb] in *.
    destruct (VIS E cs' model' x) eqn:Hv'; [|reflexivity]. cbn [negb].
    destruct (VISLE x Hv') as [Hv Hnin]. rewrite Hv in Hx. cbn [negb] in Hx.
    unfold FULL'. rewrite unfill_out by (rewrite Un; lia). exact Hx. }
  assert (MRKEEP : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
            (forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
            MR E cs' model' FULL' x = MR E cs model FULL x).
  { intros x Hx Hnsh. unfold Mr, mrestrict, hid. rewrite (VISEQ x Hx Hnsh). unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hx). reflexivity. }
  (* [comment removed for export] *)
  assert (HALLOW_in : forall iv, In iv (ALLOW E cs') <-> In iv (ALLOW E cs)).
  { intros iv. unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply in_flat_map_split. }
  assert (HALLOW_bytes : A_bytes (ALLOW E cs') = A_bytes (ALLOW E cs)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply A_bytes_flat_map_split. }
  assert (DISJF : forall m', In m' (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs)) ->
            In m' (a_maps cs) /\ m <> m'
            /\ (is_fog m' = false -> bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m')))).
  { intros m' Hm'. apply filter_In in Hm' as [Hm' Hnm].
    assert (Hne' : m <> m').
    { intros <-. unfold amap_match in Hnm. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq in Hnm. discriminate. }
    split; [exact Hm'|]. split; [exact Hne'|]. intros Hnf'. exact (DISJ' m' Hm' Hnf' Hne'). }
  assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
  { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
  (* 30 names for 30 fields; [Xmbase] removed with the [co_mbase] field, 2026-11-07. *)
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xtop Xsp0 Xnasub Xnone Xkinds Xtotsz Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xvmx Xrdr].
  destruct Hlohi as (L1 & L2 & L3 & L4 & L5).
  assert (HAeq : ALLOW E cs' = flat_map (allow1 A E) (kept ++ gone ++ a_ghost cs)) by reflexivity.
  assert (HTOPEQ : TOP model' = TOP model) by (unfold TOP, alloc_top; rewrite PISP; reflexivity).
  constructor; rewrite ?HAeq; subst cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss];
    try set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _) in *; rewrite ?HTOPEQ.
  - (* [comment removed for export] *) apply regs_ok_set_n'; [exact Xregs | lia | reflexivity].
  - reflexivity.
  - (* [comment removed for export] *) unfold know_ok. apply Forall_forall. intros K HinK.
    destruct (fold_unfill_inv E _ k gone (kn_unfill k bb bk ne) K Xknow
                ltac:(intros K' HK'; unfold kn_unfill in HK'; apply filter_In in HK' as [HK' _]; exact HK') HinK) as [Hin0 Hsh].
    unfold kn_unfill in Hin0. apply filter_In in Hin0 as [Hin0 Hkeep0].
    pose proof (proj1 (Forall_forall _ _) Xknow K Hin0) as HKK.
    destruct (kimg_b K) eqn:HnotImg.
    { destruct K; try discriminate. cbn [kentry_ok] in HKK |- *. destruct HKK as (HA' & HB' & HCC).
      split; [exact HA'|]. split; [exact HB'|]. intros i Hi. apply MRNONE. apply HCC. exact Hi. }
    apply kentry_keep_foot with (M := MR E cs model FULL); [exact HKK | | exact MRNONE].
    intros x Hfx.
    cbn [orb] in Hkeep0. rewrite APS.kentry_apart_bp_eq in Hkeep0.
    pose proof (kentry_apart_b_sem' E _ k K bb bk ne Xknow Hkeep0) as Hap0. rewrite Hest, HelenZ in Hap0.
    destruct Hsh as [Himg|Hsh]; [rewrite Himg in HnotImg; discriminate|].
    unfold kfoot_apart in Hap0, Hsh.
    destruct (kfoot E K) as [[fs fl]|] eqn:Hkf; [|destruct Hfx].
    apply MRKEEP; [subst hi; (first [clear - Hap0 Hfx E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia])|]. intros p Hp Hin. pose proof (Hsh p Hp) as HH. rewrite ?Hkf in HH. cbn [fst snd] in Hin. (first [clear - HH Hin Hfx E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
  - unfold model'. rewrite munmap_model_halted. exact Xhalt.
  - unfold fds_ok in *. exact Xfds.
  - exact Xfs.
  - exact Xtid.
  - (* LPS 727298f3 port: [co_res]'s third conjunct; the mappings left are a filter of
       the old ones, so each stays apart from the unchanged ledger *)
    destruct Xres as [kb [Hkb [Hmb [Hmr Hvd]]]]. exists kb. split; [exact Hkb|]. split; [exact Hmb|].
    split; [|exact Hvd].
    rewrite PM. apply Forall_forall. intros iv Hiv.
    unfold map_remove in Hiv. apply filter_In in Hiv as [Hiv _].
    exact (proj1 (Forall_forall _ _) Hmr iv Hiv).
  - exact Xlimit.
  - rewrite PM. exact MAPS'.
  - (* [comment removed for export] *)
    rewrite PM. apply Forall_forall. intros m' Hm' Hk'. destruct (DISJF m' Hm') as (Hm0 & _ & _).
    destruct (proj1 (Forall_forall _ _) Xholes m' Hm0 Hk') as [HF1 HF2]. split; [|exact HF2].
    intros iv Hiv. apply HF1. apply in_app_iff in Hiv as [Hiv|Hiv]; apply in_app_iff; [left; exact Hiv | right].
    unfold map_remove in Hiv. apply filter_In in Hiv as [Hiv _]. exact Hiv.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. apply seps_filter. exact Xseps.
  - (* [comment removed for export] *) unfold model_ivs_wf. rewrite PM, PN, PL. split; [|split; [|split; [|unfold init_sp_ok in *; rewrite PISP; exact Wsp]]].
    + unfold map_remove. apply ivs_wf_filter. exact W1.
    + apply maps_subtract_wf; [exact W2 | lia].
    + apply maps_subtract_wf; [exact W3 | lia].
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. exact (proj1 (Forall_forall _ _) Xbounds iv Hiv).
  - (* [comment removed for export] *) rewrite PL. apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
    pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. (first [clear - Y2 Y1 R2 R1 E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
  - (* [comment removed for export] *) exact Xtop.
  - (* [comment removed for export] *) exact Xsp0.
  - (* [comment removed for export] *) intros z Hz. rewrite PM, INMAPS'. rewrite NOACC in Hz. apply andb_prop in Hz as [Hz1 Hz2]. rewrite (Xnasub z Hz1), Hz2. reflexivity.
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
    assert (Hnf' : is_fog m' = false) by (apply KNF; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])). specialize (D Hnf').
    rewrite PN. pose proof (proj1 (Forall_forall _ _) Xnone m' Hm0 Hk') as X.
    pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' Xmaps Hm0 Hnf')) as (C1 & _).
    unfold amap_den in *. apply maps_subtract_keeps; [lia | exact C1 | exact X | cbn [fst snd]; subst hi; lia].
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk' x Hx. destruct (DISJF m' Hm') as (Hm0 & Hne' & D).
    specialize (D ltac:(apply KNF; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]))).
    destruct (proj1 (Forall_forall _ _) Xkinds m' Hm0 Hk' x Hx) as [K1 K2].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x) by lia.
    rewrite NOACC, K1, (LAZYOUT x Hxo), K2. split; reflexivity.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. rewrite sum_sizes_app. rewrite sum_sizes_app in Xtotsz.
    pose proof (sum_sizes_filter_le (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) as SF.
    change (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)). lia.
  - exact Xbrk.
  - exact Xsbrk.
  - (* [comment removed for export] *) rewrite (eager_used_sem model'), (eager_used_sem model Xwf) in *.
    2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
    rewrite PM. unfold map_remove.
    eapply Z.le_trans; [|exact Xeager]. apply sum_count_filter_le.
    intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
    (* [comment removed for export] *)
    assert (Hxo : x < lo \/ hi <= x).
    { assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
      pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
    f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
    replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb]. rewrite !andb_true_r. reflexivity.
  - (* [comment removed for export] *) rewrite <- HAeq, HALLOW_bytes. exact Xabytes.
  - (* [comment removed for export] *) rewrite <- HAeq. destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?PT.
    + apply NoDup_filter. exact N1.
    + intros q Hq. apply filter_In in Hq as [Hq _]. exact (N2 q Hq).
    + intros q Hq. apply filter_In in Hq as [Hq _]. pose proof (N3 q Hq) as P3.
      unfold page_allowedb in *. apply existsb_exists in P3 as (iv & Hiv & Hbb). apply existsb_exists. exists iv. split; [apply HALLOW_in; exact Hiv | exact Hbb].
    + intros q Hq. apply filter_In in Hq as [Hq Ho]. pose proof (N4 q Hq) as P4.
      unfold page_outside_range in Ho. apply negb_true_iff in Ho.
      pose proof (N2 q Hq) as Qa. unfold page_size in Qa.
      rewrite PL. rewrite page_in_ranges_subtract_out; [exact P4 | exact W3 | lia | ].
      unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; (first [clear - Qa Ho L4 E_SP0 argH_sp0 SINV_agree argH_agree argH_high SHADOW_ok HULL_ok SEGS_in_hull; lia | lia]).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + rewrite HALLOW_bytes.
      assert (EG : eager_used model' <= eager_used model); [|change (vm_limit (m_vmmaps model')) with (vm_limit (m_vmmaps model)); lia].
      rewrite (eager_used_sem model'), (eager_used_sem model Xwf).
      2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
      rewrite PM. unfold map_remove. apply sum_count_filter_le.
      intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
      assert (Hxo : x < lo \/ hi <= x).
      { assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
        pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
      f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
      replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      cbn [negb]. rewrite !andb_true_r. reflexivity.
  - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
    assert (Hgh0 : in_ghost E cs (bv_unsigned x) = false).
    { unfold in_ghost in Hgh |- *. subst cs'. cbn [a_ghost] in Hgh. rewrite existsb_app in Hgh. apply orb_false_iff in Hgh as [_ Hgh]. exact Hgh. }
    rewrite PM, INMAPS' in Hmx. apply andb_prop in Hmx as [Hmx Hxo'].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x).
    { apply negb_true_iff in Hxo'. unfold in_rng in Hxo'. apply andb_false_iff in Hxo' as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia. }
    unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hxo).
    rewrite NOACC in Hna. apply andb_false_iff in Hna as [Hna|Hna]; [| rewrite Hxo' in Hna; discriminate].
    rewrite (LAZYOUT x Hxo) in Hlz.
    (* [comment removed for export] *)
    destruct (HID E cs model x) eqn:Hold; [exact (Xzero x Hold Hmx Hna Hlz Hgh0)|].
    unfold hid in Hh, Hold. destruct (argH E x); [discriminate|]. cbn [orb] in Hh, Hold.
    apply negb_true_iff in Hh. apply negb_false_iff in Hold.
    (* [comment removed for export] *)
    assert (SHX : exists p, In p gone /\ fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p)).
    { destruct (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) eqn:Hex.
      - apply existsb_exists in Hex as (p & Hp & Hpx). exists p. split; [exact Hp|]. destruct (GONE p Hp) as (_ & _ & _ & G4). exact (G4 _ Hpx).
      - exfalso. unfold vis in Hh, Hold. change (TOP model') with (TOP model) in Hh. rewrite PM, INMAPS', NOACC, (LAZYOUT x Hxo) in Hh. rewrite (ALW (bv_unsigned x)), Hex in Hold.
        replace (existsb (fun p0 => (uE E (fst p0) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p0) + uE E (snd p0)))%bool gone) with false in Hold.
        2: { symmetry. apply APS.existsb_false_forall. intros p0 Hq0. destruct (GONE p0 Hq0) as (G1 & _).
             match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
        rewrite Hxo' in Hh. cbn [negb] in Hh. rewrite !andb_true_r in Hh. rewrite !orb_false_r in Hold. rewrite Hh in Hold. discriminate. }
    destruct SHX as (p & Hp & Hpx). destruct (GONE p Hp) as (_ & _ & G3 & _).
    pose proof (G3 x Hpx) as Z0. unfold Mr, mrestrict, hid in Z0. rewrite Hold in Z0.
    destruct (argH E x); [discriminate|]. cbn in Z0. exact Z0.
  - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. unfold FULL'. apply unfill_out. pose proof (argH_sp0 _ _ Hx). rewrite Un. subst hi. lia.
  - (* [comment removed for export] *) subst cs'. cbn [a_vmops vm_replay]. destruct (vm_replay E (a_vmops cs)) as [na lz]. cbn [fst snd] in Xvmx |- *. destruct Xvmx as [Xna Xlz].
    rewrite PN, PL, <- Xna, <- Xlz. unfold vm_step, vm_lo, vm_hi. rewrite Hne, HnZw. fold addr. fold lo. rewrite Un. unfold hi. split; reflexivity.
  - (* LPS 727298f3: munmap keeps [m_proc], so the channel reader stays *) exact Xrdr.
Qed.


Theorem node_sys_sound_YMunmap : ltac2:(zQ "20!oud!mk9@a$1?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0$0").
Proof. intros cs cs' E R FULL model T HC Hpre Hn HK. eapply node_munmap_sound; eauto. Qed.

End SoundMunmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundSys.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!hn1!hs0@1$0$1").
Variable A : ltac2:(zQ "10!ovf$0").
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : ltac2:(zQ "40!jb!hn8!u4!hj6>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
Variable argH : ltac2:(zQ "40!hnd!jb!hj6!hn8>0$2>0@1$3@1$1#k0$0").
Variable FS0 : ltac2:(zQ "10!oo2$0").
Hypothesis RES_len : ltac2:(zQ "10!pnf@2$0?4SEGS?1A").
Hypothesis HULL_ok : ltac2:(zQ "10!pm0@1$0?1A").
Hypothesis SHADOW_ok : ltac2:(zQ "10!pmb@1$0?1A").
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : ltac2:(zQ "60!hj6!hnd!j6!jb!og3!hn8>1E$0>2E'$0>1a@1$5@1$3#k0>0@3$4?3nx0^3^2@3$2$1@2?4argH^4^2@2?4argH^3^2").
Hypothesis SINV_frame : ltac2:(zQ "71!jb!hn8!u4!j6!hnd!ho4!hj6&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1E$6>1M~0>2M'~0>0>1a@1$1@1$0#k0>0@3$3$4@2?4argH^4^1$5@3$3@1$2@1$1@1$0#8@1^3^2@1^4^2>0@2?4SINV^4^3@2?4SINV^5^3").
Hypothesis SINV_agree : ltac2:(zQ "50!jb!hj6!hn8!u4!og3>1E$1>2E'$1>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@3$4?3nx0^3^2>0@2?4SINV^4^2@2?4SINV^4^3").
Hypothesis RES_cover : img_lo A < img_hi A /\ forall z, img_lo A <= z < img_hi A ->
  exists iv, In iv (segments_reserved SEGS) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Hypothesis argH_sp0 : ltac2:(zQ "a0!jb!r7!hnd!ho4!j6!ptd!o2!hj6!hl4!hn8>1E$7>1a@1$9@1$0#k0>0@3$4$2@2?4argH^2^1$3@2$8@2$1@1$0#k0@2$6^3$5@2$1@1$0#k0^2").
Hypothesis E_SP0 : ltac2:(zQ "50!hnd!ho4!j6!ptd!pub@3$2$0@2$4?3nx0$3$1").
Context {SC : StepCfg} {AF : AllocForced SC}.

Theorem node_sys_sound : ltac2:(zQ "20!ov7!mk9>1y$0@a$1?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0^1").
(* LPS 727298f3 port: written out (rule 11g); the zQ statement above is untouched.  The
   replay applied [node_sys_sound_YMunmap] without the [AllocForced] instance its written-out
   proof now takes.  Shape of boost-beast/http_request's As/AsanNodesMmB.v [node_sys_sound]. *)
Proof.
  intros [| |].
  - eapply node_sys_sound_YMunmap; eauto.
  - eapply node_sys_sound_YBrk; eauto.
  - eapply node_sys_sound_YSetTid; eauto.
Qed.
End SoundSys.
(* [comment removed for export] *)
