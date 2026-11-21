(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch's channel reader, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanCeil.  (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsanInit () := KReplay.lz_vm "#'J{C47Corelib7Program6Basics4flipI!sD+5Lists7!s+#Def6Forall00!se,4Init9Datatypes3fstC46Std!sc+4!s+#8nil_cons!s`25Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmap!t576nth_okK!uT,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00c79OSSVerify6Proofs:boost_json:fuzz_parse3lib8Asan!uh$argB0C13~~~C!shO7CatExec>valid_argv_len!sp%I!wW;4list!ww>6lengthC5!vk&6ZArith6BinInt1Z6of_nat!vK>Z02!sd<2le!sB<3mul!sC=addC!wI@;bv_unsigned!sm=leb!x{G1!sh>tb!v[<4andb!zF+4Bool!s'$8orb_propI!{T72or!wW>9!sz#!sc=3and00!wu=leb_!w;?sub!sC=divK!~8<nat!|C/!y~81C!#3@93n!yz54Znat5Nat2Z9is_nonneg!vl+9micromega9SatDivModCZ_div!sP&!sW'!uD;7!sQ#mod!wJ9eq!wJ4!w#&not!v}=modulo!sF<=mod_pos_bound!{}>t!siA!uU#!si15!v%$8PreO!s/#1Z;!uU#0_r_ext!sL>!st#!sL&K!vy5=RingM!s4'5Psatz07!sOK2!sOK5!sOK6!sO6:Z!sL+;!vJ%!#6$#!zJD!tl76VarMap1!sDC3I!sD?0I!uEC7Formula00!t567Env!sT#5PExpr01!sIE!ua=6option!uE8!sk25!sIE3!}465Tauto8B!uH&K!|\;1C!x%@=Z!sn$CheckerC!v}<4find!sqAC!sq0_s!|6#!x<@1K!wvL!sQ7!ux&G!sJ'4!sJF8!#=#<bool!y-#!sF@1I!#<_>0!#<}?!ueE3Op2!x[>5eKind!u8=unit!{@8!se%4kind!tT#!sf@1!#=-F3!#:,@1I!y?@!#35/0!#3aM1!#Ca\H!#Ca&8!shN=!sh#PlanS!{2#3APS2uE!sn%!tXY:!#E;#_high!#DN%!t]O:AxSymExec33AX23env0!uMW8!uM'2AP;e_sp0_early!sqb4CEIL!sj&!#JN9?!s<25State<sp_window_lo!sa\hiC!vk^6edenot!#IvU9!so$Run39env_agree!sm`<!tY%!sp0!wZ[3NX0!zo_5E_SP0!#L:A!#;3&!#N8ZSINV!{-'!#:e1Peano2lt!xI_2ev!wVV8Prop!sj#8wrap_mem!sk%!#<W7!#It#1I!#5k?!v<Z2E!~AW!uy4b!v~'!#6k3;ZifyClasses7rew_iff!sMB;!sM&_rev!#H{75proj1!sA86!#VR$!v'Y;!#7p#!|$0!txA5mkrel!#LP=6inj_lt!#=1H5!wJP3Lib2Nd:and_elimF3!#5sP3Run?total_arg_bytes!#T&@7Z_to_bv!#Yy62InC6!tGJSys2Fs5Namei>path_has_slash!u3K2Fs8!s`$eqb!t]8tl!sqN4!sq#!#ByA2!uUX;dotdot_!t/%!#DnC5!#B\<prod!#Qr33Nat!#Y&$!s=5mu!uyL;StackLayout=at_random_ptr!shW:auxv!yf'!seI6BvBase;nat!yy#wor!#[MA6bv_!un$!tmU<string!se#rs!#7ZXC!|E2_nat!#7e7!x-31!v/R8len!v+&!s^Q!sZ#_le8!#ek7flat_!#dy#!v\U?!sc#ten_!vd%s!#g9<ap!t/X9ed!z>&!tmX!z|,!z?&!tm'!#iI1repeat!#he8!#9q$fl!#8KA9and_morph!#]TB!#Zz#!#]T-!#O/?3!#T`=3Pol!#OP7!#LB:3!#3|E!sJG7!#VED4!#^~<to!|1$!#;n7Z2Nat2id!#<4=7inj_mul!}dYA!}d3Z!#C6^F!#jX$_!{n3!#<jO!zq/A!sw&!#64,!tgX@!sn&n_to_le_8!u\_G!ss&!#6&-_fst!sz_C!vX-_map!#4N#!#BD0!#4T,=!}X%_!#ng%!vwV!wp'!~q3!y[Y!v$0pair!#Lf^@s!tu#_image_siz!#EDH3inj!#EgD!#6v#!sK@6!sK$!#fEK4!}PC!#<w#!x05:!wF'!t_88!t_#Inst7Inj_Z_Z!#GJH1!#9JW!|j$!w-#!#m+75False00!y0YMbuild_!x@%!#3g$within_span!~v^!s~4!#IPN@entry!sd&!tW$!#7C:>pow!#n{#!#pgA3pow!sC<:!sk#!#:z&!#8wB7!wL84Tru!wK#4!z'3divAZplus!#<6#idemp_r!sMIl!sM8:!#=$$mu!#qF=8mul_comm!sh:min!t8%!~_Y=!|&&bsb_eq!#6TU7StepTac9!sh#!#s:$!#4>]6!sl#ge!si`len_av!sid!#YD'!{SNAsegments_reserve!#GVK!#`u%!s]'_top!#^K[6img_hi!ux`if!tQ$!uxP!u:&brk_aslr_max!saQ9p!#9}'!ur[8BRK_ASLR!ut_7usp_fi!#Ma&!#]#]4e!#v>#!#@<^9u64_rang!#eDV!$1'&B!$1',str!$1/+!tbQAgentLib7!tb#l!v?'!yyZ!w'#lo!sid!{O'!#l>\V_S1!sjf2!sjb6V_ARGC!sleENVC!uFeL!#q%b3V_W!sib5V_BRK!~%`W!|J0!xN_!#c]&!$-k'!#<u#8!#l%#Na!#^&#;lt_ge_casesI!#lQ8!#?@-!#Ez,<!$>8#verfl!#@l4!#fF3e!v'Y8L1!v+kL!|@W!#y^48pagedow!#4<%!#6id!teW!so3mkMd!xZ2!#Bt29mod_small!t8P?!t8,!uy$4AX2S7u_mul64!u0V!sv;add!svm:!#wN%!#8>'!syf!w%#_!#z$-!wv^5mkAlu!tik;!st$!tj0!#@R9!$IK$3Sem5alu64!sNE7mul_!$@3#!sP?5Instr!sz#op01!sRHmul!sR#!#<4]al!~rce_pg!#7P^3u!#xP'!}+;<eq_decidable!#abE6!uDP!#tv34!uE_6uE0!#9&'!si[_!vs,!#<2\!$-x#!tV_<!#7K&_us!#J1'!#o{>5bv_eq!$8Q=N!#~dZ7!v1#!uE+!#hnB!#i7C2!#i7M4!wHa8!x5b6e_envp!slV!{>45!tYeaux!#Sh_8!x6#!uF,!sk^!tX,!uF_str0!vyg6!tYh1!v4_4Hav0!vud!v/k7!v/b:e_at!#w,%!ztetr8!v8_5u!~#-!#X$O8m_halt!#[VR5m_fds!sZTtid!tmTvmmap!t9R;vm!#^#Y7vm_!t>Ynoac!s;#!#\HQ!uW#_lazy!s^QA!s^$materializ!u^S8!tD#imit!s]Q6vm_brk!#__Qvm_start!saY!xn#_baseC!|&TAcct:eager_use!#g#`model!$B$'!yjPFdEntry00!#3&O!#QK47fds_st!u>`5LIMIT!sh%K!xjQVmMaps!#sgL!{H&alloc!#f3#!s^P:vm_init_sp!vUb3TOP!w~W!ug'!w}din_hul!#L7&!$2-;orb!t8b6in_ivs!t7B4negb!x3R!#iw#!};$!s^P>!s^$in!#Z|$s!uUb8in_!yd#w!uW'!#GJ%!$m7+;orb_false_r!#>^`!#<~_<!#33$_facts!#Aj_TOP!$Of`FULL!$NZ9!$IE'sym!vj6:!vj#true_r!#M&Yhid0!#wc+!}{bhi!#^:B!$qZ#g!${m79nth_erro!$BNW<!#~c$to_mem!$gYC1!to>tb_l!#<aK!#w_#!$$4-!$/4#!}7R!s`%max!#tm$!x7P!#rH&3rdn!zC_;Mr0_visibl!#s2V!tV+7rdn!$qM#!sj^D!sj#!$Uh#!v8%abov!#hEV!#`z19spli!#biZ!{T5?!su+!#a#0!$PK?bv!uO$!sLA@!$Pq%!$}z+!$'E1:!s,%_dec;Z_lt_le!s2#!#mL16Specif7sum!$k>$!#3c+7!$5[%?Rela!tB#!s6&=eq_Tran!$hQ$!sV59Morphisms:respectful!s}E<eq_Reflex!s|BJr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!%$T#er!tT;!sR,@!u$0per!sS?Mt!wc#_co_!$[$#v_impl!$HM$ism!#5';7mod_!$S$4!#9T$9!$8G#_ind!$jG^!#pP$!#_B&!so^5sadd!#qBg6a!#AD$!sod5a_off!t_g!#ntZ!#W2->!$md,!#=P'!#uSd5!sok!#i,_8!$b[$E!#B/_9!sk%ev!#fi'!{]62or!$wN3!s@,2!#<4Y!tH%!#{nZ!#s[74fla!#sTA!#?>2>!#r>#!sE+@!$XW#!$M#$!$It]>!$Mk'_spec!wh_=rdn_Mr0!#=w$!#<$FC!#;Z&!#;],!y4[!#z1$SA!{Xe6k!#D&#!#4\W!x[89!sw%_o!v3'!uYO9Ref!$b\-!xe#!#PwB3s!$m>Z7!#A6$u!tw`8!tw$!#6\+!slO!$D+&<!{E$add!$b`+!y0Z!$x`#!%$V,!uJY>read_!wH+!t`_;k!uR$!|4/!$2`=!$i{#!sF?mul!#iy_uxb!uD_4Hhi'!u=2!$K94ax!#3e#!#U+Y!w=+!|Q+!#82+!%NO81!sGC2!vR\4auxw!~yk7know!~w,!$QX;!$Fx#!#z83!$Vh'@!%K[$_!$bl$_eqI!#5Ve0!#6Il6!|>`!#YA#_be!#\o+!w>d6e!#j7#!suV!#PB49elenZ!$4|n5!sx$!wEm7!sqm!$Ej&!#@CX8store!{V#!w9a7u!$;r%!t[_5wview!scZ<find_!$TL%!sjK<MemImageType<seg_writable!shX9!sh#!$^~O!se08!se$as!%R{<4of_N!sD=to_N!v]Z?!vX&!u5$_at!#=rYMr!~v1!#?PQoreOk?!zR'_of_!yj+I!vpW7S!uL%!%FL3!$a>-1!$TdY!#?g$rgc!ubWArgvEnv7u!sh$N!siW!$UO%?!tV'v_ptr_k!sq^<cat!sp+!ta_!sn#struct!$n1/!#>@9firstn!#D6Zu_!u+5!#ApZlo!#ApB!$Cg#1_!$J3e8u_sltu!$I<'!#jJ?ge!$P@=!$p$#!%:J#!{J67iff!#o>#!#H5_!v|#n!#w`+!#C1Z8kw!sr$!$Z'b8e!sm%!#3m%!$H<M5!#Y$Y!$60%1!#=Ol!$VkE3eqb!sF?8eqb!#eb#!t^_!%MS#1!~LV!y;,!%7/,!#Ps+!~L:5skipn!%cy9x!$upR!wf#CeilA!#3J$1_!t+$_nth!uGV!#pm+seg_r!$:-'!#Y%?:bv_extrac!%1Y87f_equa!%;#W8ed_slack!#v#N;!#v#%!s^%!#xP4>!#xP'_Non!#u_Y=!#s?#!#s9#_sp!~+b!$=N$b!slb5K_RND!#8N^<!$ED#!$?r/!soY5vals!#dE3!$M:5!$T~Y7if!$/n-!w>\img!$kf'!#5%f!$SU_9!#Pd$!#Dj'!wAZif_rw!yacrw!v6+!v|]!sk#!$q;'!#I&;succ!#=r=8inj_!sJ#!v,]ph!u@b9ph!%3S#_z!#5g&!#HYV!sk&!#>2\ph_ent!tS`6!sj%!tR`num!tRdnum!xb83N!%y`/!z~\eadd!tr+!#8Q4:!#_Z$!%5E#!#>0Z!#iq'!#ut'!#4zYaux!#_W,!ui[<!$@p#kn!%5##!#3G_kr!t\+!#4wYbrk!#tK-!slY?!$0d$!%fQ%!v>d5V_UID!skb4V_H!$x?%I!ym66Ex!s2#!$a0Z8!#<m%!$>o_!$ek#L!$YU_7!si#u!$;k'!#C>U<hwcap_rv64gc!sgW=!sg/v!#@\Yargc!#kk0!soY=argv0!spl1!sp1!v=W7AT_PHDR!#GzW!sb$ENT!sc]NUM!sc[HWCAP!scW9!tH#AGESZ!sdW6AT!~]$!w2ZE!sbZ!u'#SECURE!sd[RANDOM!u-[NULL!zhY:atr!#_5#!#:{akimg!|Cb<rw!#8T2!#9HY!#;i-!srb;!#M=&!#:8X!#J^2sr_upd!#:<a9!uV$re!%X0&K!&F_C!$Yw;!&H\06!$uC#b!uX_4ridx!te'!#y,3!$zt2!&1ZF:!#z:<!%n##!ur?4BvWf!uEP!%'j8!uK#!$6E/!#]B=6eq!%J^#!tDd>!tD%!s6#trip!tHE7!tH#neq!v2AD!$4i&oblig!$D{#_1!%WDA!$-I#!$C^#!#;VY!zp+!#]H,!|Vbge!#{<k7!th$!$5;W!#[o'4ge!#k[`2R0!|FB!&74$!$>JY!&,9&!%#Z,!#N5]_stk!wDlu_sub!%7KW!tc/8!tc$!#W/'!#jIM!$0`P!$dr5!$b@#A!u6V!sr6pageu!#bGb:sha!#<6#!$JFW!td55sh!#[nX!sq9!%KnW!w>;!#pqb7a_!#`c#!smc!#?[%!|icmk_ss!{qcvis_cos!$OBb6esca!$_g&K!sl[3acs0!wlc5a_vis!xYegh!v5+!#GWY!#uw$!#3o+!#T&Z_!#6C,I!uH[4amap!&CXc9MBASE_MIN!#3~bSTKLEN_MAX!yKdfd!yK'!v<]vmo!v<,!wnTAcct7A!$4V%!xZ^9if_!#77$!v}V!#5M4E!#8q$_!%ie$!%PD0!#LSZ!#:_#!$|'#!tq&!#Q?I!$mI$5in_fsC!{']!#5IX!#DC3!#M&,!so_5s_log!wrh2Mr!|ab2!#9Ic4a_fd!uDh6fds!#]fS!y9%4m!y8_8a_tidse!$Fuh:maps_matc!#s7b6a!%7a$!sla5a_y!#B<i7hole!wi+I!ssa4se!%-J#!tg%!#3`N>BackingAlgebra6ivs_w!$YKV!vE$Ceil:!%1O%!#NdX!t^25iv!t]bE!t],!%39$!%'E#!the!%+5$_!vN0!ym[7am_kin!~Yi8amap_den!tcf!$omY!}/1m!$#Z,!uQa9sum!$B\#!#={_8if!sk/!%,%7app_nil_r!v]^_totsz!#3xdbrk!x9d_!%@w#!smb8a_a!#BA,!#vn65NoDup!&fv,!sB51!#CeX=!%8|#!#A5#ed!$6W%K!spX4MI!$>]+I!si^0!}fiin!#LZ-!xS_vmo!#;%W!|x6!%M;#pla!#SsV!%;v%;!%;v'1!$DG%!#;+a5cs_ok!$ajW!ss<!#},_3in!%[R_;!|]%!#ID,!#ahY!#f3+!#?7W!#Hm3!$es/!#T+Y!#r9&!#E\R2Fs2Fs!xLb!#AG$!#\_cCEIL!#S$'!#R;[5m!#g5#!zvW!sm63!smi4!smi!$f&A!#td0;!'>B#_empty!#l&X6reg!#w=+!siX4mks!#SBW:!#Dm+!%R{J3Run6config!%RyL!s[#B!t:%achine_s!tM#!udY!#yx$!ui[7in!$W<#!s\U!%jE#!s\P6in!$4Q#!s[P8in_!$3_#!v{O;!v2$!w]%!#;na6cfg_o!#Iv%!$fNJ!$hv1=!xU0!&LwZ3fx0!tUQ!z[/0".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z3h5LinuxProcessSemanticsfLinuxProcessSem5Statehch2target_alloc_limit37Corelib4Init9Datatypesm04list04Npos35stdpp9bitvectorbdefinitionso52bv46Stdlib6ZArith6BinInt1Zq73addm06length3h5LinuxProcessSemanticsfLinuxProcessSem3Runseftotal_arg_bytesq76moduloq73mulq76of_natq73subhc9ProcInputhch0mkProcInput_fullm04conso57Z_to_bvq73divm03nilo5bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hn53envm04boolm03nat37Corelib5Lists7ListDefhsa3nth3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthu8fat_random_byteshu89ed_random79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit4Init~~~~~~ijc5vals079OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~io55K_RNDhn53Env46Stdlib5Arith8PeanoNat3Natit33eqbm04andbq73lebq73ltbm03orbijc5argB0io5be_sp0_early79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~ji62uEm06option37Corelib4Init5Logicjn92eqhn52evm04truejn93and37Corelib4Init5Peanojq72ltijc2E0ijc5argH0io53NX069OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jt78wrap_memq72leio54CEILhn56edenotio5cexpr_vars_lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AxSymRun3~~~~~~kk59env_agreeijc5SINV0hccsp_window_lohccsp_window_hi69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~kr5h0stack_image_sizeq73powio56img_hiio58BRK_ASLRhn54EVario56V_ARGCio55V_BRKio56V_ENVCio54V_L0io54V_S1io54V_S2io53V_Wio54V_S3io54V_L1io55V_UIDio54e_pgji68pagedownio55e_sp0io55e_sp8io56e_envpio56e_auxvio56e_str0io56e_str1io5ae_atrandomio56e_atr83h5LinuxProcessSemantics5Riscv7Preludelu45bvmapjn91Ijt76regupdo52BVo54BvWflu4bbvmap_emptyhc5Modelseh1segments_reservedhcainit_modelijc3inpkr55LIMITijc6model0m04prodhc8m_vmmapsm04Nonehc7FdEntryhc5m_fdshc8m_haltedhc5m_tidhc9m_vm_lazyhch1m_vm_materializedhc6vm_brkhc8vm_limithc7vm_mapshccvm_mmap_basehcbvm_noaccesshcbvm_reservedhccvm_start_brk69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~nj8aeager_usedji67fds_stdji63TOPm04Someijc5FULL0q72lthn54exprm04pairhn59split_lithn52SAhn56adenotjn92orm05falsehu8dat_random_ptrhn54ELitio59init_regsijc2R079OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~oge7regs_okio55e_stkio58e_stklenio57a_entry01Nse6configsebinit_configji66cfg_ofjt73fx0q74of_Nhu8h1build_stack_bytes3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeos87Segmentio56atableos88PhdrInfohu89EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem2Fspib2FshcbInputStreamhc8NetQueuehc6VaSizekr59img_factsse8valid_spse9valid_brkseavalid_argvseavalid_envpseh0entry_stack_fitsse8valid_idsebvalid_hwcap" s.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition LIMIT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ka$0").

(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  (* 75d69e00 NOTE, measured and NOT acted on: boost-beast's img_facts gained a field
     [if_resx : (2 <= n_resx A) /\ (20 <= p_resx A)] bounding what the LAUNCH reserves
     beside the image (the vDSO pair), which [init_cs_ok]'s ledger case needs.  THAT HUNK
     DOES NOT PORT: boost-json's own [atable] declares no [n_resx] and no [p_resx]
     ("The reference n_resx was not found", with [n_res], [s_resv], [nq_rest], [c_resv]
     offered), so the bound must be stated over THIS tree's fields.  Rule 7: an occurrence
     is a defect relative to its own tree's declaration. *)
  if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.

(** the EXACT size of the initial stack image.  75d69e00: Linux's block runs from the entry
    stack pointer to the stack VMA's end ([Run.length_entry_stack_image_launch]), so the
    size is [top - sp] and nothing else.  PRE-REVISION this computed the block from
    [8 + 8*(argc+1) + 8*(envc+1) + 160] plus the strings and a pad: that arithmetic is
    OBSOLETE, not stale — the 160 was the whole ten-pair auxv, the strings have moved to
    the TOP of the block, and no constant offset from the head reaches them. *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(** the string area holds argv[0] and its NUL, and at least the exec name's NUL.
    Donor: a donor tree
    :projects/boost-beast/http_request/proofs/lib/As/AsanInit.v:52-57, statement and proof. *)
Lemma launch_strings_argv0 : forall (av ev : list (list byte)) (ex : list byte), (0 < length av)%nat ->
  (length (nth 0 av []) + 2 <= launch_string_bytes av ev ex)%nat.
Proof.
  intros [|a t] ev ex H; [cbn in H; lia|].
  unfold launch_string_bytes. cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
Qed.
End FPX1.

(** LPS 727298f3: expressions over the variables below [b] denote alike under valuations
    that agree there.  Text of boost-beast/http_request's As/AsanInit.v (the same lemma). *)
Fixpoint nb_lt0 (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt0 b a && nb_lt0 b c
  | EExt _ _ _ a => nb_lt0 b a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_ev_agree0 : forall b E E' e,
  nb_lt0 b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros b E E' e. induction e; cbn [nb_lt0 edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(* [split_u] sits outside Section Init: its text proof's lia would draw in the section's
   variables, and callers outside the section pass [E] first, as at main. *)
Section SplitU. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma split_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e ->
  bv_unsigned (edenot E b) + k = uE E e.
Proof.
  intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
  pose proof (u64_range (edenot E b)) as Rb.
  rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
  destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
  - rewrite Z.mod_small by lia. reflexivity.
  - exfalso.
    assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
    { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.
End SplitU.

Section Init.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!n8!ovd@1$0$1").
  Variable A : ltac2:(zQ "10!pg8$0").
  Variable ph : ltac2:(zQ "10!ph2$0").
  Variable sp : word.
  Variable rdraw : ltac2:(zQ "10!phe$0").   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : ltac2:(zQ "10!pl6$0").
  Variable stdin : ltac2:(zQ "10!plc$0").
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : ltac2:(zQ "30!n8!nf!q2@1$0@1$2@1$1#k0").
  Variable net : ltac2:(zQ "10!pma$0").
  (* [comment removed for export] *)
  Variable nofile sigmask : word.
  Variable abterm : bool.
  Variable vasz : ltac2:(zQ "10!pn5$0").
  (* [comment removed for export] *)
  Variable urnd : ltac2:(zQ "10!plc$0").
  Variable tmp : ltac2:(zQ "10!pl6$0").
  (* 08b1429/75d69e00: [ProcInput] has twenty fields; the five after in_tmp are taken
     as section variables like the fifteen before them, so [inp] stays the run's own
     input with every field quantified (no literal stands in for a field the published
     statements quantify over). *)
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Variable chrdr sigdfl sigterm : bool.
  (* 75d69e00: the image's ELF entry.  [Run.init_config]'s pc and the auxv's AT_ENTRY
     ([StackLayout.auxv_entries]' third argument, absent pre-revision).  Appended after
     the variables above so that no existing lemma's argument order moves. *)
  Variable apc : N.

  Hypothesis IMG : ltac2:(zQ "10!pne@3$0?4segs?1A?2ph").
  Hypothesis Hsp : ltac2:(zQ "10!pob@1$0?2sp").
  Hypothesis Hbrk : ltac2:(zQ "10!pp6@2$0?4segs?4brk0").
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : ltac2:(zQ "10!pq2@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!pqf@1$0?4envp").
  (* [comment removed for export] *)
  Hypothesis Hfit : ltac2:(zQ "10!prc@3$0?2sp?4argv?4envp").
  (* [comment removed for export] *)
  Hypothesis Huid : ltac2:(zQ "10!pt0@1$0?3uid").
  Hypothesis Hhw : ltac2:(zQ "10!ptb@1$0?2hw").   (* [comment removed for export] *)

  Definition inp : ProcInput :=
    mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp
                     kern execfn chrdr sigdfl sigterm.
  (* 75d69e00: [Run.valid_input]'s launch clause (a name [execve] admits, under E2BIG) and
     [Run.valid_entry]'s fifth conjunct (the start state is exactly a Linux launch).  Both
     are new premises of the revised model and both are discharged by the published
     statements' own hypotheses; neither pins [kb_rseq]. *)
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* LPS 727298f3: the launch's channel reader, [cs_ok]'s [co_rdr] at init *)
  Hypothesis Hrdr : in_channel_reader inp = true.

  Let rseq : bool := kb_rseq kern.
  Let R : Z := rseq_z rseq.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.

  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.
  Lemma la_rseq_eq : la_rseq la = rseq.       Proof. reflexivity. Qed.
  Lemma R_range : 0 <= R <= 1.                Proof. apply rseq_z_range. Qed.

  (* 75d69e00: the mapped image IS Linux's block, sp .. ed_top; [entry_slack] is gone with
     the page tail ([Run.v:1326-1348]).  Pre-revision this was
     [build_stack_bytes ph sp argv envp uid hw rdraw], seven arguments against twelve. *)
  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
  Let SIMG := entry_stack_image inp mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [StackLayout.block_items mod 2]: STACK_ROUND's 8-byte gap, in words *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* C, sp to the top of the AT_RANDOM bytes *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* L, the string bytes with their NULs, the exec file name included *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (* W is repurposed: the [arch_align_stack] pad between the AT_RANDOM bytes and argv[0],
     in BYTES, 0..4110.  Pre-revision it was a word count derived from a head of
     [8*argc + 8*envc + 184], which is OBSOLETE: the strings are now above the pad. *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* argv[0]'s first byte *)
  Let STR0 := usp + CHEAD + W.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 G; Z_to_bv 64 R; gid].
  (* the initial valuation: the fourteen words (eleven before the revision; [gid] is
     [V_GID], index 13), and byte string [K_RND] = the AT_RANDOM draw *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* hidden argument bytes: the argv pointers from argv[2] on, the argv NULL and the envp
     pointer array with its NULL, and the string area, which at this revision is at the TOP
     of the block -- argv[0] at [STR0], up to the stack VMA's end. *)
  Definition argB0 (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 24 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.
  (* ... and above the valuation's own stack pointer *)
  Definition argH0 (E : env) (a : word) : bool :=
    (argB0 a && (uE E e_sp0_early <=? bv_unsigned a))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* ----------------------------------------------------------------------- *)
  (* Layout arithmetic.  Donor for statement AND proof throughout this block:  *)
  (* a donor tree           *)
  (* :projects/boost-beast/http_request/proofs/lib/As/AsanInit.v:177-283.      *)
  (* Constants and addresses are boost-json's own.                            *)
  (* ----------------------------------------------------------------------- *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  (* instantiate the hypotheses a [RefLayout]/[PropExec] lemma's Section discharged.
     Donor: boost-beast@a donor tree:.../As/AsanInit.v:183-190. *)
  Ltac inst_hyps H :=
    repeat match type of H with
           | ?P -> _ =>
               let Hp := fresh "Hp" in
               assert (Hp : P) by first [ assumption | exact Hlo' | exact Hhi' | exact Hlaunch | exact Hlau
                                        | exact Hva | exact Hve ];
               specialize (H Hp); clear Hp
           end.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  Lemma gap_range : 0 <= G <= 1.
  Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  (* C = 8*items + (432 + 32*rseq) + 8*g + 16, with items = argc + envc + 3.
     RULE 12a: run the same derivation over the PRE-REVISION definitions -- a fixed
     auxv_size of 160, no AT_RANDOM block inside the head, no exec name -- and it gives
     8*argc + 8*envc + 24 + 160 = 8*argc + 8*envc + 184, exactly the literal this file
     carried at eight sites.  472 = 24 + 432 + 16. *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * R + 8 * G.
  Proof.
    pose proof (auxv_size_rseq rseq) as HA. fold R in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items. lia.
  Qed.

  (* the rseq-free launch's minimum: chead_eq with R = 0, G = 0 and argc = 1 *)
  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof. pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range. lia. Qed.

  Lemma s0_in_strings : L0 + 2 <= LSTR.
  Proof. unfold LSTR, L0. pose proof (launch_strings_argv0 argv envp execfn Hav0). lia. Qed.

  Lemma lstr_lo : 2 <= LSTR.
  Proof. pose proof s0_in_strings. unfold L0 in *. lia. Qed.

  (* [Run.valid_launch]'s E2BIG half, in this file's names *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (* The pad [arch_align_stack] left: r (0..4095) plus the low-four-bit remainder.
     4110 is taken from the model, not derived from 4095. *)
  Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
  Proof.
    destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    rewrite inp_argv, inp_envp, inp_execfn, inp_rseq in Hslo, Hshi.
    change (ed_top rdraw) with top in Hslo, Hshi.
    fold LSTR in Hslo, Hshi. fold CHEAD in Hslo, Hshi. fold utop usp in Hslo, Hshi.
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR - 4095) 16 ltac:(lia)).
    lia.
  Qed.

  Lemma pad_eq : W = utop - 8 - LSTR - usp - CHEAD.
  Proof.
    pose proof pad_bounds_Z.
    unfold W, block_pad_len, LSTR, CHEAD, utop, usp in *.
    rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma pad_range : 0 <= W <= 4110.
  Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.

  (* the old [W_range], restated: the pad is bounded by the model's own 4110, not by a
     head of [8*argc + 8*envc + 184] it no longer has *)
  Lemma W_range : 0 <= W <= 4110.
  Proof. exact pad_range. Qed.

  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size sp top.
  Proof.
    unfold bsb, stack_image_size.
    exact (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma length_bsb_sum : Z.of_nat (length bsb) = CHEAD + W + LSTR + 8.
  Proof.
    pose proof pad_eq. rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. lia.
  Qed.

  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof.
    unfold usp, bsb.
    exact (entry_stack_image_no_wrap Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
    unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
  Qed.

  Lemma bsb_ge : 8 * argc + 8 * envc + 474 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof R_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (* ----------------------------------------------------------------------- *)
  (* The four AsanPlanSound hypotheses about SINV/argH.                       *)
  (* Donor: the same file, :610-640, statement and proof.                     *)
  (* ----------------------------------------------------------------------- *)

  Lemma argB0_high : forall a, argB0 a = true -> usp <= bv_unsigned a.
  Proof.
    intros a H. unfold argB0 in H. pose proof len_av. pose proof len_ev.
    pose proof chead_range. pose proof pad_range.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold STR0 in H; lia.
  Qed.

  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. apply andb_prop in H as [H _]. apply argB0_high in H.
    destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL. unfold usp in H. lia.
  Qed.

  Lemma argH0_sp0 : forall E a, argH0 E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
  Proof. intros E a H. unfold argH0 in H. apply andb_prop in H as [_ H]. apply Z.leb_le in H. unfold uE in H. exact H. Qed.

  Lemma E_SP0 : AP.expr_vars_lt NX0 e_sp0_early = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. intros E E' a Hag. unfold argH0, uE. rewrite (edenot_agree NX0 E E' e_sp0_early Hag E_SP0). reflexivity. Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M Hag [H1 H2]. split.
    - intros n Hn. rewrite <- (proj1 Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
    - intros a Ha. apply H2. rewrite (argH0_agree E E' a Hag). exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* Donor for statement and proof through to [u_e_atr8]: boost-beast@a donor tree
     :projects/boost-beast/http_request/proofs/lib/As/AsanInit.v:289-441.  Each of these was
     a KReplay whose own term carried the pre-revision 184; a plain-text grep of this file
     could not see it and the compiler could.  Replaced by explicit proofs, never re-encoded. *)
  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge. pose proof len_av. pose proof len_ev. lia. Qed.

  (* the values of the initial variables, as Z.  Two components are new at this revision:
     V_G (the STACK_ROUND gap, in words) and V_R (CONFIG_RSEQ as 0/1). *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 4096
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096
    /\ uE E0 (EVar V_G) = G /\ uE E0 (EVar V_R) = R.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof R_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK V_G V_R].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma uE0_S3 : uE E0 (EVar V_S3) = (usp mod 4096) / 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    unfold uE. cbn [edenot E0 ev nth vals0 V_S3]. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma uE0_envc : uE E0 (EVar V_ENVC) = envc.
  Proof. destruct uE0 as (_ & _ & _ & H & _). exact H. Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma edenot_uid : uid = edenot E0 (EVar V_UID).
  Proof. reflexivity. Qed.

  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma u_e_pg : uE E0 e_pg = pagedown usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_pg, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2. unfold pagedown.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma pagedown_usp : usp - 4080 <= pagedown usp <= usp /\ 0x7fff80000000 <= pagedown usp /\ pagedown usp mod 4096 = 0
                       /\ usp = pagedown usp + 16 * ((usp mod 4096) / 16).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold pagedown.
    lia.
  Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. pose proof uE0_S3 as U3. pose proof u_e_pg as UP.
    pose proof pagedown_usp as (P1 & P2 & P3 & P4).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite UP, U3.
    rewrite (Z.mod_small (16 * _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_S3 as U3.
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* the auxv's size IN BYTES: 27 pairs, or 29 under CONFIG_RSEQ.  New at this revision;
     pre-revision the vector was a fixed 160 and had no expression of its own. *)
  Lemma u_e_auxsz : uE E0 e_auxsz = 432 + 32 * R.
  Proof.
    pose proof R_range. destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9).
    unfold e_auxsz, eaddz, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U9. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* the AT_RANDOM bytes sit [C - 16] above sp.  Pre-revision they were at the TOP of the
     block and [e_str0] was [e_auxv + 160]; both facts are gone with the layout. *)
  Lemma u_e_atrandom : uE E0 e_atrandom = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof gap_range. pose proof chead_eq. pose proof bsb_ge. pose proof length_bsb_sum. pose proof lstr_lo. pose proof pad_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & U8 & _).
    pose proof u_e_auxv as UA. pose proof u_e_auxsz as UZ. unfold e_atrandom, eadd, escale, uE in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UZ, U8. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 e_str0 = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof length_bsb_sum. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA. unfold e_str0, eadd, eaddz, uE, STR0 in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 e_str1 = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof chead_eq. pose proof gap_range. pose proof bsb_ge. pose proof R_range.
    pose proof length_bsb_sum. pose proof lstr_hi. pose proof s0_in_strings.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE, STR0 in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* (e_atrandom - 24 - 432) / 8 as a linear form: the eighth of [e_auxsz]'s variable part
     is [escale 4 (EVar V_R)], so the multiply denotes through [mkMd_denot] and V_R's
     valuation is [uE0]'s last component. *)
  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + 4 * R + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9). pose proof u_sp8 as US.
    unfold e_atr8, eadd, eaddz, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite US, U3, U4, U8, U9. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [Run.init_config]'s model: [State.init_model] at the run stack pointer, with the
     launch's vDSO draw copied in by [State.with_vdso] (new at 75d69e00). *)
  Definition model0 : Model :=
    with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  (* the run's CONFIG_RSEQ as a number.  It is the plan's [r], and it is READ OFF THE
     INPUT rather than chosen, so nothing here pins [kb_rseq]: every value of the flag
     gives its own initial state, and [Run.valid_input] leaves the flag free. *)
  (* the plan's [r] is the section's OWN [R] (= rseq_z rseq, :132), not a second spelling:
     [lia] cannot relate two atoms for the same flag, which cost round
     a farm round. *)
  Let cs0 := init_acs_of R A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* THE LAUNCH'S RESERVED LEDGER is the image's reservations AND the vDSO pair
     ([State.init_reserved]), placed at [State.vdso_top] of the initial ledger.  New at
     75d69e00: pre-revision [vm_reserved] of the initial model was the image's
     reservations alone, which is why this claim had to be restated rather than reproved. *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved kern VTOP.

  (* Ported from boost-beast/http_request's plain-text twin (As/AsanInit.v:473-514), with
     [kb] -> [kern].  boost-json had none of these: it has [RESX] but no shape, no sum and
     no [sum_sizes_app] -- [sum_sizes] is a bare Fixpoint in AsanPlanSound.v:79.  They are
     what [co_totsz] needs now that the ledger carries the vDSO pair:
     [vdso_len_bounds] bounds [vdso_len], not [sum_sizes (vdso_reserved …)], and
     [resx_sum] is the bridge between them (measured at farm/20261106t143...-47195c, whose
     residual was `sum_sizes (vdso_reserved kern VTOP) <= 163840` against a bound reading
     `5 * 4096 <= vdso_len (in_kernel inp) <= 20 * 4096`). *)
  Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
  Proof.
    induction l1 as [|iv l1 IH]; intro l2; cbn [app sum_sizes]; [lia|]. rewrite IH. lia.
  Qed.

  Lemma mb_range : mmap_base_min <= bv_unsigned mbase <= mmap_base_max
                   /\ bv_unsigned mbase mod page_size = 0.
  Proof. destruct Hmb as (Y1 & Y2 & Y3). repeat split; assumption. Qed.

  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (* the pair, for ANY kernel build: four vvar pages, then one to sixteen text pages *)
  Lemma resx_shape :
    RESX = [(Z_to_bv 64 (VTOP - vdso_len kern), Z_to_bv 64 (vdso_vvar_pages * page_size));
            (Z_to_bv 64 (VTOP - vdso_len kern + vdso_vvar_pages * page_size),
             Z_to_bv 64 (vdso_text_pages kern * page_size))].
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof (vdso_len_bounds kern).
    unfold RESX, vdso_reserved. cbv zeta.
    replace (VTOP - vdso_len kern <? page_size) with false
      by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    reflexivity.
  Qed.

  Lemma resx_sum : sum_sizes RESX = vdso_len kern.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (vdso_text_pages_pos kern). pose proof (vdso_text_pages_le kern).
    rewrite resx_shape. cbn [sum_sizes fst snd].
    unfold vdso_len, vdso_vvar_pages, page_size in *.
    rewrite !u64_lit by lia. lia.
  Qed.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  (* the initial ceiling: the launch's alloc_top is sp - 8 MiB.  8388608 is
     [State.stack_max_size] and it did NOT move at this revision. *)
  Lemma TOP0 : TOP model0 = usp - 8388608.
  Proof.
    unfold TOP. change (alloc_top (m_vmmaps model0)) with (bv_unsigned sp - stack_max_size).
    unfold stack_max_size, usp. lia.
  Qed.

  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite TOP0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* 6144513 is [StoreOk.stack_window_depth]: what the 8 MiB leaves below [sp] for the
     largest entry image [StoreOk.stack_window_reach] bounds.  RULE 12h: 8388608 carried
     TWO meanings here and only one moved -- [stack_max_size] is unchanged (see [TOP0]),
     the ZERO-FILLED window below sp is now 6144513, because the entry image itself now
     runs all the way to the stack VMA's end. *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
                 <= bv_unsigned sp + stack_window_reach - stack_max_size)
      by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hlaunch Hlau).
    assert (Hs : stack_to_mem sp bsb a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold bsb. rewrite Hs.
    unfold stack_window_reach, stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    pose proof (stack_window_lo_ge_sp inp sp brk0 mbase rdraw Hlau) as HW.
    assert (Hs : stack_to_mem sp bsb a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold bsb. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. change SIMG with bsb. unfold bsb.
    rewrite <- (rdn_wrap_stack_above segs inp mbase ph entryw sp rdraw a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp in *; lia | apply Hvis; exact Hx].
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma argH0_E0 : forall a : word, argH0 E0 a = argB0 a.
  Proof.
    intros a. unfold argH0. destruct (argB0 a) eqn:Hb; [|reflexivity]. cbn [andb].
    apply Z.leb_le. rewrite e_sp0_early_eq, u_e_sp0. apply argB0_high. exact Hb.
  Qed.

  Lemma argH0_ev0 : forall E a, (forall n, (n < NX0)%nat -> ev E n = ev E0 n) -> argH0 E a = argB0 a.
  Proof.
    intros E a Hev. rewrite <- argH0_E0. unfold argH0, uE, e_sp0_early.
    cbn [edenot]. rewrite (Hev 0%nat) by (unfold NX0; lia). rewrite (Hev 6%nat) by (unfold NX0; lia).
    rewrite (Hev 10%nat) by (unfold NX0; lia).
    reflexivity.
  Qed.

  Lemma argH0_SINV0 : forall E M a, SINV0 E M -> argH0 E a = argB0 a.
  Proof. intros E M a [Hev _]. apply argH0_ev0. exact Hev. Qed.

  (* the hidden set, in the revised geometry: the argv/envp pointer array, and the string
     area, which now runs from STR0 up to the stack VMA's end rather than sitting in the
     middle of the block. *)
  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. rewrite argH0_E0 in H. unfold argB0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (* the VISIBLE part of the block: argc, argv[0] and the sp0+16 word, the auxv, the gap,
     the sixteen random bytes and the [arch_align_stack] pad -- everything between the
     envp NULL and argv[0]. *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 24 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range. pose proof R_range.
    pose proof gap_range. pose proof str0_hi. pose proof lstr_lo. unfold STR0 in *. lia.
  Qed.
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 Mr0 (KWord (SA b k) 8 v).
  Proof.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  (* UNITS.  [AUXW] is the auxv SERIALISED TO WORDS: 2 * auxv_count rseq of them, so 54
     without CONFIG_RSEQ and 58 with.  [auxv_word_ok] below is indexed in WORDS and
     [auxw_ok] in PAIRS; the two sit four lines apart and the bounds differ by more than a
     factor of two.  Pre-revision this read [auxv_words ph (at_random_ptr sp argv envp) uid
     hw] -- FOUR arguments, against eight now -- with a word bound of 20 and a pair bound
     of 9, which is the ten-pair vector. *)
  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* EVERY auxv word, not only the first 52.  The bound WAS `j < 52` -- the 26 pairs that
     sit at the same index under both kernel builds -- which was enough while the plan
     claimed no terminator.  The terminator is now claimed at pair `26 + 2 * r`, i.e. words
     `52 + 4 * r` and `53 + 4 * r`, so the bound has to be the vector's own length.
     `j < 2 * auxv_count (kb_rseq (in_kernel inp))` pins nothing: it is a bound ABOUT the
     flag, not a choice OF it, and the proof below already derived exactly this fact from
     the old numeral.  A fixed widening to `j < 58` would be UNSOUND -- at r = 0 the vector
     is 54 words and [nth 56] is the default, so the conclusion would claim a KWord over
     memory that is not the auxv. *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hjc Hv.
    (* The address arithmetic below needs j's bound as a Z, and it must be the SYMBOLIC
       one: the auxv region is [e_auxsz] = 432 + 32 * R bytes, i.e. 54 + 4 * R words
       ([u_e_auxsz]).  A flat `j < 58` loses the r = 0 case and the lia then fails with
       "Cannot find witness" (a farm round), because at R = 0 the region
       is 432 bytes and word 57 is outside it. *)
    assert (AC : forall b, Z.of_nat (2 * auxv_count b) = 54 + 4 * rseq_z b)
      by (intros [|]; vm_compute; reflexivity).
    assert (Hj : Z.of_nat j < 54 + 4 * R).
    { (* [inp_rseq] is reflexivity, so the two spellings of the flag are one; [AC] is
         COMPUTED per branch rather than left to [cbn], which does not reduce [auxv_count]
         and cost round a farm round. *)
      rewrite inp_rseq in Hjc. pose proof (AC rseq) as ACr.
      first [ unfold R | change R with (rseq_z rseq) ]. lia. }
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
    pose proof lstr_lo. pose proof bsb_ge.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold STR0. lia.
    - rewrite <- Hv.
      (* this fact WAS derived here from the numeral; it is now the lemma's hypothesis *)
      pose proof (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw) as RW. inst_hyps RW.
      exact (RW j Hjc).
  Qed.

  (* PAIRS.  The bound was `0 <= i <= 25` -- pairs 26 and 27 are the rseq pair or AT_NULL,
     and a LITERAL there would pin kb_rseq.  A PARAMETRIC index does not: `26 + 2 * r` is
     the terminator under both builds, so admitting it here claims the same fact of every
     kernel.  [auxv_count b = 27 + 2 * rseq_z b], so the two words of pair i are within the
     vector for every i <= 26 + 2 * r. *)
  Lemma auxw_ok : forall i ty v,
    (0 <= i <= 26 + 2 * R) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    (* ONE atom for the flag: the bound is stated over the section's own [R], and
       [inp_rseq] carries it to the spelling [auxv_word_ok] wants.  Two spellings cost a
       round (a farm round): [lia] cannot relate [RZ] to
       [rseq_z (kb_rseq (in_kernel inp))] when they are distinct atoms. *)
    assert (AC : forall b, Z.of_nat (2 * auxv_count b) = 54 + 4 * rseq_z b)
      by (intros [|]; vm_compute; reflexivity).
    pose proof (AC rseq) as ACr. pose proof R_range.
    assert (HR : R = rseq_z rseq) by reflexivity.
    assert (Hc : (Z.to_nat (2 * i + 1) < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat)
      by (rewrite inp_rseq; lia).
    assert (Hc0 : (Z.to_nat (2 * i) < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat)
      by (rewrite inp_rseq; lia).
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [exact Hc0|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [exact Hc|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* bytes of the zero window below sp, through [Mr0].  6144513, not 8388608 -- see
     [FULL0_below]: the 8 MiB is [stack_max_size] and did not move, the ZERO window did. *)
  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
  Qed.

  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-6144513)) (ELit 6144513))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-6144513)) (ELit 6144513)).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-6144513)) = usp - 6144513).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 6144513) = 6144513) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-6144513)) (elenZ E0 (ELit 6144513))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        pose proof len_av. unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* argv[0] is at the bottom of the string area, [string_base_addr] bytes below the stack
     VMA's end.  Pre-revision it was a constant offset above sp; the revision moved the
     strings to the TOP of the block, which is why this needs a lemma at all. *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof R_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (in_argv inp) with argv. change (in_envp inp) with envp. change (in_execfn inp) with execfn.
    change (kb_rseq (in_kernel inp)) with rseq.
    unfold STR0, CHEAD, W, usp, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 e_str0).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* the word at sp0+16: argv[1] or the argv NULL *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 e_str1).
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof R_range.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U.
          rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
          rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
          change (in_argv inp) with argv. change (in_envp inp) with envp. change (in_execfn inp) with execfn.
          change (kb_rseq (in_kernel inp)) with rseq.
          rewrite U. unfold STR0, CHEAD, W, usp, L0, top, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw) as RW. inst_hyps RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* the AT_RANDOM block is byte string [K_RND] = the draw (faithful, no hypothesis).  At
     this revision the block sits [CHEAD - 16] above sp, inside the head, where before the
     revision it was the LAST thing in the image. *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge. pose proof R_range.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof lstr_lo.
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : 0 <= ak <= 456) by (subst ak; vm_compute; split; discriminate).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    pose proof (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw) as AO. inst_hyps AO.
    destruct AO as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd.
    rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia).
    cbn [rdn] in Hrd.
    change (entry_stack_image inp mbase ph entryw sp rdraw) with bsb in Hrd |- *.
    destruct (stack_to_mem sp bsb (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length bsb)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0' & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  (* 75d69e00: [at_random_ptr] takes the rseq flag -- sp, rseq, argv, envp -- where it
     took three arguments before. *)
  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 e_atrandom.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof gap_range. pose proof R_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge.
    pose proof (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw) as AO. inst_hyps AO.
    destruct AO as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* The rest of the vector ([AsanPlanCore.auxv_rest]), as jsoncons/fuzz_bigint's
     [AsanInitK.v] [auxt_ok] / [auxv_unk_ok] / [auxv_rseq_ok] / [auxv_rest_ok], over this
     unit's [auxv_word_ok] / [auxw_ok]. *)
  Ltac aux_val :=
    unfold AUXW, auxv_words, auxv_entries;
    repeat match goal with
    | |- context [Z.to_nat ?z] =>
        let v := eval vm_compute in (Z.to_nat z) in
        change (Z.to_nat z) with v
    end;
    cbn [flat_map fst snd app nth];
    first [ reflexivity
          | (rewrite edenot_lit; reflexivity)
          | (rewrite edenot_lit; try unfold entryw; rewrite Hapc; reflexivity)
          | fail 0 "AUXVAL" ].

  (* a type word alone (the pairs whose value stays unknown) *)
  Lemma auxt_ok : forall i ty,
    (0 <= i <= 25) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty)).
  Proof.
    intros i ty Hi H1.
    assert (AC : forall b, Z.of_nat (2 * auxv_count b) = 54 + 4 * rseq_z b)
      by (intros [|]; vm_compute; reflexivity).
    pose proof (AC (kb_rseq (in_kernel inp))) as ACr. pose proof (rseq_z_range (kb_rseq (in_kernel inp))).
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
  Qed.

  (* the whole vector is readable ([KUnk]): it is visible block memory below argv[0] *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (432 + 32 * R))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge. pose proof R_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (432 + 32 * R)) = 432 + 32 * R) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold STR0, usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw) by (rewrite u64_lit; unfold usp in *; lia).
    change (entry_stack_image inp mbase ph entryw sp rdraw) with bsb.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* the CONFIG_RSEQ pair (26, 27), claimed only at [R = 1], where it is in the vector *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb R 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    pose proof R_range.
    destruct (la_rseq la) eqn:Hlr;
      [ assert (HR : R = 1) by (unfold R, rseq_z; rewrite <- la_rseq_eq, Hlr; reflexivity)
      | assert (HR : R = 0) by (unfold R, rseq_z; rewrite <- la_rseq_eq, Hlr; reflexivity) ];
      rewrite HR; cbn [Z.eqb Pos.eqb]; [|constructor].
    apply Forall_app; split; apply auxw_ok;
      [ lia | | | lia | | ];
      unfold AUXW, auxv_words, auxv_entries; rewrite ?Hlr;
      repeat match goal with
      | |- context [Z.to_nat ?z] =>
          let v := eval vm_compute in (Z.to_nat z) in
          change (Z.to_nat z) with v
      end;
      cbn [flat_map fst snd app nth];
      first [ reflexivity | (rewrite edenot_lit; reflexivity) | fail 0 "AUXRSEQ" ].
  Qed.

  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest R A).
  Proof.
    pose proof R_range.
    unfold auxv_rest.
    (* AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY, AT_GID, AT_EGID: below the CONFIG_RSEQ pair,
       so the same words under both layouts; AT_ENTRY from [Hapc]; AT_GID/AT_EGID are
       [gid], slot [V_GID] of [vals0] *)
    do 6 (apply Forall_app; split; [ apply auxw_ok; [ lia | aux_val | aux_val ] | ]).
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_cons; [exact auxv_unk_ok|].
    (* the eleven type words *)
    do 11 (apply Forall_cons; [ apply auxt_ok; [ lia | aux_val ] |]).
    apply Forall_nil.
  Qed.

  (* the ranges of [V_G] and [V_R] ([AsanPlanCore.vrows]) *)
  Lemma vrows_ok : know_ok segs E0 Mr0 vrows.
  Proof.
    pose proof gap_range. pose proof R_range.
    destruct uE0 as (_ & _ & _ & _ & _ & _ & _ & UG & UR).
    unfold vrows. apply Forall_cons; [apply kr_ok; rewrite UG; lia|].
    apply Forall_cons; [apply kr_ok; rewrite UR; lia|]. apply Forall_nil.
  Qed.

  (* the 8-aligned shadow word of AT_RANDOM + 8 ([AsanPlanCore.atrm_rows]).  Statements and
     proofs after openssl/hashtable's Common/AsanInit.v [Xsh] .. [e_atr8m2_range], over this
     file's variables (V_S2 is the page index, V_S3 the 16-byte index). *)
  Definition Xsh : Z := argc + envc + 4 * R + G + 2 * ((usp mod 4096) / 16).

  Lemma usp_s3_range : 0 <= usp mod 4096 / 16 < 256.
  Proof.
    pose proof usp_lo. pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)) as B.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.

  Lemma Xsh_range : 1 <= Xsh <= 1024 + 256 + 4 + 1 + 510.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range. pose proof usp_s3_range.
    unfold Xsh. lia.
  Qed.

  Lemma u_e_Xsh : uE E0 e_Xsh = Xsh.
  Proof.
    pose proof Xsh_range. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof R_range.
    pose proof usp_s3_range. pose proof usp_lo. pose proof usp_hi.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9). pose proof uE0_S3 as U10.
    unfold e_Xsh, Xsh, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U3, U4, U8, U9, U10.
    set (u := usp mod 4096 / 16) in *. clearbody u.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_Xm2 : uE E0 e_Xm2 = (Xsh + 2) - (Xsh + 2) mod 8.
  Proof.
    pose proof Xsh_range. pose proof u_e_Xsh as UX. unfold uE in *.
    unfold e_Xm2, eaddz. rewrite !mkAlu_denot, !edenot_lit. rewrite u_and64, u_add64. rewrite UX.
    change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
    rewrite (Z.mod_small (Xsh + 2)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3)%Z by reflexivity. rewrite land_highmask by lia. reflexivity.
  Qed.

  Lemma u_e_atr8m2 : uE E0 e_atr8m2 = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + ((Xsh + 2) - (Xsh + 2) mod 8).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof Xsh_range. pose proof (Z.mod_pos_bound (Xsh + 2) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)).
    assert (usp / 32768 <= 2 ^ 32) by (apply Z.div_le_upper_bound; lia). pose proof (Z.div_pos usp 32768 ltac:(lia) ltac:(lia)).
    assert (0 <= (usp mod 32768) / 4096 < 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct uE0 as (U1 & U2 & _). pose proof u_e_Xm2 as UM. unfold uE in *.
    unfold e_atr8m2, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, UM.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* The bound is the launch's: the AT_RANDOM block ends below 2^47 ([usp_fit]), so
     atr8 <= 2^44 - 61 and the word, a multiple of 8 at most atr8 + 2, is at most
     0xFFFFFFFFFC0; from below, sp >= 0x7fff80000000. *)
  Lemma e_atr8m2_range : 0xFFFF0000000 <= uE E0 e_atr8m2 <= 0xFFFFFFFFFC0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof pad_range.
    pose proof lstr_lo. pose proof usp_s3_range. pose proof Xsh_range as XR.
    assert (D8 : usp / 8 = 4096 * (usp / 32768) + 512 * ((usp mod 32768) / 4096) + 2 * ((usp mod 4096) / 16)) by lia.
    assert (E8 : usp = 8 * (usp / 8)) by lia.
    rewrite u_e_atr8m2.
    pose proof (Z.div_mod (Xsh + 2) 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound (Xsh + 2) 8 ltac:(lia)) as M6.
    set (m := (Xsh + 2) mod 8) in *. set (q := (Xsh + 2) / 8) in *.
    set (s1 := usp / 32768) in *. set (p := (usp mod 32768) / 4096) in *. set (s3 := (usp mod 4096) / 16) in *.
    unfold Xsh in *. lia.
  Qed.

  Lemma atrm_rows_ok : know_ok segs E0 Mr0 atrm_rows.
  Proof. unfold atrm_rows. apply Forall_cons; [apply kr_ok; exact e_atr8m2_range | apply Forall_nil]. Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with R atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof R_range. pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    (* [auxv_rest] is proved apart ([auxv_rest_ok]); hiding it keeps the [Forall_app]
       splits below from opening it *)
    remember (auxv_rest R A) as REST eqn:EREST.
    remember vrows as VR eqn:EVR.
    remember atrm_rows as AM eqn:EAM.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    (* boost-json's own [init_kn_with] orders its KRange rows differently from the donor's,
       so the bullets are matched to the GOAL rather than to a fixed position.  Each branch
       still ends in [lia] on the goal's own bound, which [kr_ok] fixes from the goal, so a
       wrong rewrite cannot close a row -- it can only fail. *)
    { repeat (apply Forall_cons;
        [ first [ exact SW1 | exact SW2 | exact argc_word_ok | exact argv0_word_ok | exact argv1_word_ok
                | cbn [kentry_ok]; change (edenot E0 (EVar V_HW)) with hw;
                  destruct Hhw as [Eh|Eh]; apply (f_equal bv_unsigned) in Eh; rewrite Eh;
                  unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite u64_lit by lia; lia
                | apply kr_ok;
                  first [ rewrite U1 | rewrite U2 | rewrite U3 | rewrite U4 | rewrite U5
                        | rewrite U6 | rewrite U7 | rewrite U8 | rewrite U9
                        | rewrite uE0_S3 | rewrite uE0_L1 | rewrite uE0_uid
                        | rewrite u_e_atr8 | rewrite u_e_sp0 | rewrite u_sp8
                        | rewrite u_e_pg
                        | unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as UU; unfold uE in UU; rewrite UU;
                          rewrite Z.mod_small by lia
                        | idtac ];
                  try pose proof pagedown_usp; try pose proof L1_range;
                  try (unfold valid_id in Huid; pose proof (u64_range uid));
                  unfold BRK_ASLR in *; lia ] | ]);
      (* The five rows this leaves are the two stack-window rows and the three KWord rows
         (argc, str0, argv1).  The window rows WERE `KWr/KZero (SA e_sp0 (-8388608))
         (ELit 8388608)`, which is FALSE at 75d69e00: [FULL0_below] proves zeroes only down
         to [usp - 6144513] ([StoreOk.stack_window_depth]), because the entry image now
         runs to the stack VMA's end.  AsanPlanCore's [init_kn_with] carries 6144513 and
         they close; the three KWord rows match by construction. *)
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* the rest of the vector, proved apart; closed here, before the generic steps below
       (their [vm_compute] fallbacks must not see it) *)
    all: try (rewrite EREST; exact auxv_rest_ok).
    all: try (rewrite EVR; exact vrows_ok).
    all: try (rewrite EAM; exact atrm_rows_ok).
    (* [auxw_ok]'s bound is now `0 <= i <= 26 + 2 * r`, so [lia] needs the flag's range *)
    pose proof R_range.
    (* THE TERMINATOR ROW IS DONE FIRST, and its [R] is fixed BEFORE anything unfolds.
       Doing it with the other nine does not work: the generic branch unfolds
       [auxv_words], which expands [R] into raw positive arithmetic on [kern], after
       which no rewrite of [R] can fire -- measured twice (a farm round,
       …125715z-b8a7da, four unreadable residual goals each).  [R] is a Z with
       [R_range : 0 <= R <= 1], so case on its VALUE: that touches neither [kern] nor any
       Let built from it, and BOTH branches are discharged, which is the parametric form
       rule 12k permits and not a pin. *)
    (* [apply auxw_ok] FIRST, so the bound goal stays `0 <= 26 + 2 * R <= 26 + 2 * R` and
       closes from [R_range] alone.  Rewriting [R] before the apply left the bound as
       `0 <= 26 + 2 * 1 <= 26 + 2 * R` -- the lemma's own [R] is not the goal's -- and no
       later rewrite reached it (a farm round). *)
    10: apply auxw_ok;
        [ lia
        | (* ONE case split, on [la_rseq la], with [R]'s value DERIVED from it.  Casing on
             [R] and on the vector's own branch separately produced four combinations, two
             of them contradictory (R = 0 with la_rseq true), and those two are genuinely
             unprovable goals: with the flag set the terminator is at pair 28, not 26
             (a farm round).  [la_rseq la] is also the safe term to case on
             -- the section's Lets are built from [kb_rseq kern], which is syntactically
             different, so nothing is re-abstracted and the "R is already used" clash does
             not arise.  Both branches are discharged, so this is rule 12k's parametric
             form and not a pin. *)
          destruct (la_rseq la) eqn:Hlr;
          [ assert (HR : R = 1) by (unfold R, rseq_z; rewrite <- la_rseq_eq, Hlr; reflexivity)
          | assert (HR : R = 0) by (unfold R, rseq_z; rewrite <- la_rseq_eq, Hlr; reflexivity) ];
          rewrite HR;
          unfold AUXW, auxv_words, auxv_entries;
          rewrite ?Hlr;
          (* [cbn] with a whitelist gets STUCK part-way through [Z.to_nat (2 * (26 + 2*1))]
             and prints raw positive fix-points; [vm_compute] on the closed index does not.
             Same step, and same reason, as the generic block below. *)
          repeat match goal with
          | |- context [Z.to_nat ?z] =>
              let v := eval vm_compute in (Z.to_nat z) in
              change (Z.to_nat z) with v
          end;
          cbn [flat_map fst snd app nth fst snd];
          first [ reflexivity
                | rewrite edenot_lit; reflexivity
                | vm_compute; reflexivity
                | idtac ] .. ].
    1-9: apply auxw_ok;
         [ pose proof R_range; lia
         | (* The index must reduce BEFORE the row is selected: the probe showed the goal
              stuck at `match Z.to_nat (2 * 0) with | 0%nat => AT_SYSINFO_EHDR | ...`, i.e.
              [auxv_entries] selecting on an UNREDUCED index.  The previous attempt put the
              index [cbn] BEFORE the unfold, where [Z.to_nat (2 * i)] is still hidden inside
              the folded [AUXW]/[auxv_words], so it reduced nothing.  Unfold first. *)
           unfold AUXW, auxv_words, auxv_entries;
           cbn [Z.to_nat Z.mul Pos.mul Pos.to_nat Pos.iter_op Nat.add Nat.mul];
           cbn [flat_map fst snd app nth];
           try reflexivity .. ].
    (* Whatever branch leaves them, reduce every CLOSED [Z.to_nat] index to a literal and
       let [auxv_entries] select its row.  A whitelist [cbn] does NOT get through
       [Z.to_nat (2 * i)] -- two rounds (1adfea, and the ordering fix before it) proved
       that -- but [vm_compute] on the closed index does, and it touches nothing else
       because the [change] is guarded by the match. *)
    all: repeat match goal with
         | |- context [Z.to_nat ?z] =>
             let v := eval vm_compute in (Z.to_nat z) in
             change (Z.to_nat z) with v
         end.
    all: try (cbn [auxv_entries]; try reflexivity).

    (* The residual value goals are matched to the GOAL, not to a position: boost-json's
       own auxw row set differs from the donor's nine, so `1:` indices do not transfer.
       Every branch ends in [reflexivity] on a closed goal, so a wrong branch cannot
       close the wrong row. *)
    all: try (rewrite edenot_lit; reflexivity).
    all: try (rewrite edenot_lit, P1; reflexivity).
    all: try (rewrite edenot_lit, P2; reflexivity).
    all: try (rewrite edenot_lit, P3; reflexivity).
    all: try exact atr_ptr_eq.
    all: try exact Hatr.
    all: try exact kimg_ok.
    all: try exact rw_window_ok.
    all: try apply Forall_nil.
    (* The tail block [atr; KImg …; KWr …] arrives as ONE Forall over three rows, so the
       `exact` lines above never see it: split it first, and let each row pick its own
       fact.  A wrong pick cannot close a row -- [exact] fails on it. *)
    all: repeat (apply Forall_cons;
                 [ first [ exact Hatr | exact kimg_ok | exact rw_window_ok ] | ]).
    all: try apply Forall_nil.
    all: repeat match goal with
         | |- context [Z.to_nat ?z] =>
             let v := eval vm_compute in (Z.to_nat z) in
             change (Z.to_nat z) with v
         end.
    all: try (cbn [auxv_entries]; try reflexivity).
    all: try (unfold AUXW, auxv_words, auxv_entries;
              cbn [flat_map fst snd app nth]; try reflexivity).
    (* The terminator's four residual goals: the tail of the vector still branches on
       [la_rseq la], so the [nth] cannot pick a row until that is decided.  Casing on
       THAT term is safe where casing on [rseq] was not: the section's Lets are built
       from [kb_rseq kern], a syntactically different term, so nothing is re-abstracted
       and the "R is already used" clash does not arise.  Both branches are discharged. *)
    all: try (destruct (la_rseq la); cbn [nth flat_map app fst snd];
              first [ reflexivity
                    | rewrite edenot_lit; reflexivity
                    | vm_compute; reflexivity ]).
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn R A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma init_regs_nth : ltac2:(zQ "90!nq8!hrd!nv3!hs4!jod!hu1!lp2!nvb!iue>1n$3@3$4$0@4$5$0^1$7@1$2ZM1\0$1$0@2$8^1N2$6@1$2Z").
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  Lemma init_regs_ok : ltac2:(zQ "40!js1!og8!nvb!ol5@3$3$0$2$1").
  Proof.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_stk : ltac2:(zQ "70!jod!h9!js1!om0!lo6!jma!hi4@3$0$1@2$5$2$3@2$6@1$4?3usp+ogggg0").
  Proof.
    pose proof pagedown_usp as (P1 & P2 & P3 & P4). pose proof usp_hi. unfold e_stk, eaddz, uE. rewrite mkAlu_denot, edenot_lit, u_add64.
    pose proof u_e_pg as U. unfold uE in U. rewrite U.
    rewrite Z_to_bv_unsigned. change (bv_wrap 64 (-8388608)) with (2 ^ 64 - 8388608).
    replace (pagedown usp + (2 ^ 64 - 8388608)) with ((pagedown usp - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
  Lemma u_e_stklen : ltac2:(zQ "80!jod!h9!js1!om9!lo6!jma!rf!hi4@3$0$1@2$5$2$3@2$7@2$6+ogggggggggg0+ogggg0@1$4?3usp").
  Proof.
    pose proof pagedown_usp as (P1 & P2 & P3 & P4). pose proof usp_hi. unfold e_stklen, esub, uE. rewrite mkAlu_denot, edenot_lit, u_sub64.
    pose proof u_e_pg as U. unfold uE in U. rewrite U. rewrite u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (pagedown usp - 8388608), pageup ((pagedown usp - 8388608) + (0x800000000000 + 8388608 - pagedown usp)));
     (pagedown (shadow_off A + (pagedown usp - 8388608) / 8), pageup (shadow_off A + ((pagedown usp - 8388608) + (0x800000000000 + 8388608 - pagedown usp)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_e_stk, !u_e_stklen.
    unfold uE. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost STKLEN_MAX
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost STKLEN_MAX <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_hi.
    pose proof pagedown_usp as (Q1 & Q2 & Q3 & Q4).
    rewrite allowA_init. set (pu := pagedown usp) in *. cbn [A_bytes fst snd]. unfold vis_cost, STKLEN_MAX, CEIL, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (pu - 8388608 + (0x800000000000 + 8388608 - pu)) with 0x800000000000 by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    rewrite (P2 0x800000000000 eq_refl).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (pu - 8388608) / 8) (shadow_off A + 0x800000000000 / 8) ltac:(lia)).
    assert (pu - 8388608 - 4096 < pagedown (pu - 8388608) <= pu - 8388608) by (unfold pagedown; lia).
    split; lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 (in_fs inp) E0 cs0 R0 FULL0 model0.
    Proof.
      destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
      pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
      destruct abytes_init as [AB1 AB2].
      constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_vmops];
        rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
      - exact init_regs_ok.
      - reflexivity.
      - exact init_kn_ok.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - intros _; reflexivity.
      - (* co_res, boost-json's OWN shape: a single existential over the kernel build.
           boost-beast discharges three fields here through [if_resx]/RESX, which does not
           port -- boost-json's atable has neither [n_resx] nor [p_resx] (AsanInit.v:43-49)
           -- and no tree on the shared branch carries this widened [co_res], so this one
           bullet is written rather than ported.  [State.vm_reserved_init_model] (SHIPPED,
           75d69e00:theories/LinuxProcessSem/State.v:7844) states exactly the ledger, and
           [kb] stays EXISTENTIAL so no kernel field is pinned. *)
        exists (in_kernel inp). split.
        + exact (vm_reserved_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).
        + (* LPS 727298f3 port: [co_res]'s mmap-base conjunct, the launch's [mbase] by
             [mb_range] ([Run.valid_mmap_base] through the section's [Hmb]); and the
             launch's mapping list is empty, so every mapping is apart from the ledger. *)
          split.
          * apply (Z.le_trans _ (bv_unsigned mbase) _); [exact (proj1 (proj1 mb_range)) |].
            apply Z.eq_le_incl. reflexivity.
          * split; [apply Forall_nil|].
            (* the pair is the ledger's suffix at the launch *)
            intros x Hx.
            eapply (eq_ind_r (fun l => In x l));
              [| exact (vm_reserved_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)].
            apply in_or_app. right. exact Hx.
      - reflexivity.
      - reflexivity.
      - constructor.
      - apply seps_nil.
      - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
        exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp Hsp).
      - constructor.
      - constructor.
      - rewrite TOP0. pose proof usp_lo. pose proof usp_hi. unfold CEIL, CEILMAX. lia.
      - rewrite TOP0. pose proof u_e_sp0 as U. unfold uE in U. rewrite e_sp0_early_eq, U. reflexivity.
      - intros z Hz. exact Hz.
      - constructor.
      - constructor.
      - (* co_totsz.  [if_sizes] gives the image half EXACTLY, and the vDSO half is bounded
           by [State.vdso_len_bounds]: two intervals of at most twenty pages, so at most
           2 * 20 * 4096 = 163840 bytes -- which is the budget [init_acs_of_with] now
           carries.  The donor routes this through RESX/[resx_sum] off an [n_resx]/[p_resx]
           field boost-json's [atable] does not have, so the instance is taken directly. *)
        (* [resx_sum] turns the ledger's vDSO half into [vdso_len kern], which is exactly
           what [State.vdso_len_bounds] bounds -- at most twenty pages, 81920 bytes, well
           inside the 163840-byte budget (two intervals of twenty pages) that
           [init_acs_of_with] now carries. *)
        rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
        pose proof (vdso_len_bounds kern) as VB. unfold page_size in VB. lia.
      - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
        destruct uE0 as (_ & _ & _ & _ & _ & _ & U7 & _). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
        rewrite Z.mod_small by lia. lia.
      - lia.
      - lia.
      - exact AB1.
      - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
      - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
      - split; [intros; reflexivity | intros; reflexivity].
      - split; reflexivity.
      - exact Hrdr.
    Qed.

  (* [comment removed for export] *)
  (* [Run.init_config] is the configuration [cs_ok] speaks about.  [apc] is now a section
     variable (it is also the auxv's AT_ENTRY), so the statement no longer quantifies it
     here; [Hapc] ties it to the table's [a_entry]. *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp
    = @cfg_of fx0 segs R0 (a_entry A) FULL0 model0.
  Proof.
    (* [R0] and [model0] must be unfolded here, unlike in boost-beast's twin: the residual
       mismatch with the donor's shorter list was EXACTLY those two, folded on the left and
       expanded on the right (a farm round).
       THE FPState IS [fx0], THE CONCRETE ONE, NOT THIS SECTION'S ABSTRACT [fx].
       `PropExec.v:51` defines `fx0 : FPState` as a global, and `init_mkst`
       (`PropExec.v:2033`) states `init_machine_state … = @mkst fx0 …` at it -- so the
       left-hand side is at [fx0] by construction and nothing on this side can move it.
       Resolving [cfg_of] to the Section's abstract [fx] is what left the two sides
       identical except for `@mkst fx` against `@mkst fx0` through five attempts
       (rewrite, erewrite, `(fx := fx)`, `@init_mkst fx`, `@cfg_of fx`:
       a farm round, …152100z-0e980e, …153236z-d07422, …154336z-dbf4e0). *)
    unfold init_config, cfg_of, FULL0, entryw, R0, model0.
    rewrite init_mkst, Hapc. reflexivity.
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* LPS 727298f3: what [SINV0] gives the main phase (the AsanInitP.SINVm lemmas). *)
  (* Text of boost-beast/http_request's As/AsanInit.v (str0_cat,              *)
  (* SINV0_vals_E0, SINV0_sp0_E0), at this unit's names.                       *)
  (* ----------------------------------------------------------------------- *)

  (** [STR0] ([usp + C + pad]) is [CatExec]'s [usp + cat_string_off] *)
  Lemma str0_cat : STR0 = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof. unfold STR0, CHEAD, W, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  Lemma SINV0_vals_E0 : forall E M, SINV0 E M ->
    uE E e_envp = usp + 8 * argc + 16 /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E e_str0 = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof.
    intros E M [Hev _].
    pose proof u_e_envp as U1. pose proof u_e_str0 as U3. pose proof uE0_envc as U2. unfold uE in U1, U2, U3.
    unfold uE. rewrite (edenot_ev_agree0 NX0 E E0 e_envp eq_refl Hev), (edenot_ev_agree0 NX0 E E0 e_str0 eq_refl Hev).
    split; [exact U1|]. split; [| rewrite U3; exact str0_cat].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree0 NX0 E E0 (EVar V_ENVC) eq_refl Hev).
    apply bv_eq. rewrite U2. pose proof len_ev. unfold envc in *. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_sp0_E0 : forall E M, SINV0 E M -> uE E e_sp0_early = usp.
  Proof.
    intros E M [Hev _]. rewrite e_sp0_early_eq. unfold uE.
    rewrite (edenot_ev_agree0 NX0 E E0 e_sp0 eq_refl Hev). exact u_e_sp0.
  Qed.
End Init.
(* [comment removed for export] *)
