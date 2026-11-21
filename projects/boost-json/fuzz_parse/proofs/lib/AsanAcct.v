(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the system-call robustness premise (sys_rob). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg CatSim PropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsanAcct () := KReplay.lz_vm "#&-tC47Corelib7Classes?Relation!s6&9Reflexive!sR-Program6Basics4flipC46Stdlib5Lists4!s+#2hdK!s[,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!tt#s2bv00I!sg+4Init5Logic2eq00C!sc@;bv_unsigned!sPA5bv_eqC5!u[&6ZArith6BinInt1Z6of_nat!sF<3ad!t/B7Z_to_bv!sLBbv_wrap!sLAD!uM-_in_range!sYA=!t#&_small!u><7add_0_rC!w778eq_ind!sD#!t9?@!u`&!tq+c79OSSVerify6Proofs:boost_json:fuzz_parse3lib8AsanAcct4woffC13~~~!y{G3I!y{?!yX93and!sA/!s_4Z00K!s_19Datatypes3nat01K!sc?!sDA2K!{_D1!w0A6bv_add!tqA2!sjA4BvWf!sIA:bv_modulus!|/=!sG$oK!}_;1!yh9iff_refl!#3d'9micromega;Zify!#4S%3inj!sIB5mkre!{?44Znat5Nat2Z9is_nonneg!u;<2le!vj<4list01I!sFA0K!tt56VarMap1t!x`#!sD>1!sD@3I!sD?0!sD6=RingM!s4'7Formula!tq87Env!sT#5PExpr!tv8!sI21!sIE3K!tbL!st75Tauto8G!sJ'4C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!vm<4find!sqAC!sq0_sou!sX8!z^/;rew_!{U%vC3!|}%7tactics<f_equal_hel!#<W+!{%+divAZplus!}<#_idemp_l!}iA?!~x%!#;C,!tk@5mkapp!sKB6!sK$2I!#3t?0!}8>8inj_succ!#3+74True01!tS68!tS#Inst7Inj_Z_ZI!wc@;!tG%!#9_#00!yL<5eKind!~-=uni!~-9!se%4kind!zw8!{J13Op2!#8W-!t58!#3]=bool!#9|=!sF%1!#<QX<!#>w#_avoids!#<Y$!#7M2Peano2lt!#62=t!tk<6op!zL#!#3V7!~=38!u9Y6woff_0!u39!yn$6!#@D$!zV>6!zV#!u=>!w&%2!xYI3!sMI5!|{B7!#35%!v4Y9!v4$!|y#!v7%!yu=prod!yu?!sF$1!#Is7In!z4_s!z5%!tn8!x#%5False!tk?!#<a#2!xd87!#6Q%!#JX8or!~w#ELinuxProcessSemantics5Riscv7Prelude5bvmap!#G5;transI!sp:?!s<2>!t$$!sE+=ac!s?#_report!#Ey3!|U5!u%<!t7B>ms_svc_pending!t}[machine_state!t[\5ms_pc!scZ6ms_mem!z6Y;munrestrict!#36&!tTI2Fs4path!sVN2FsC!x>;3!#<Z#!sqI5S!w4#7PipeBuf!#LwF!#8ZY9m!v:2!slPPropExec4mks!v{+!#3:'!|<#HFunc!{,#alExtens!s1$ityIf!s?+_e!s@0!u?Y8!u>1!skY:!yA3K!|Ch!wbZE!zx-_m!{&Y!tg27ms_regs!seZ8ms_f!sf^9!~d$_val!u6`sv!se^fcsr!#46]rom!x<[!x:,!y}3!#A;Yhclean!#A;Asy!u#ZB!t,%_!u,+!#=M&!suYC!sn+!#76Z<MemImageType<seg_readable!shX9!sh#bytes!seX8!se$ase!#GJ;4of_N!#ar<sub!sa=to!sa/N!sD+Nat1N6to!#bu#!{+YBsegment!v\$!uwQ!sp2<find_!su&!sjZ;memory!t[$I!wNW7S!tN%!#D`=!#B$&1!trZ=ov!vK-!#LDE3!#RI7!#bV#!#8ZYC!vE-1_hidde!~W?9!#Gk#_in!#e\YA!#P1-_con!#P68!w%,7nat_!#S_4!#U:-0!~F]writ!~FO!x-2?!{X'!x-#_!|G\5wview!voY>!sb$_!#=[g8store_ok!wT<6leng!#F7L!~53!w5#e_to!#HC\?!yV0h!#9/_!sr1tl!vZA!#O-06!#r>#!#6f<3!sC?6eqb_eq!w+<8lis!{[$C8!uNN3Lib2Nd9ex_elimF1!uF&!tq<leb!tQ<4andb!#HA'4Bool!s'$=!s>#_true_iff!uX=leb_!#it3!#S4+1!s@<2!ujW:and!uk%3!#>8]!#<g#size!#5P73not!v/6>!v/$f!#5l$!v0Cgt!#[}73N!#me-!{3YF!#;y-!sp#e_spec!xrCpow!~'ZA!vL#!#:^/!t4<>pow_po!#p>C:!sN#!sJ%!#^4C5Psatz!#_+E!sO&6K!#fcL2!#HWYin!wG-t!#<;/!#oED7!#>=E5!#xO?3!t3>3Pol!#h+E!vK&4!vKN1!|zX>!yT#execu!#<n#!{Zgsom!{Z04!|x67N_nat_Z!t>YJ!{Y4!#<fh<code!s|%ov!#79<negb!t0K6BvBa!u5#e4!{3Z!tb/!u]i=fetch_wor!u^%!u@S2!tFahalf!tFN!sk2:!sk,!zk[!tT/!vpi>!sz-any!#@IH4bits!#x=@9bv_concat!ubYG!tf1!ucptail!s{#!#5a=N01!#hcY>!#_F&resul!#Oa#!snh!zy[@!uj%!#J}#trap!#g'=orb!t{j3!|vafailure!$;j9x!vr=!ze%3Sem3eff01!uEj!#RwY@!#s]-_nil!#=_&!uM:1!uMJ2!sNJ3!sNJ4!sNJ5!sNJ6!sNJ7!y<Z;width!#[eP!#8R%@le!#<e%to!#9=#!tQZCinterp_eff_!#v3$!#]@\!#vs%valu!#VD[!tR&d!$Ao$s!#9VY!#@#>!#n,Z!#yI01!#[:^!|X'!#[:+!z#J!$'PYA!#Ws&!#9tY!z2&D!#X@$_!$Ds#!z>'!sjR=!sc0!#BnY!#Y2-_!#lTfC!sx0!#a00!w_C7!|I#!$:5#!$C/BextractI!syD4core00I!y'I!#~mZ=!#cu%!{?%!skZDde!#GD#exec!#3Gb8is_ecall!#CCAD!tA$C:!tI&!#CtC!vH#6c!#w:?!x=-c!#v|@!wl/!$&L=!tH2!#vL<!sO0!#v6>!us1Bis_!yu$ed_illegalK!ynJ1!#aYZ!#sb&!#ui-!srYL!#9l5!#G@h6!#|k$!x+F!zp#!|pA5Instr5i!s+#!|t]step!|$c:!#P=+!w7Y;!x'+pc!x#_F!#Qn/!#6zgG!#L:0!szhF!#HM/!syhM!#5?6!zri4!y9#!tdYI!xF+!$-E,!}UdF!zr0!v]h:eager_used!vJQ!$6d$Am_vm_materialized!#fF<mulI!t'P5Model!~@M!s\%9page!#jB#!#@TYsame_but!uM1!#EzO!u601!s\Q7VmS!$5P$!unR!wQ$lazy!s^Q?with!sa#back!$@zM!t|&Fd!t|%0I!u\Y!s^SIo!s^YFs!s^X9!s7#!s`X8Li!uYY9Time!s`X6VmMaps!|@S4m_fd!sYQ8!z'#m!#[3#!t8Rio!sYQ6m_fsys!s[Tproc!s[Q5m_lim!t7Ttime!t7Tfd!uHR7m_pipe!s\Ustdin!x~Us!x~Thalted!v$Tti!sZR=m_rlimit_core!v-Tclock!#5:SEntry!}ES;InputStream!$`t4!#;_+div!#vWE7!sg<7di!$n+#!#;6X4A_wf!#?%^7A_pages!sjb!#W\$!sj$!#en+!$Y3$7!s+#Def6Foral!#>P#!#ch/3Nat3ad!uwZ>Zmod0_multiple!#A=&!wW49SatDivModCZ!$g}#!#~E$!#~pB=!sQ#pos_b!$ii#!sM@!su#!sM15!tI$8PreO!s/#1Z;!x[#0_r_ext!sL>!st#!sL3!tA3<eq_deci!$D5#!#~<D4!$+g<!$B2$!#}QJ7!sOK5!$,a75Z2Nat2id!{wBu!$}J<?mul!$l[#distr_r!t69!$cp#7inj_!%$9#!w2'!$`^+:!#__%seq!sE?!$^L#!sE=!$X%#!#pA:fst!sC=sndC!|9:3s!$6{-!sB2map!x]E5!#4BE6!}$Y=!#Hq#allowedb!}#2!$3~+<or!$7-,!v`67ex!s2#b!v|8in!w?#!sa#!#rE2!$kg%e!$oP,!s_-6!$/I#q!$h;A9and_morph!y{<8max!$'s$!t469in_or!xj$!#MG<ax!tT6!$r9'@!%0/$_!}3%!%0Y5!$kv3!$N,+5!sG$8!v$$Na!#6?'!tx78!vd#consI!sC65NoDup!$rR,!sB51!sB>2!v98!sB$!$HN\E!sf%!u,#!%4:-!#S'^!#;$%_in!zk2!u,-4incl!s?7A!uF'cl_!~Q%!$4%M3!#:rY!u$'!$FK%!u+&!$#u'!%:89=eq_Tran!$dF$C5!sV+!$$E%6PosDef3Pos3mul!sw59M!{y#isms:re!{b#tf!sM7!tF3<eq_!%;[6!s|4Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!s\??eq!sK#per!sRE@!s~0per!sS?M!$oj#_co_!$vg#v_impl!#3T$ism!#?aBdiv!#?aI!#;N#!~5/!~w+div?!#@S$!%%[#full!#GpP!#Y\$!$Za#!s^P<!s^+_o!#7z+;setoid_ring6Nc!s,#>!s'#!#Bs#_com!#5|=o!%&d,!sn/>!sn%_!#rH#al4Zops!sOG2Zr!}&Ztwo64_as!#G5-!wA8:!wA%!uS#!#94=ul!up#m!sh8AZ!v8$!sl#!#@Q$!x,R8!wM$mem!#4_6>!#<E%_!s-%!tq=eqb!%9A%!#M,O!tJ$insert!s`Q@!#~&%!#51$acc!woYA!tO-_nodup!#d%V>!#e^'!t]$!#fPY!uH3!t^/!zEZ!uT/i!#h>_C!tl4!#;G'!$QxVex_intro!$Qx&!#<{Ylazy_cover!w}WHnewly!#fZ/!}f&!{p66filt!%:W,!#@4-!sA%_I!#YSQ!we'!$/o_A!z:1!xUbD!st2!{y0!up5<!#@^$!uv%!#C%Y!#4,&!$VT%no!zicD!#9N-_al!#Cz,!$\P_3!}Ae!tc$!%Mp+!#7OQv!#bt#i!$E|YE!#qV3_wvb!uJ_=!#m}'!spc>!#t%+!sqc<!#h]&!so,k!soX4MInv0!$b5%i!si^0!x[WJ!wo-_model!$$/,!#415!}?%!%Du-!#Pp1app_or!#8KZ!#TN$!~s&!#],$!uKV?!#sa+!xZ$!t\Y8!vt#!y=cE!tY2_spli!#|,_?new!v?&props!#3x\!$f^+5!t__7nod!$oE#!wpP3Run?mi!z+#ount_!$%/\F!{%/!$$/&!#T+`C!$%+#!$%|'s!zG-!svO4Scfg8the_scfg!sg%K!v>N6config!$S~L!s[#9s!u3$cfg!#w;L!s^#=!s^+_sub!t@O5!s`$!$U+L!sZ#7!t;$to!$#YL!uR%ys_inpu!#I<QGsyscall_effect!$6BS!tJ#<apply!sh&!#<@Qm_kill!#tYNpecs<!u+'spec!$+6Qevent!$RL<!s\@4!s\LMonad7outcome!$T2<!s^B!xqP@advance_past_svcI!|_V0I!ziW!{GY2!#whP=S!xc%E!y~$!#xNR!x0&0!#FPY!$0f1_same!#4eT!#40,!$DOZ!sh%!$Ae#_de!#;v_J!#9[1!#8q3I!s}O6CatSim6m!sq#s!#BR&!thY;!t]$!%=l/!tYV:!tY%!$PF#!vE_!$9:7!#Yb$!#<8^!$?3,!$>;fD!#='+!%RJ+!sw_K!un9fr!{a+!s~p!#e]#!s~_F!%JC-!%E/h>!sy/em!sq_E!#D:#!}n%!#Bih=!{E&!$P8dDrz_!ss&!tiiB!#6,2!%GX`@wx_segs_no!%}Z#!#K>_7seg_to!#YJ=7f!$-X#b!%0e8!#{E#!#me<Diff!#mY$subr!#ph&!#fW6!t4&_!s-%!z_Z!v81!uJ%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionk14boolk14None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsn0dmachine_staten0h3Build_machine_staten07ms_fcsrn08ms_fregsn06ms_memn09ms_pc_valn07ms_regsn07ms_resvn06ms_romn0ems_svc_pending79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct4FPX1~~~~~~hi69mrestricthi6bmunrestrictk14list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeho97Segment37Corelib4Init5Logichs92eqk14truen0cfind_segmenthfbbv_unsigned46Stdlib6ZArith6BinInt1Zig74of_Nk14andbho98seg_baseho9eseg_executableho98seg_sizeho9cseg_writable36Stdlib5Lists4Listim82Inig73addig72leig73powk13natig76of_nathf7Z_to_bvk15false37Corelib4Init5Peanoir72lthi64woffk14prodk14pairhi6crange_avoidsk11Shs91Ihf2BVhf4BvWfhf6bv_addk13nilhi6cranges_avoidk14conshi68restrictn05ms_pchi6aunrestrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jl44mkst3h5LinuxProcessSemantics5Riscv7Preludejp75bvmaphi66hcleann0bmemory_readk14Somen0dov_read_byteshs93and69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~jvc9mrestrictjvccrange_avoidsn05wviewn08store_okn0cwrite_to_memk16length01Zhs93notn0h1seg_ov_read_bytesn0ccode_read_ov01Nn0dfetch_word_ovn0dfetch_half_ovn0efetch_half_anyn0efetch_tail_anyn0dfetch_failuren0emachine_result3h5LinuxProcessSemantics5Riscv3Semlh34coren0daccess_reportn09MachineOkn0h3interp_eff_accessesn0emkAccessReporths92exn0dmemory_accesslh33effjvccranges_avoidn0h4decode_exec_accessesjvc6hcleanjvc8restrictjvcaunrestrictn0dstep_accessesn0caccess_valuen0faccessed_rangesn04stepig73lebk13fstk13snd3h5LinuxProcessSemanticsfLinuxProcessSem5Statemj59page_sizeim87existsbig76modulo37Corelib5Lists7ListDefmo56Forallmj59page_basemj5epage_in_ranges79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct4FPX2~~~~~~ms5dpage_allowedbmj55Modelmj5alive_bytesmj59m_vm_lazymj58m_vmmapsmj5h1maps_subtract_allmj5evm_backed_mapsmj5h1m_vm_materializedmj5fvm_backing_usedms5aeager_usedig73mulmj5fwith_vm_backingms5h5same_but_materializedmj57m_clockmj54m_fdmj55m_fdsmj54m_fsmj56m_fsysmj58m_haltedmj54m_iomj55m_limmj57m_pipesmj56m_procmj5dm_rlimit_coremj57m_stdinmj55m_tidmj56m_time3h5LinuxProcessSemanticsfLinuxProcessSem2Fsom82Fsmj57FdEntrymj57FdStatemj57FsStatemj5bInputStreammj57IoStatemj58LimStatemj57PipeBufmj59ProcStatemj59TimeStatemj56VmMapsms57A_bytesms57A_pagesms54A_wfim85NoDupmo53mapmj5cpage_base_ofjvc4woffmj5bpage_insertmj58page_memmj5h0access_pages_accmj5eaccesses_pageshs92ormj5h8newly_materialized_pagesms5alazy_covermj58vm_limitms54MInvmj5hamaterialize_model_accesses3h5LinuxProcessSemanticsfLinuxProcessSem3Runpvb6configmj55eventpvb5SNextpvb9sstep_cfgpvb7step_to69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~qlb8the_scfgjvc4MInvpvbfmi_account_stepjvc4A_wfjvcalazy_coverpvb5mkCfgk14unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct5Nodes~~~~~~qtf7node_okjvch5same_but_materialized69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~rk56mstepsjvcbmunrestrictk14negbk13orb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct4FPX4~~~~~~rq47seg_topim87forallbrq4h0wx_segs_nowrap_bjvcewx_segs_nowrapjvc7A_bytesjvcaeager_usedjvceH_off_segments" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition mrestrict : ltac2:(zQ "41!h9!jc!l9!m2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$3>1m~0~0") := ltac2:(zQ "50!h9!jc!m2!l9!m9\1H>0@1$1@1$0#k0$2\1m>0@1$1@1$0#k0@1$3@1$1@1$0#8\1a@1$1@1$0#k0M2\0$2@1$3@1$1@1$0#8@1^3^1@1$4@1$1@1$0#8@1^2^1").

(* [comment removed for export] *)
Definition munrestrict : ltac2:(zQ "41!h9!jc!l9!m2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$3>4full~0>2m'~0~0") := ltac2:(zQ "41!h9!jc!m2!l9&>0@1$1@1$0#k0@1$3@1$1@1$0#8\1H>0@1$1@1$0#k0$2\4full~0\2m'~0\1a@1$1@1$0#k0M2\0$2@1$3@1$1@1$0#8@1^4^1@1^3^1@1^2^1").

Definition restrict : ltac2:(zQ "40!q7!m2!h9!jc>1H>0@1$3@1$2#k0$1>2ms$0$0") := ltac2:(zQ "e0!m2!h9!r7!q7!se!t8!u3!uc!v8!hg2!hgc!hh5!hm6!jc\1H>0@1$d@1$1#k0$0\2ms$3@8$2@1$8^1@1$5^1@1$7^1@1$b^1@1$9^1@1$4^1@2$c^2@1$6^1@1$a^1").

Definition unrestrict : ltac2:(zQ "50!h9!jc!q7!m2!l9>1H>0@1$1@1$0#k0$3>4full>0@1$1@1$0#k0@1$4@1$1@1$0#8>3ms'$2$2") := ltac2:(zQ "f0!h9!jc!m2!l9!r7!q7!se!t8!u3!uc!v8!hg2!hgc!hh5!hn3\1H>0@1$1@1$0#k0$2\4full>0@1$1@1$0#k0@1$3@1$1@1$0#8\3ms'$5@8$4@1$a^1@1$7^1@1$9^1@1$d^1@1$b^1@1$6^1@3$e^3^2@1$8^1@1$c^1").

(* [comment removed for export] *)
Definition H_off_segments : ltac2:(zQ "50!m2!ho2!h9!hre!jc>4segs@1$1$3>1H>0@1$4@1$2#k0$0P") := ltac2:(zQ "b0!h9!hre!m2!htd!jc!m9!ho2!l9!hu3!hua!hv9\4segs@1$6$1\1H>0@1$4@1$0#k0$2>1a@1$4@1$0#k0>0@3$3$2@1^2^1$8@3$3@1$7$1@3$9^4@2$a@1$0#k0^2+1@1$5$1").

(* [comment removed for export] *)
Definition wx_segs_nowrap : ltac2:(zQ "20!ho2!hre>4segs@1$0$1P") := ltac2:(zQ "f0!hre!ihf!ii7!m2!ho2!hu3!htd!iie!ija!ikc!il8!inb!io1!io8!ioe\4segs@1$4$0>3seg$0>0@3$b$0^1^2>0@3$6$3@2$2@1$8^2@1$a^2$5@2$d@2$c@1$1@1$7^3@1$1@1$9^3@2$e+2+k0").

(* [comment removed for export] *)
Definition woff : ltac2:(zQ "30!h9!jc!ip5>1a@1$1@1$0#k0>1k$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!ip5!io1!ipb!iq5!jc!hv9\1a@1$5@1$0#k0\1k$1@2$4@1$0#k0@2$2@2$6@1$0#k0^2@1$3^1").

Definition range_avoids : ltac2:(zQ "40!h9!jc!m2!ip5>1H>0@1$1@1$0#k0$2>1a@1$1@1$0#k0>1n$3P") := ltac2:(zQ "80!m2!ip5!h9!jc!iqf!htd!isb!it1\1H>0@1$3@1$2#k0$0\1a@1$3@1$2#k0\1n$1>1k$1>0@2$6^1^2@3$5$0@1^5@2$7^4^2$4").

Definition ranges_avoid : ltac2:(zQ "60!h9!jc!m2!ho2!ip5!it9>1H>0@1$1@1$0#k0$2>1l@1$3@2$5@1$1@1$0#k0$4P") := ltac2:(zQ "90!h9!jc!ip5!it9!m2!ho2!iu0!iu7!inb\1H>0@1$1@1$0#k0$4\1l@1$5@2$3@1$1@1$0#k0$2>1a@1$1@1$0#k0>1n$2>0@3$8@2$3@1$1@1$0#k0$2@4$6@1$1@1$0#k0$2^2^1^3@3$7^5^3^2").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma woff_0 : ltac2:(zQ "40!h9!jc!htd!it1>1a@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1N0^1").
Proof.
  intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma woff_succ : ltac2:(zQ "a0!h9!it1!jc!iv7!ip5!ivb!htd!jg0!jg5!jgc>1a@1$2@1$0#k0>1k$4@3$6@1$2@1$0#k0@2$1@3$9@1$0#k0^2@3$7@1$0#k0+1Kv$5@2$8@1$0#k0+1^1@2$1^2@1$3^1").
Proof.
  intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : ltac2:(zQ "80!m2!h9!jc!iv7!iqf!ip5!htd!iu7>1H>0@1$2@1$1#k0$0>1a@1$2@1$1#k0>1n$5>0@3$7^3^2@1$3^1@3$6$0@1^4^3$4").
Proof.
  intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : ltac2:(zQ "a0!h9!iu7!jc!iv7!m2!ip5!ivb!jg0!jg5!jgc>1H>0@1$2@1$0#k0$4>1a@1$2@1$0#k0>1n$5>0@3$1^3^2@1$3^1@3$1^4@3$9@1$0#k0^3@3$7@1$0#k0+1Kv$6@2$8@1$0#k0+1^2").
Proof.
  intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : ltac2:(zQ "c0!h9!m2!iu7!jc!iv7!iqf!ip5!ivb!htd!jg0!jg5!jgc>1H>1x@1$3@1$0#k0$1>1a@1$3@1$0#k0>1n$6>0@3$8$1@1^3^2$5>0@3$2^4@3$b@1$0#k0^3@3$9@1$0#k0+1Kv$7@2$a@1$0#k0+1^2@3$2^5^4@1$4^3").
Proof.
  intros H a n H0 Hr k Hk. destruct k as [|k].
  - rewrite woff_0. exact H0.
  - rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : ltac2:(zQ "70!h9!jc!m2!ip5!jh5!it9!jhb>1H>0@1$1@1$0#k0$2@2$6^1@1$4@2$5@1$1@1$0#k0$3").
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : ltac2:(zQ "a0!h9!jc!ip5!it9!jhb!m2!jib!ho2!iu0!iu7>1H>0@1$1@1$0#k0$5>1a@1$1@1$0#k0>1n$2>1l@1$7@2$3@1$1@1$0#k0$2>0@3$9^4^3^2>0@2$4^5^2@2$4^6@3$6@2$3@1$1@1$0#k0$2@4$8@1$1@1$0#k0$2^5^4^3").
Proof.
  intros H a n l Ha Hl a' n' [Heq | Hin].
  - injection Heq as <- <-. exact Ha.
  - exact (Hl a' n' Hin).
Qed.

(* [comment removed for export] *)
Lemma restrict_svc_pending : ltac2:(zQ "80!h9!hh5!jc!m2!l9!htd!q7!jj2>1H>0@1$2@1$0#k0$3>2ms$6@3$5@1$4@1$2@1$0#k0@1$1@2$7^2^1@1$1^1").
Proof. reflexivity. Qed.
Lemma restrict_pc : ltac2:(zQ "70!h9!jje!jc!m2!htd!q7!jj2>1H>0@1$2@1$0#k0$3>2ms$5@3$4@1$2@1$0#k0@1$1@2$6^2^1@1$1^1").
Proof. reflexivity. Qed.
Lemma unrestrict_mem : ltac2:(zQ "91!h9!jc!l9!u3!m2!htd!q7!hn3!jk6&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$4>4full~0>2ms$6@3$5~0@1$3@3$8^3^2^1@3$7^3^2@1$3^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_mkst : ltac2:(zQ "a1!h9!jc!l9!jof!m2!htd!q7!jrd!hm6!jj2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$4>4regs@2$7@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0@3$5$6@2$9^5@5$3?2fx^4^3^2^1@5$3?2fx^4^3@2$8^5^2^1").
Proof. reflexivity. Qed.

Lemma munrestrict_mrestrict : ltac2:(zQ "71!h9!jc!l9!m2!htd!hm6!hn3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$3>1m~0@3$4~0@3$6^2^1@2$5^2^1^1").
Proof.
  intros H m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : ltac2:(zQ "71!h9!jc!l9!hm6!m2!htd!hn3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1H>0@1$1@1$0#k0$4>4full~0>1m~0@3$5~0@2$3^3@3$6^3^2^1@2$3^3^1").
Proof.
  intros H full m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma unrestrict_restrict : ltac2:(zQ "80!q7!m2!htd!h9!u3!jj2!jk6!jc>1H>0@1$7@1$3#k0$1>2ms$0@3$2$0@3$6^2@1$4^1@2$5^2^1^1").
Proof.
  intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite munrestrict_mrestrict. reflexivity.
Qed.

Lemma restrict_unrestrict : ltac2:(zQ "80!h9!jc!q7!jj2!m2!l9!htd!jk6>1H>0@1$1@1$0#k0$4>4full>0@1$1@1$0#k0@1$5@1$1@1$0#8>2ms$2@3$6$2@2$3^3@3$7^3^2^1@2$3^3^1").
Proof.
  intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite mrestrict_munrestrict. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hclean : ltac2:(zQ "40!m2!h9!q7!jc>1H>0@1$3@1$1#k0$0>2ms$2P") := ltac2:(zQ "90!h9!jc!m2!htd!m9!l9!hu3!q7!u3\1H>0@1$1@1$0#k0$2\2ms$7>1a@1$1@1$0#k0>0@3$3$2@1^3^1$6@3$3@1$5@1$1@1$0#8@2$8^3^2@1$4@1$1@1$0#8").

Lemma restrict_hclean : ltac2:(zQ "60!m2!h9!q7!js6!jj2!jc>1H>0@1$5@1$1#k0$0>2ms$2@2$3^2@2$4^2^1").
Proof.
  intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : ltac2:(zQ "70!q7!m2!htd!h9!js6!jj2!jc>1H>0@1$6@1$3#k0$1>2ms$0>0@2$4^2^1@3$2$0@2$5^3^2^2").
Proof.
  intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
  apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : ltac2:(zQ "90!h9!jc!q7!m2!l9!htd!js6!jj2!jk6>1H>0@1$1@1$0#k0$3>4full>0@1$1@1$0#k0@1$4@1$1@1$0#8>2ms$2>0@2$6^3^1@3$5$2@2$7^4@3$8^4^3^2^2").
Proof.
  intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISA.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!ho2!hre@1$0$1").
Variable H : ltac2:(zQ "30!m2!h9!jc>0@1$2@1$1#k0$0").
Hypothesis HH : ltac2:(zQ "10!sja@2$0?4segs?1H").
Hypothesis Hwx : ltac2:(zQ "10!sgf@1$0?4segs").

(* [comment removed for export] *)
Lemma memory_read1_hidden : ltac2:(zQ "90!h9!jc!ho2!htd!m9!m2!l9!hu3!jt0>1a@1$1@1$0#k0>0@3$3$5@1?1H^1$7@3$3@1$6@1$2@1$1@1$0#8@3$8?4segs^2@1$0#1@1$4@1$2@1$1@1$0#8").
Proof.
  intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

Lemma ov_read_bytes_restrict : ltac2:(zQ "b0!h9!jc!ho2!l9!jte!htd!ju5!ip5!jv5!kj7!kk4>1n$7>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$5@1$3@1$2@1$1@1$0#8@4$6?4segs@2$9?1H^3^2^4@2$4@1$2@1$1@1$0#8^1@2$8@3$5@1$3@1$2@1$1@1$0#8@4$6?4segs^4^3^5@2$4@1$2@1$1@1$0#8^2@3$a?1H^3^5").
Proof.
  induction n as [|n IH]; intros m a bs Hr.
  - cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
  - cbn [ov_read_bytes] in Hr |- *.
    unfold mrestrict in Hr at 1.
    destruct (H a) eqn:Ha.
    + rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
    + destruct (match m a with
                | Some b => Some b
                | None => match memory_read segs a 1 with
                          | Some (b :: _) => Some b | _ => None end
                end) as [b|]; [|discriminate].
      destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
        [|discriminate].
      destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
      rewrite Hfull. split; [exact Hr|].
      apply range_avoids_cons; assumption.
Qed.

Lemma wview_restrict : ltac2:(zQ "80!h9!jc!l9!m2!kl4!m9!htd!kj7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0@3$6@1$2@1$1@1$0#8@3$4?4segs@2$7?1H^2^1M3\0$3@1$2@1$1@1$0#8@1?1H^1@1$5@1$1@1$0#8@3$4?4segs^2^1").
Proof.
  intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
  rewrite (HH a Ha). reflexivity.
Qed.

Lemma store_ok_restrict : ltac2:(zQ "b0!h9!jc!m2!hu3!htd!klc!ip5!l9!jv5!kj7!kk4>1n$6>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1a@1$1@1$0#k0>0@3$4$2@4$5?4segs@2$9?1H^2^1^3$3@2$8@3$4$2@4$5?4segs^3^2^4$3@3$a?1H^2^4").
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
    destruct (H a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_restrict : ltac2:(zQ "91!h9!jc!l9!km7!kj7!kn6!ho2!htd!kk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2bs@1$6@1$1@1$0#8>1m~0>1a@1$1@1$0#k0>0@3$8?1H^1@2$5@1$1@1$0#8^3@3$7~0@3$3@2$4?1H^3^2^4@2$4?1H@3$3^3^2^4").
Proof.
  induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite <- (IH _ (a + 1) Htl). f_equal.
  apply functional_extensionality. intro x. unfold mrestrict.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : ltac2:(zQ "a0!h9!jc!l9!htd!m2!kn6!ho2!hu3!km7!kk4>2bs@1$6@1$1@1$0#8>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1x@1$1@1$0#k0>0@3$9?1H^2@2$5@1$1@1$0#8^4>0@3$3$4@1?1H^2$7@3$3@1$2@1$1@1$0#8@4$8^5^4^6^3@1^5^3").
Proof.
  induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha in Hx. discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma find_segment_some_spec : ltac2:(zQ "e0!hre!ihf!jv5!knf!iie!io1!io8!jte!ho2!l9!htd!ikc!hua!inb>1l@1$8$0>4addr$3>1n$3>3seg$0>0@3$a@1$9$0@3$c^4^3^2@2$7$0^1@2$2@3$d$0^2^5@2$2@2$6@1$1@1$4^2^4@2$6@2$5^4^3@2$5@1$1@1$4^2@1$1@1$b^2").
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.

Lemma find_segment_none_spec : ltac2:(zQ "f0!hre!ihf!knf!iie!io1!io8!m9!ho2!l9!jv5!htd!ko2!ikc!hua!inb>1l@1$7$0>4addr$2>1n$2>0@3$a@1$8$0@3$d^3^2^1@1$6$0>3seg$0>0@3$e$0^1^5@1$b@2$9@2$5@1$1@1$3^2^5@2$5@2$4^5^4@2$4@1$1@1$3^2@1$1@1$c^2").
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

(* [comment removed for export] *)
Lemma in_segment_not_hidden : ltac2:(zQ "d0!h9!ihf!hre!iie!io1!io8!hv9!m2!iqf!htd!ikc!inb!jc>1x@1$c@1$0#k0>3seg$2>0@3$b$2^1?4segs>0@2$5@1$1@1$3^2@2$6@1$0#k0^3>0@2$5@2$4@2$6@1$0#k0^4+1@2$4@1$1@1$3^3@1$1@1$a^3@3$9$7@1?1H^5$8").
Proof.
  intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
  exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

Lemma seg_ov_read_bytes_restrict : ltac2:(zQ "h20!h9!ihf!jc!iie!io1!io8!l9!hre!ikc!ko9!hv9!ho2!ip5!htd!kj7!inb!ipb!ioe>1n$c>1m>0@1$2@1$0#k0@1$6@1$2@1$0#8>3seg$7>1a@1$2@1$0#k0>0@3$f$7^2?4segs>0@2$5@1$1@1$3^3@2$a@1$0#k0^2>0@2$5@2$4@2$a@1$0#k0^3@1$h0^6@2$4@1$1@1$3^4@1$1@1$8^4>0@2$5@2$4@1$1@1$3^5@1$1@1$8^5@2$h1+2+k0@3$d@1$6@1$b@1$2@1$0#8@4$9@2$e?1H^7^6^5^8@4$9^7^6^5^8").
Proof.
  induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
  unfold mrestrict at 1. rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned.
      assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (bv_unsigned_in_range 64 a). lia. }
    rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

Lemma code_read_ov_restrict : ltac2:(zQ "80!h9!jc!l9!kpe!ho2!htd!kqd!kj7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1n$6@3$5@1$2@1$4@1$1@1$0#8@4$3?4segs@2$7?1H^3^2^1@4$3?4segs^3^2^1").
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
  apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
  rewrite N_nat_Z. exact H2.
Qed.

Lemma fetch_word_ov_restrict : ltac2:(zQ "60!h9!jc!l9!kr0!htd!kj7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0@3$4@1$2@1$1@1$0#i0@3$3?4segs@2$5?1H^2^1@3$3?4segs^2^1").
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : ltac2:(zQ "60!h9!jc!l9!ks0!htd!kj7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0@3$4@1$2@1$1@1$0#h0@3$3?4segs@2$5?1H^2^1@3$3?4segs^2^1").
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : ltac2:(zQ "60!h9!jc!l9!kt0!htd!kj7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0@3$4@1$2@1$1@1$0#h0@3$3?4segs@2$5?1H^2^1@3$3?4segs^2^1").
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : ltac2:(zQ "60!h9!jc!l9!ku1!htd!kj7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0@3$4@1$2@1$1@1$0#i0@3$3?4segs@2$5?1H^2^1@3$3?4segs^2^1").
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : ltac2:(zQ "80!h9!jc!kv2!l9!htd!lg2!q7!kj7>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0@3$4@1$5$6@3$2?4segs@2$7?1H^2^1@3$2?4segs^2^1").
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)
Lemma interp_eff_accesses_restrict : ltac2:(zQ "h54!h9!jc!l9!lj5!it9!htd!ljd!jv5!iu0!lkd!ll9!lg2!ln0!kj7!m2!ho2!hu3!lo1!lo7!lp7!lpe&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@2$4$3~0&@1$6~1&@1$b~2>1t$h3>1m~0>1c$3>3mr'~0>2rs@1$f$h2>0@3$5~3@3$a?4segs^5@2$d?1H^4@2$9~2@3$c~1@4$8$3~0^3^2^1@2$h1~0\3mf'~0@2$7@3$5~3@3$a?4segs^7^6@2$9~2@3$c~1@4$8$3~0^5^1^3@2$7@3$5~0^4@2$d?1H^1@2$7>1x@1$1@1$0#k0>0@3$5$e@1?1H^1$h0@3$5@1$2@1$1@1$0#8@1^3^2@1^8^2@2$h4?1H^3").
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; (* [comment removed for export] *)
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - (* [comment removed for export] *)
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  - (* [comment removed for export] *)
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [|destruct (range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  - (* [comment removed for export] *)
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_accesses_restrict : ltac2:(zQ "h10!q7!ljd!jv5!htd!lkd!lqe!lg2!ln0!ho2!h9!lo7!u3!ls6!lpe!lt0!ltc!jc>2ms$0>1w@1$h0@1$9#i0>4msr'$0>3rs'@1$8$a>0@3$3@1$6@1$1$0@3$5?4segs@2$e?1H^4^3@2$4@1$1$0@3$7$0^2^1@2$2@3$3@1$6@1$1$0@3$5?4segs^5^4@2$4@1$1$0@3$7$0@3$f?1H@1$b^5^3^2@2$2@2$d?1H^2@2$c?1H^3").
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : ltac2:(zQ "f0!q7!ljd!jv5!htd!lkd!lg2!ln0!lua!ho2!lo7!u3!ls6!lpe!lt0!ltc>2ms$0>4msr'$0>3rs'@1$8$9>0@3$3@1$5@1$1$0@2$7?4segs@2$d?1H^3@2$4@1$1$0@3$6$0^2^1@2$2@3$3@1$5@1$1$0@2$7?4segs^4@2$4@1$1$0@3$6$0@3$e?1H@1$a^4^3^2@2$2@2$c?1H^2@2$b?1H^3").
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (vdso_text_at segs (ms_pc ms)); [discriminate|].
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

(* [comment removed for export] *)
Theorem step_restrict_sound : ltac2:(zQ "h00!q7!jv5!htd!ljd!lkd!lg2!u3!lt0!ltc!lo1!lva!mg9!mhb!lua!ls6!lpe>2ms$0>4msr'$0>0@3$2@1$5$0@2$c?4segs@2$7?1H^2@2$4$0^1@2$9@1$3$0\3rep@1$3$0@2$1@3$2@1$5@1$3$0@2$d?4segs^4@2$4@1$3$0^1@2$1@3$2$0@2$a$0^1@3$8?1H@1$6^4^3@2$1@2$f?1H@2$b$0^1@2$1@2$e?1H^3@3$2$0@2$7?1H@3$8?1H@1$6^4^3^3").
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End ISA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition page_allowedb : ltac2:(zQ "60!knf!m2!ho2!it9!h9!jc>1A@1$2@2$3$0$0>1p@1$5@1$4#k0$1") := ltac2:(zQ "d0!knf!it9!h9!mi2!hv9!ii7!mi9!ho2!mif!mm3!mn0!io1!jc\1A@1$7@2$1$0$0\1p@1$c@1$2#k0@3$a@2$1$0$0\2iv@2$1$0$0@2$5@2$3@3$6$0$0^1@2$4@1$2#k0^2@2$3@2$b@2$4@1$2#k0^2$9@3$8$0$0^1^2").

(* [comment removed for export] *)
Definition A_wf : ltac2:(zQ "30!knf!ho2!it9>1A@1$1@2$2$0$0P") := ltac2:(zQ "b0!knf!it9!mi9!mif!jv5!htd!mm3!mnb!ho2!mpc!io8\1A@1$8@2$1$0$0@3$9@2$1$0$0\2iv@2$1$0$0@2$4@2$a@3$2$0$0^1@3$3$0$0^1@2$4@3$5$0@2$7@3$2$0$0^1$6Z@3$5$0@2$7@3$3$0$0^1$6Z^1").

(* [comment removed for export] *)
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

(* [comment removed for export] *)
Definition lazy_cover : ltac2:(zQ "60!h9!jc!ho2!it9!knf!m2>1H>0@1$1@1$0#k0$5>4lazy@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0>1A@1$2@2$3$4$4P") := ltac2:(zQ "c0!m2!h9!jc!htd!ho2!it9!hu3!knf!mq6!iqf!mr3!ng5\1H>0@1$2@1$1#k0$0\4lazy@1$4@2$5@1$2@1$1#k0@1$2@1$1#k0\1A@1$4@2$5$7$7>1w@1$2@1$1#k0>0@3$3$0@2$a@1$8^1^3$6>0@3$3$0@1^5^2$9@3$3$0@2$b^4@1$8^3$6").

(* [comment removed for export] *)
Definition eager_used : ltac2:(zQ "20!knf!nh6>1m$1$0") := ltac2:(zQ "60!nh6!nhf!nid!nja!nk6!nlc\1m$0@1$1@2$4@1$5@1$3^1@1$2^1").

Lemma vm_backing_used_split : ltac2:(zQ "d0!kn6!htd!h9!knf!nh6!nme!mm3!no4!np7!io1!nq5!ipb!jc>1m$4@3$1$3@1$7^1@2$9@1$8^1@2$a@1$b@2$0@1$c@1$2#k0@1$5^1$6").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized : ltac2:(zQ "10!nh6>1m$0>2m'$0P") := ltac2:(zQ "50!nh6!htd!nid!nme!nqc\1m$0\2m'$0@3$1$0^1@3$4@1$2^2@1$3^1^2").

Lemma same_but_materialized_refl : ltac2:(zQ "20!nh6!nrf>1m$0@2$1^1^1").
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : ltac2:(zQ "20!nh6!nrf>2m1$0>2m2$0>2m3$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : ltac2:(zQ "70!ho2!h9!nh6!nid!nqc!nrf!jc>1m$2>4mat'@1$0@1$6@1$1#k0@2$5^2@3$4@1$3^2^1^2").
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : ltac2:(zQ "i60!htd!jv5!h9!jc!ho2!l9!it9!nh6!nt9!nu4!nuc!nv5!nvd!og7!oh3!ohb!oi4!oif!oj9!oka!ol5!ole!nid!nja!np7!knf!op3!op9!oq4!oqf!ora!os9!ot4!ou0!oub!ov8!pg5!nrf>1m$7>2m'$7>0@2$i5^2^1@2$1@3$0$hc@1$9^2@1$9^3@2$1@3$0$i4@1$h7^2@1$h7^3@2$1@3$0@1$4@2$6@1$3@1$2#k0@1$3@1$2#k0@1$h6^2@1$h6^3@2$1@3$0$hf@1$e^2@1$e^3@2$1@3$0$hd@1$c^2@1$c^3@2$1@3$0$i2@1$h1^2@1$h1^3@2$1@3$0$i0@1$f^2@1$f^3@2$1@3$0$i3@1$h5^2@1$h5^3@2$1@3$0@1$4@2$6@1$3@1$2#k0$hb@1$a^2@1$a^3@2$1@3$0@1$4@2$6@1$3@1$2#k0$i1@1$h0^2@1$h0^3@2$1@3$0$he@1$h3^2@1$h3^3@2$1@3$0$ha@1$b^2@1$b^3@2$1@3$0@1$5@1$3@1$2#k0@1$d^2@1$d^3@2$1@3$0@1$5@1$3@1$2#k0@1$h4^2@1$h4^3@2$1@3$0@1$5@1$4@1$3@1$2#8@1$h2^2@1$h2^3@2$1@3$0@1$3@1$2#k0@1$8^2@1$8^3@3$0$h9@1$h8^2@1$h8^3").
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  repeat split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
  match A with
  | [] => []
  | iv :: r =>
      map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
          (seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
      ++ A_pages r
  end.

Lemma Zmod0_multiple : ltac2:(zQ "60!knf!htd!mm3!lo1!mnb!nq5>1a$0>0@3$1$0@2$4^1$2Z@2$3$0\1q$0@3$1$0^3@2$5$2^1").
Proof.
  intros a Ha. exists (a / page_size)%Z.
  pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
  rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.

Lemma A_pages_length : ltac2:(zQ "b0!knf!kn6!ho2!it9!htd!mm3!pgf!pha!pi5!nq5!ipb>1A@1$2@2$3$0$0>0@1$8^1@3$4$0@2$9@1$a@2$1$0@1$7^2$5@1$6^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanAcct ()) ["FPX2"] "#$&{p'0h01Hh13Hleh22H0h33Hhih43Hloh53Hwfh61ih71qh81zi001zh91eh:4Hwf'h;4__x1h<4__x2h=4__x3h>1li011lh?1Ah@2H1hA2IHhB7__arithhC4__ffhD8__varmaphE5__withF3H10hG2H2hH2H3hI2H4hJ2H5hK2H6hL2H7hM2H8hN2H9hO4__p1hP4__p2hQ4__p3hR4__p4hS6__sat0hT!s/%1hU4__x4hV4__x5hW4__x6hX4__x7hY4cstrhZ2hih[2loh\1nh]2q0h^1rh_2r0h`1aha2ivhb1pi021phc3qhihd3qlohe1xi031xp%0p&0p;2p;1p;3p;6p;4p;9p;5p;7p;8g00`7R0k20^Tg00EAR1k108Tg03[jj1LTg03\kj1BTg03]oj1:Tg00Dak105Tg00A`j2gTg00c4j3;!sB$Ej2>Tg00<9R2j28Tg0037j32Tg004_j1DTg005?j23Tg01F;j27Tg00[^k600Tg01O\k20PTg03_3R3j3S!t-$Tj6y!s:$Tj2oTg01WWj2r!s8$kk201Tg02H[R4k20!t9$C`k107Tg03a6j2n!uH$Ij2mTg01cVj1^!sA$gj2lTg00Y9j26Tg03bNj2kTg03c5j2j!s/$[j2iTg03dAj2hTg00d1j2XTg00G;k10Y!s0$Yk10!s:$HDk204Tg001Qj1Q!s_$gk303Tg00o?j1sTg00K<k20W!s0$^k20VTg00LJk30U!s0$ik40TTg03=oj29Tg03eJj1qTg00?Uj1pTg01iYj2~Tg00=ok10O!sK$jk20NTg03fSk30MTg01jBk30L!s0$kk20JTg00F?k10!wN$YUk10C!u-$gj2wTg00IJj3v!s/$mj4bTg03g<k20ATg008hj6Jl9{!s<$Zk30@Tg03h;k30?!s0$dk20>Tg03iGk20E!s0$fk40=Tg03jEk30HTg01]=k50ITg00`Wj4z!sC$dk30<Tg03kAk30K!yt$@j2tTg03ZHj2|!sB$^k20;Tg03l:k40!zL$mlk30Q!z}$ak20R!uX$]k40!vW$lVk30!yY$JXk70!xS$Zek60]Tg03m9k70\Tg01MMk60[Tg01mLk70ZTg00Z7j8_!{2$TR5f1R6,r5#Dg03?BR7'9f0R832p=If3R9P5P5f2R:P6Cz;;8p=AB0<558p=GB0K!s/$C1t87g00=QR;525p=51978p=11|87#qp=Eg00=2R<00;8p=Vg00QCR=P5P6P8H0:p=\B0Q568p=UP5!s=%Czp=N1r58p=]1967=258p=d1987p=cA2!sT$41967/38p=}%D8/97p=P13:6!sS%M1>;8p=<1t87p==1|87p=F1368925:p=Z1>8;p=YA258;p=?20R58p=[P5P:!th%9p=W20458p=RB0S!tB$KP:g00T2R>g00TQR?P?g00U1R@P5P6g00UQP8Cbg00V8RAK06p=@%Q8#Qp=fg00SFRB?;68p>0GA;B689;B:p>0Ff4RC!s7+9;B95;Bp=0P6P>P?P?P@P8J0]p=eP:!s8+6P8K0\p=x!tI&]cP8Cbp=T!s\/P!tS%O!sp1[p=`!sp3Zp=aP9!s:+!u{$G_p>0Bf6RA!s>'f5RDPC!sN5G_p=uP!sM+PD!s0+CP9P:G_!su&=H20^55R>$08REP>%L8%B6%:6'I[RFX?E&05>RG#L%:G,g5W5P0P5P5A;>:6#LA;>9:R0#B%:0'I[\F^>EP8P>P9P:P6CA#LP3P>%G8R3%C8R0'>%53%50'8'8Xa>R0P>PAPDPCCAR392E6f8RH%D8RI#1RJ'3X6=f7RK,7ARL#E#V'\%BD'U%:D,3L'IRL[!t<$!uI$CARM92EGP>P!v0$CARN!s6$EPGP1P>p-0RGP8g01Qjg00bWROn1011010002!s%$!s#$X9Eg00RFP3P8J00PO20PL8b2W0P8O1W0%G6RL%C6R3'>RP%5L%53'8'8P2%G:R3%C:RL!u^$R3%5L'8AS>0:A;>C9P>f=RLf<RQf;RRCA52Ef?RS/3JX6=f>RT,7LRU!u^'Q'U%:Q,3U'I[[P8%GC%CC'>%GD#5%CD#5!tA%A#5%CA#5AS>0AA;>HKP>fAR2f@RUPS!t3%CRV!t3&BS00,72RW!t4'U'U%:U,3W!t4'H#5f9RW#C!sy%Wf:RX9;>RP>fDRYPVQ00!s{$A;>QRP>fERZPYPV!s:$PEPEP1P>PEP8PLP8!v~2102101X9EA;>LQP>fFR[PZPYCAP8EyA2EQYPEP>!sh$>P8PSP6!sh>TLfGR1/N[RY=;>ZP6EyA2>TYfHRY/N192>SP8fIR\/NY92>UP>fJR]/N\A2E2\R^%C9!uY%ZfQR_!v>%S01fOR`fPRa'7Rb#ERc#VS02'\RdfNRe#BRf'U#]S03#D%:eRg,3b'dS04]:]3^43^1P[Xb>A2EUYP8P^PEP]fMR^fLRP'NR3#GRb%C3'>1Ne^R3#G#51N`e!w4'9fRRh!tY%17a_Ri#ERj!wo%`Rk'U%:`,3iRi'I]:]3]4]1X>EfKRl,NPRm#G%Cm'>%5b%C3!sw%^P=%]dS05%]fR0'o1dIiX\=P=Q02,r=S06%]k,o8#D/diX\=RkP=PcPkP5%DcRk%D0RI'3S07%c8S08/4iX85P5%cIS09,}k148!s8%Pg%Pj?M!s4$201a:%18Ri,4_X75-025P4P514hiX7517_hRj#E#P%:aRa13ja3MP8fTRa/4iP5%16RjP>P8fUS0:PaCA#LfV,>6%5:RgfXR3/79Rb#E#PfWRm#:Rn13bn3M]4]1]5X[5P>PjPafSCA#L%1:RaQ0:'>%19#5S0;201mW143i!ti-fYR4/4iX75%1ARm,74R4!tp%3R31343!tp$[!tn$Pj%1XRi/>8P>%1RR3P6f]!t9%LR4,79Rn!tj$_S0<#:Rb13nb3M^3g]5]1XZ5%1WRg/>jP>PiPaf\S0=CA#LQ0;f^#B#]Ra$07%Da#<1n47%<41>;7Ra%1S#=#<[[1nm7%<m%1HRm#=Rj#<\a[%1KRn/m7A257;Ro#^Rp%Fm#1=Zmj[1lm716;7Rj%=gRq#<S0>16q7'8[1kg7167;Rr%=iRs,67%Ys'8[1ji7%F3#?\o1i37%1QRt#=/4t\o%FtS0?P5%=4S0@P5%1[/m7%11Ru%Fu#1%=u3Z\p1lu7%1YRv#=Rw#<16w7'8\j1kv7%1\Rx#=Ry!t=$y'8\r1jx7%1]Rz#F!tB%z7%1lRl#=/4l\o%FlS0AP5%1PRP#=S0BP5fnP_O1foR{#B%:{'I1he:14e:R|%^|'XR|eP|1h1X141XR1%^1'XR1eP1&05BS0C&08BS0D%[:%[97W6&0Y5S0E&0X5RBg00;6R1-045R|%Q1S0F#RR}6035S0G%s1R1#RR~'K1K~|1K~!s@$3@20WB@S0HP8P:g00VXR@g00W8R~'g20V8:=2@~dB0U5;6H0TS0IbCbDbEX;5X<5X=51786/9:19:819:6'7'4^;5^<5^=5P8P7P_P\O3bBbFbNbAb_b]bMbLbKbJbIb^b7bHbGb@b2b0bSbTbY17CQ%1C/7t'dP517DLR\#cR~%E8#Pf`#:R@138@3M!}|%\%q8#P17AT/}@S0J7M@!s?&Q08Q!s6'13~b,g5%q\#DQ0<!zs$b!zs$b#<%1TRb/n7%<b%1U#=!z]$1nn7%<nQ0>\a[1mm7%Fg#1=Zgq\p1lg7%<s16s!y7&i7%=3Ri!y3$i!y3%37Q0?!y/%t7Q0@/44\o%F4P5%=bP51mu7%Fv#1=Zvw\p1lv7%<y16y!sx&x7%=zRx!sx$x!sx%z7Q0A!sx%l7Q0B/4P\o%FPP5%1^#=P5P{PhO1fp!yu-`:14`:R`%^`'XR`eP`1hYX14YX!s:/%p<#p#p,~5Q0F#QR`#QR{#Q#f!s$%$0ORP-0N51~5<60M560L5g01oX+0JRoP!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$~!s$qQ0C-0Go:0FooD0!s$~!s$~!s$~!s$~!s$~!s$LQ0D%[A&0D5Ro7W9%[C7W:%[K?WKo%[D7WK7W6Q0EPB%R{R{9@B|Rl1eBl5xB&0C?R?PB%s`#RRl9@B}Rz1eBz5xBP?PBPB%R`R`1w5;Rz5@BRrP?%Q1#RRx1K`}Rj5@!sN&PrP?A@Blz!s5%1T`z,OBRyP?1T`x,OB1`BW5a!sT&1Tz`,OBRvP?1`BX1Tx`,OB!sE,eBrRwP?1K`l=v5x9@Bj!t5,%s1#RR11K`|!tO5{!tO&P!tH%1!tH%R!t%+P!tA%Q1T1!tA0P!t=%{=v51!t=+51w5PRj/K}g00]<R}1Kj|Cb,O!s[$A@B1z!s/&xzP?P5PzP}Q0G!sH$H0BFuFH!s$6uQ0HQ!#NJ3XU5XV5XW5XX5XOGXPGXQGXRG148DR}PO\}'X14:K!s2'%?C19DC,4A[%?D%?XR}[16A;16KH/8Q[16;K16WH,8T[%?HPO[19WH19WL;ZX[%?W19XH,4Q[%?T\}16R;16QT/8V[16;Q16SL,8Z[%?L!s`$TQ19T2;ZU[19PL19PQ'>%?2RZ17SU#<\Z[!s#0!#PT'^U5^V5^W5^X5^OG^PG^QG^RGP8%<R%YR%<C%YCPDPQPRPCP7PhP]P6P:PAPKPHPWPXPLPTPSPUP2PYP[PeOJ!#QFL-0A\EJ%F~Q0CQ0DPoQ0EA@Bjz,eB!wK/%?PPO[P8bBPpe:0@\7EJ%1D/74P8J00b0W3W5W1Q0=P8!th$TM9{W0Xc5P6P8O2n2001!#fO$121103000b9W4W1W5Q0:P8P_PHPK!s[%d!s[@Q09P^P8O1EJQ07#cB0?kI7EJ1oc0#D20>c0EJQ0620Ec<EJQ05P=P5Q01Q02H0=EJQ03B0H5dfEJQ04eW:W3W4W1Q00P8EJb@W2P2!s0$!#h2%b2!s+%W0P8PK!#jj$O5W0!s_%!ty7!s/%W0W1!sD?X>EXe!#kb%P8O4n20021!sO'20041103!s7+A2E8N13K!#bl$DARD!#g[&C'U%:C,3D'I[X>EPMO1P81gENO1b0%BM%:M'IeW5XAFX?EXZ5X[!w$/102!w$'0100X`>P8I0IW?o"). Qed.

Lemma A_pages_in : ltac2:(zQ "f0!knf!h9!htd!hv9!m2!ho2!it9!hu3!mm3!pha!pi5!ng5!inb!mnb!jc>1A@1$5@2$6$0$0>1p@1$e@1$1#k0>0@1$a^2>0@3$2$0@2$d@2$3@1$1#k0^2$8Z>0@3$2$4@2$b^4^3$7@3$c$0@2$3@1$1#k0^4@1$9^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanAcct ()) ["FPX2"] "#$<vp'0h01Hh11ih21qh32H0h44__x1h54__x2h61eh71zi001zh83Hleh93Hpah:4__x3h;2hih<1li011lh=2loh>1xi021xh?1Ah@2H1hA3HhihB3HlohC7__arithhD4__ffhE8__varmaphF5__withG1pi031phH3H10hI3H11hJ3H12hK3H13hL3H14hM3H15hN3H16hO3H17hP3H18hQ2H2hR2H3hS2H4hT2H5hU2H6hV2H7hW2H8hX2H9hY3HwfhZ4Hwf'h[6__sat5h\4__x4h]4__x5h^4__x6h_4__x7h`4__x8ha4__x9hb2b1hc2b2hd2ivhe1nhf2q0hg2q1hh1rhi2r0hj2r1hk3Halhl!t2%3hm!s/%4hn1Bho4__p1hp4__p2hq5__x10hr!s-$1hs1fht3lenhu1mhv5starthw1yhx4Eqhihy4Eqlohz3Eqph{3H19h|3H20h}2IHh~!t8%6i04!s0%7i051ai063qhii073qloi082qpi092z3i0:2z4i0;1bp%0p%1p&0p;2p;1p;6p;3p;4p;5p;7p;8p;<p;Bg00`7R0k20}Tg00EAR1k10=Tg001Qj1ETg0026k10|!s0$Tk10gTg03[jj1bTg003Qj2;Tg03m]j2vTg00Dak10?Tg00[^k606Tg03\kj1gTg01O\k20JTg00c4j3L!sV$ER2j23Tg00<9R3j27!s~$7j3:Tg03_3R4j3q!sY$Tk60FTg004_R5k10!tm$5?R6j2>Tg01F;j28Tg02F1k20CTg00d1R7j2QTg03ngk20VTg01^cj2=Tg01_@j2fTg03oGk303!s9$^k20{Tg01`?k20z!tR$kk20!t#$H[R8j2{Tg03a6j2S!v&$Ij2!s}$cVk107!sB$gj2YTg00Y9R9j2cTg03bNj2XTg03c5j2[!s/$[j2WTg03dAj2RTg00G;k10!vv$GYk10aTg00HDk20G!sM$gj3zTg00o?j1yTg00K<k20`Tg00A`j2x!s9$^k20_Tg00LJk30^!s0$ik40]Tg03=oj20Tg03l:j4wTg00a7j3!t+$ock50\Tg03eJR:j1oTg00=ok104!t/$@j2!x:$ZHj2<Tg00F?k10!u\$Hgk20D!sa$jk20BTg00?Uj1^Tg01iYj2uTg03fSj3s!sh$ek60X!v=$Uk10!uy$g<k20UTg008hj6iTg03k^j2kTg040BR;k202!wQ$Tk20;Tg00XaR<k201!sH$\k30RTg0417k60T!s0$`k20ATg01n0k10O!s0$Nk20N!s0$ok30!u=$M[k40yTg01N1k40xTg02L2k40!u'$gZk30s!x}$_k30rTg01a9k30qTg042Bk50pTg01]=k50!vQ$`Wk40ITg03jdk30m!uA$Ak30l!|p$ak20k!v]$]k40!u_$lVk30jTg00Imk40:Tg00JXk70H!s:$Jk30hTg01jBk30n!s0$kk20fTg00Z7k809!tZ$`k20eTg00P8m<0dTg00C;m<0K!s:$]mB0tTg01mLk70cTg01MMk60v!}s$9k70wTf0R=#E#Ep>0@g00<TR>g03?BR?,6=g00=QR@3:p=9g00VXRAg00W8RB7:=p=5f1RC%g=5G>p=mf2RD/;C=G>=p=df3REP>P>PDPCH0I;L=p=?B0m>>=p=PB0l!s/$H!sI$CP=H0Ip=_10?=p=21<=?#op=}g00QCRFP>PCg00=2RG/k=Cwp=|1>=?p=I18C=/<?p=rP!sL$%o=,kGCw9G>Dp=`A:>C=p=1P>f4RHPEPDPCP=J06p=J13@=p=416=?p=F1<=?p=N1>C=9:>Dp=B1cC=,7Dp=O1cDC13=@'7p=ZA:>=@p=A&07=,QCp=U20k>=p=a!ub%P=H0ip=D20!u~$KB0j!tR$CPDg00T2RIg00TQRJPJg00U1RK!uT&UQP=H0:g00V8RLK0Hp=@!uE%p>0[1kG=p>0Z%E!wt$#Ep=jB0h!t%$\B0n!s/$Mg01oX-0f=p=pg00SFRM?LC=p=TPEPIPJPJPK!ts%L09p=h!tI&]<!tI$p=nPC!sM+=P!tS%]f6RL!s<'f5RNPH!ss6!sv$e20e@=p=lP>!wU$>P:PHP5PEg043=!sR%N<0dp>0!sG%;P5P2g043jPGP@!wf'N<0Kp>0QPF!s$$>P>P>g044LP5!s$$6g03hd!sX0B0tp>0S!sT$<P5P9g00\:P!tz%!s{/P1cDC/7=p>0013=@p=~!u{'c!u{%>05PD!uV+CP=K0cp=t!v8/J0vp>0M!sM3wp>0L20}>>R9$0=R!tU%;6S00#ES01#ES02#ES03#E$0@S04$0|R<$0gS05%bC1;<C#9S061vED#51;<ER6/mH[[[]GS07X?5Q05&0?9R2#bQ061v2D#5PA1v2EPAp-0R;P=g00bWS08g01QjR:n0110;00020000X6Ag00RFROPB!{o$Q08%g29d<H00J=b0W9WkWYWGP0P>P>Q07Q05AL9ED!t?$AL9NH/vD#5AL9LN,m6!tj$[^<5P=!sS%P9!w:%C?!sX$P9PLPNPHC?!s]$P4P9%P=R4%H=R6'3%94%96'7'7Xd9R0P9f9RPf8RQf7RRC?S099:5CP9f:RSPPPQC?#g9d<LRT[PDP9PRPLPNC?S0:9:52P9PQPRPLC?S0;!s7$5P2P1P9P;P=P:Q08n101101!v,%!v0$!v3$5POQ09!v/'20JT=b3W0P=O1W0%PCRT%HCRO'3R:%9T%9O'7'7P3%PDRO%HDRT'3%9ORO%9T'7Aq90DAL9HEP9f@RTf?R2f>RUC?5:5f=RVP9fARWPTP2C?#g5d<[[P=%PH%HH'3%PN#9%HN#9!t0%L#9%HL#9Aq90LAL9QRP9fDRXfCS0<fBRY!s}$P9fERZPXQ0<!vA&W!s{%Q#9%HP!se%Pf;R[=L9SP9fGR\fFR]PZ!td%<R^=L9[P9fHR_P\P]!s|%5P5!v]$5P=PVP=!v\2103101X65AL9V^P9fIR`P_P\C?P=J0FA:5^\P5P9!si$9P=P2PC!si>UVfJR1/_`Ra=L9_PC!sj$9UafKRa/_19:92P=fLRb/_a9:9TP9fMS0=/_bA:5WbRc%HE!u`%ZfOS0>,;<RdP9fSRefRRffQRgC?'mS0?]Z]A^BO^8:[XG9A:5TaP=PcP5Q0=fPRcQ0>'_R:#PRO%H:'31_gcR:#P#91_fg#H!t4%E1;<cRhP9fTRiPePfC?'m]Z]A]B]8X<5Q0>fNS0@'_Rj#P%Hj!y<$%H:!se%cP>&0E=#2R0,>iX1F18fe#}'|%ggPdP320CC=#5%5DRd%5CR:'Q[RO%5=Rj,Q:20CDC#5Rk[%5ERl/Qd\k20VC=PCn20!w$$0001!{J+cAXbAPO^cA^bAP=1=ih%Ih/=e'fRh1;<gRO,=4%IORk/=6'fXd9>039fRmQ0=O3%5h%5m'QP7fUR7/=O1=ki'f#51;<fRk!sa$kRO!sa/e#5fWRm/>0X1FfVRh,r75`k1mki'QP=1=hk1=O7!sk&eS0AfXRO!sU%1rhm3`S0BQ0A/m7S0CP31fC=#517d:[Rk17:j1f!ux$j[17ld\j20{!utBk!ut+;<iRk,=ORj%Ik/=mRkPCO3%5j%5k'7P3fYS0D1;<7Rk'=#5!sK$O#5f[Rk!to%Q0DfZRj'8#}'|9d<h!s{$m,=k!uD$O#I/=k#5P31=!u+$3DC[Rl13C=1=!u+$d[13ED\d20z!u+<u>Xe>RdPl^u>^e>RlP=f^R:1;<jRnPDO313:nPdPlP=f\Rl,;<#IRdf_RnPEO313dnfaS0E008TfbRd%2=Ro'1X2>,{>P8P>fcS0F/1oX2>fdS0G!uQ'F,8d!uN&nP=feRp/1o208pXff!sU%!sg'gRq!s7%Q0GfiRr!x[&hRs,8q#}'|5d<P=11ro1;<q008p1;<s!sj01;<rR8!tT&nRs!si&lRqfmRt'r5`8P=fk,;</1oP>%2CRofrR8!sN&pRufqRv'r5`=X7>1;<qS0H%I=/3uX7>P2PoP=DJ%Iofo'31;<t138=X7>PY%2DR8PCDJ13v81;<s%9=RsX7>Pq%2ERqPDDJ%9qP>%2URq%2N1>C!tB$sS0I/r=3`X=>Q0IPsX=>PfPqPV!sW$ftR813=8X=>Pi%22RtPUDJQ0I,3tfuRo%2R,3=X=>PE%2TRuP2DJ%2L,3ufvS0JP9P=Q0JPoC?#bX=>Pv%2WRvPTDJP9PvPoP8C?#bP>%2VR8%2P%2XRo!x&'<#2Rw,!tk$;>Q0JPsX;>P7P8P^DJ%98fw13o=X;>PE!u#%13wqfxRs%2[#I/3!sA$QP!u%$%2S#I/3tfyRxP9%2]RyP=Px!tf$!sg$!u1$P9%2ZRxPuPsC?#b1Sy?%4y13@?Rs%2_Ru#FRz#4R{[[1S8?%48%Ft#4\s[1Sw?%4w%FxRw!s7%Vo?A:>?@Ro$07S0K%Nx#2=Bxw[1Yx?1c@?Rx%FyRw#4?Ow?[1Xy?1c?@Rw%2\Rs#FR8=Z?8[1[s?%Nu#A\o1Wu?%2`R|#FR}/1|\o%N|P>%21R~#FP>1Vy?Q0K%Ns#2=Bs8[1Ys?AO{z?\x1Xu?AZ?}}\w1[|?%N~!sx%~?%2aR~#F/1~\o%N~P>%2b#FP>%2m/V!sv$2OR~%N~#2%F~3B[1Y~?Q0D#2R~#FR}#4?O}!t0$~?%2j!s;$x=Z?x\w1[~?%2kR~#N!t<,l!t<1f]R~#2!u5$R:C11:CRo/UoRoePo1R7P117P!s8/kW11kW!s8,&0?MS0L&0=MS0M%aDS0N%aE7DC&0b>S0O&0a>RMQ00-0G>RoQ01#KRw5z>S0PQ00#yS0Q#KRx'C1Cxo1Cxw5z>3@20`MKS0RP=PD1xAB20_=D#5dB0^>@CH0]S0SbDbEbFX4>X5>X:>18=C/0D10D=10DC'8'1^4>^5>^:>P=P?PdP~O3bCbPbObNbjbgbMbLbKbJbIbibfbHbXbWbVbUbhb2bTbSbRb3b0blbmb[18W]/0?18vy'118Y\S0T/0?S0U1>|0R|X1FR0%N=5`qX7>P>Q0TA`q0=X7>g044lRyp4p710RvP!s0$210RyPC\CRB&0=DRAP3!#K&&Cw9GE=PHP=O1=:NDAGL=E'7X>N,{NR}[PE!s@%HCAGN=D'7X>H,{H!#Kk&Cw9GHC[R{!#GW$PECw9GND\}!#L2+I0\P=!#8x7wDW<WsWnW?P{^wD^<A^sB^ny^?vP=PFP>P0Q0</8_$0[R0PqPF11|t18X`R|#oS0V$0Z9GF='7X>F18U_S0W#oRtQ04$0@#jS04$04Rv/0_Ry&0EtS0X,0v'>10vU'1AGFt0S0YP>Q0W10v`Rt10v=S0Z!sH$2R0'1X7>1SyvS0[%4y%4vRB10v1RA/6vS0\#4S0][[S0^1S0vS0_%4010vW/6v#4\B[S0`10vZR0/SvS0a!sD%\R\/6vR0!sH&b10v]S0c/VvS0d%AvR]$07R{1<\v,0v=B\0[S0e1Y\vS0f1c@vR\16y!sg$?O0v[S0g1XyvS0h1cv@R016tvS0iQ0i5Zv[S0j1[tvS0k1<Av#A\]S0l1WAvS0m10vaR}/6vRz/1}\]S0n1<}vS0oP>10vbR8!u]$pP>1VyvS0q1<tv,0vQ0i5Bt\{S0i1YtvS0rQ0]Q0\;Ov\\S0]1XAvS0\AZvzz\0S0s1[}vS0t1<8vS0u!tS%v1W8vS0wQ0=,0vRz!t9$x/1z\]S0y1<zvS0zP>Q0@,0vRt/6vRyP>Q0D,0v!vJ$D10vjS0{Q0{/<!te%{/6v3B\{S0|Q0{/YvS0{10vkS0}!t,$~#4Q0~!tu&~Q0}/XvS0}10vlS10/6vS11Q115Zv\0!s1$0/[vS1010v~S12/<!v_%13Q12/WvS1210v:S14/6vQ14'1\]S15Q14/<vS16!vd$nS17!t$$8P>f`S19/RCQ19/1CR:/U:S1:eS1;Q1:1RmP11mPRm/UmS1<eS1=Q1<1R~W11~WR~/U~S1>eS1?Q1>Q0LQ0MQ0N&0Y>R~7DCQ0O20D>vRm/CoS0NAz>wo,Cm'\1CmwR:5@MQ0RQ!#4y0Q0Z18C=!{|'C!#4u&P=PjQ0GO2!#4qZQ0XQ0WQ0[Q0^Q0_Q0`Q0aQ0bQ0dQ0eQ0fQ0gQ0hQ0jQ0kQ0lQ0mQ0nQ0oP>Q0pP>Q0qQ0iQ!yq'Q0sQ0tQ0vQ0wQ0yQ0zP>P!x~%Q!x[$Q!x>$Q!w{$Q!wg$Q15Q16P>Q18P>Q!w%$Q!vp$Q!v_&4#j#j!#3+&-0B>S1>%^G#^S1?,u>5s>S1<!sM8=1u>GS1:!sI$;'MS16#pQ0L'TQ0M%aPS159D~H%aRS12?DL~7DD%aN%aQS13?DP~7DE!wx%PM!s$$!#Z0%20D>@RK9@MmJ0XS10&0WJRJQ0Q#ES11#E#K,CmS0}Q01#yRI#KS01'\9@M:ChPJPMPMQ10PJQ0N%yI!sS$/\x5@M!sD22#KS02!sq$~%E!sO%Q11#KRI'\!sU+A@MIKPJPMQ01=@M!s1&N,n:,]M!sG&xKS0NPJQ0P,nK,]MChFeFeFe!z$5X:>X\>X]>X^>X_>X`>Xa>Q08\]R:10vDS0810vPS0P;BN[Q08Q0P;BH\:10vLS!s5&Q\:%AQS0PQ0PQ!sW$N'3Q0P18RQ#4[!s#%!#<w'^\>^]>^^>^_>^`>^a>P=PNP^Q0<PYPHPnP[Q0GPjPSPWP_PgP7PePhO@!{Z[+0UEiP31kCD9GF=202DC20;DE-01C'7R3[202C=20;CD-01='71kDE9GFC[R71kEH9GFD\3B0RDC=!#;z9eFXvFXtFP7^eF^vF^tFP=Q0VPG182`R`#oR2202G2S0WQ0V-0;GS0P-012S0{'7%l`RG#4RF%l|R7,>@S0|,cGR3'7!}e${PFP31x>@S0{P2PGP=X>>R3%l!s-$FP`P`1x>`I0>R`H0Q!sI$`!wS$!};%VP7P3PFP|P|1x>|I0>H0SJ0PJ0T20A@|117|:00@|%~|%A7'7'Q18Z1#lP>18WaRa-0A@%laR1/1a:00@a%~a%A1!sO%Yb!sO$Szv%4zQ0>,0vR1/6vRa#4RZ\B[10vXRX/Sv%4XQ0c!#<v&1SAv%4AQ0p!s5%V}vQ0u,0vQ0p5B8\{1Y8vQ0x#4Q0x;Ov\\1XzvAZvyy\01[tv1<1v#A\]1W1v10vcRc/6vR8/1c\]1<cvP>10vgR}/6vP>1Vzv!#;p%=Bty\{1YtvAOZa!s~$1vAZv88\01[cv1<}!s~&}v10vfRf/6v/1f\]1<f!s|%e!sz$Q14/VvQ17Q17!#;4%183B\{Q17/YvQ19,0vR{/6vRf#4?Of!t:${vQ0E!s?+\=Zv\\01[{v10vdR{!#:n%1W{vQ0F!sN'/1{\]1<{vP>Q0G,0v!uK%RpC11pCRp/UpRpePp1RlP11lPRl/UlRlePl1RdW11dWRd/UdRdePdQ1=Q1?#^Rd#^#^#^Rl,u>Rp5s>Q1>1u>d5s>RdQ1<'M'M#pR{Q04$0O-0N>R]%^l#^,u>Rl60<>Q16'M#pQ1==s>lR0B0<>]pR]Q1;,Md!sf%Q16,Md,M],M0#pQ00!sr&>0<>lQ1:!sJ$0L,T{,T{'T!s$%!s1$Q0MQ13Q157DH%a[9D~L7DD%aS9D~NQ12!#7W/!#6D%~Q0Q#yR{!#7=%%K{R{!#6=,!sN+1,CmRlQ11#y!#79:1CmIRxQ0}Q03#KR0!sm-Q01Q025z>R]-05K,]MA@Mo]5tM20MMVA@MoK5tM60LM!sU%29z>IRI!sS,wI5tM1nIK,]!sZ$U!sU-A@M0K!s/&{!s/$1\lm/nx!#81%Q0~/nl!s3+NPJ1nKo,]M1\Kw-05o,]M5tM!#8C$!#8GMXq>Xr>Xo;Xp;10vH10v[RM;BR\:Q08?BM!#8G$Q?BMS\:18RLRL11EL600@%AE,7U'Q18PRRP11NP!s<$~P/7T'Q%A^RT1>Mv10v^Rv'313Mv%A[%4S1>@[7OS[[[\T!#8yC^q>^r>^o;^p;P=Q0@#A18nr#~!#98,Q0GPnPrP[Q0@Pb!#9=$Q0=Q0>PhPjPiPOPkOGbCb|b{bPbjbgbObN!#9I%ibfbJbI!#9I%hb2bVbUbTb3b0b[b~c04c0:bSc09bRH0yO4b0H0xQ0X#2,>u/1qQ0Y'7eH0uO6b0Q0U#NQ0T!#DF$P~Q0OQ10!wT/P:P=bCQ0Ke80s?Ei%2Y/8sP=DJb0bYbQb8bAQ0JP^EibYb@b8bBQ0IPVEibkb@bQQ0HP=EiWzZ08>PCP=O2!#:@/1102000b6WxZ06!sHAyZ07!sH@bQb0b@b0WQW@!sN7!s/%b9b040rW9P=O1Q0A,=4Q0A#I!#fO-i#5Q0BQ0CPiPePHPgP=O440q!s[%!s|-2110!s3&b9b0I0pQ0?eQ0?eWZWAWBW8PYP=Eib@W3PW!s0$!#p|%b3!s+%W0P=PR!#RV$O5W0!s^%!u5=W0W8!sD?X<5X>9!#SN&O4n20021!t~+00411!s7-Q0;9:5=Q09#g9d<N[X<5Q0:O1P=Q0;,x5O1!#v%+W}X?5X;>X=!wN/103!wN'0100Z059P=I0oW?o"). Qed.

Lemma NoDup_map_bv_unsigned : ltac2:(zQ "70!h9!jc!knf!pid!ho2!pj6!hv9>1l@1$4@1$1@1$0#k0>0@2$3@1$1@1$0#k0^1@2$3$2@4$5@1$1@1$0#k0$2@1$6@1$0#k0^2").
Proof.
  intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
  apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.

Theorem allowed_pages_bound : ltac2:(zQ "h40!h9!jc!knf!ho2!htd!mm3!inb!m2!kn6!it9!hu3!pgf!pi5!ng5!pid!io8!mnb!nq5!ipb!hv9>1A@1$3@2$9$2$2>5pages@1$3@1$1@1$0#k0>0@1$c^2>0@2$e@1$1@1$0#k0^2>0>1p@1$1@1$0#k0>0@3$6@1$1@1$0#k0^1^4@3$4$2@2$h0@2$h3@1$0#k0^2$5Z>0>1p@1$1@1$0#k0>0@3$6@1$1@1$0#k0^1^5@3$4$7@2$d^7^2$a@2$f@2$h1@1$h2@2$8@1$1@1$0#k0^5$5@1$b^6").
Proof.
  intros A pages Hwf Hnd Hal Hpa.
  rewrite <- (A_pages_length A Hwf).
  assert (Hlen : (length pages <= length (A_pages A))%nat).
  { rewrite <- (length_map bv_unsigned pages).
    apply NoDup_incl_length.
    - apply NoDup_map_bv_unsigned. exact Hnd.
    - intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
      apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_as_pages : ltac2:(zQ "50!ioe!htd!knf!mm3!nq5@3$1$2@2$0+2+k0@2$4$3@2$0+2+j4").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_woff : ltac2:(zQ "a0!h9!jc!ip5!htd!mq6!pjd!pkd!io1!ipb!hv9>1a@1$1@1$0#k0>1k$2@3$3@1$1@1$0#k0@1$4@2$6^2^1@1$5@2$7@2$9@1$0#k0^2@1$8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanAcct ()) ["FPX2"] "##mLp'0h02H0h14__x1h24__x2h31zh41Hh52H5h62H1h72H2h82H3h97__arithh:4__ffh;8__varmaph<5__with=6__sat2h>!s/%3h?4__x3h@4cstrhA5heq_zhB2H4hC2H6hD!sO%0hE!s/%1hF!sJ$rhG2r0hH3H10hI!s9$qhJ2q0hK2HahL!sT%4hM2H7hN2H8hO2H9hP4__p1hQ!sE%5hR1ahS2b1hT2b2hU1nhV1qhW2q1hX2r1hY3H11hZ3H12h[3H13h\3H14h]3H15h^3Hdmh_3Hflh`3Hpsha2Hzhb1bhc1khd5lemmahe2q2hf1rhg2r2hh1xi001xhi1yi011yi022x'i032y'p%0p&0p;1p;2p;3p;4p;6p;7p;:p;9p;8p;@g001Qj19Tg0026j1q!s/$Tj1STg003Qj22Tg004_j1BTg005?R0j26Tg006hk20KTg00@Wk10DTg00Y9j21Tg00C`j1`Tg00?Uj1yTg01iYj2hTg01jBj3g!s/$kj2tTg00Dak10OTg00c4j3rTg00EAk10N!s0$aj2eTg00F?k10I!s0$]j4^Tg00G;k10C!s0$Yk10@Tg00Hgj2a!s/$Dj2]!tc$Uk105Tg00K<k203Tg00A`j2w!s9$^k200!uc$7j3?k10>Tg00LJj3|!s/$ij4{!uy$;k30V!uz$\j2_!ux$Bj2RTg00=oj1QTg00o?j1xTg01fgj2uTg03=oj2!tJ$A@j23Tg01hMk20U!v1$5k30TTg03a6j3YTg03[Ij2Kk30?Tg01cVj1sTg03ZHR1j27!sP$gj2HTg03bNj2ITg03c5j2L!s/$[j2JTg03ejk20!s0$fSk30HTg01lik30GTg01MMk60FTg01mLk70ETg04<Jk10=Tg04=:k20<Tg01n0k10;!s:$[j4mTg04>Bk10:Tg04?1j4l!s/$hk309Tg04@^j2kTg04AJm:08Tg04B7m906Tg04C1j3Wj2j!x]$Ej2!vg$<9R2j2N!sF$bk404Tg00[^j6oTg04DCk30!z<$8hj6pTg009Fj2cTg00:5k201!sL$hk10LTg04E`k10MTg00Imj4fTg00JXj7~!s8$Jj3}Tg00Z7k80PTg03lVk30Q!v|$ek60RTg04F[m@0STf0R3#9!s$%p=zg00=QR4f1R5'V/N3p=Gg00<TR6/w3p=CA?653p=41V43p=0P6P5g00]<P3Cfp=b!s4$T2R7g00TQR8P8g00U1R9P3g00V8F~p=;A}!sj$Of3R:P7P8P8P9f2R;P5P3L0Pp=Pg03?BR<,73/5<p=E173<p=:153<p=8%93#9p=v!tK'c!tK%Z1143p=TA?634p=@15;5/639?6:p=>11;51V34'Np=M1153,N;p=d!sr$!s$/p=XB0Q!to$A!t/&UQ!t/%[P5!t}'P3J0Rp=n11;5/N3p>0B1V34p>0AP6P4f6R=P0f5R0g01F;g04GFf4R>g04Gcg04HLP:P;P5P<P<P3N@0Sp>07!u#&p=F16;5=?63p=D133<p==113<p=<1553,6;p=\16539?6;p=iP6P>!sv&3Epp=Ug00;6R?#9R@#9#zS00#qRA#SS01g00QC12A5%B3'6S02P620KA;12A;RB&0DARC,1B'G12A:%B;'6RB#C145BRBePB%`:%B:#0P212A0RB#011BC12A=%B0'6#0P;f7RB,2A#0f8RD,2ARE/1Cg00SFRFg00=2RG#yRH#y,h61h6HRH1h6GRG5g65g6g01oXRI't&0OFRJ3r&0NFRKP61e6;RLP5&0I6RMC^&0C6RN&0@6RO1a64RP1]6@RQ'b,;O&058RRPO1]6?RS,bP,;OPR1OSQ!s2%CPCP203O9RTP3P;g00VXRUg00W8RV'w2003;=?UVdA|645C{RVb:b;b<X16X26%05RU16;:#0\U[^16^26P3f9RW#Bf:RX,2AP0P;O4b9W0W4P5P3O2n20010!s#$12!s-%0b@bAPUeP!ww$[RU%S3RY%S5RZP2%S;??5312:;12:5'4R[[12;512;3'4%S:??;5[R\%S>??:;\[B0V;53P3!t77WTWSWUP\^TZ^SY^UUP3PA1_A:,2AS03#ES04,_AS05%E:RU!s1$6Q04,RA%:>RY#8RZ,_A,2AR\,43X361RA:S07%E3R[,RA/4\!s;%US081RA>#E!s<$3X36P6%Q@R@%x?R\#9R]#x#vR^#QR_'uR`,5<Ra13>3#E/3313Z3'4X3613:aP6PJPKPMPNQ00#v#zRb#QRc,a6,Z!x@$TP!w^&%TcP3b9114<RcePc130aRd!zv$dReePe%BB,6ERE#C14=EREePE%`D%BD#020U@_S09%T@%0_%T`[RE[S0:%0@Reg01QjRfB0T@_5UWKS0;%0`\f^KeReAYXaD%0aRff;R_/3a#0[1K_a%@aRg#sRhf<RiPa17ia13iaC>[1Hia%TaRjf=Rk/3aRl11la'G[1Ika11a4Rlf>Rm/3aRn=Man[1Lmaf?Ro/7aRp#@\g1Joaf@Rq/3aRr/4q\g17qaS0<P6fARs/3aRtP6P2fDRu,2ARv#011vCPhPsfFRv!}O%GS0=,2A/1CPWPsO1%0>S0>?d>aS0?PmfBRwO1PEP2%0=S0@11=aS0APhP5%0DRx11WaRyp-0Rz%Xb#X!s$&Q-0J6>0H6H=g6G/tI=rFJPKP6P6PMP;PLC^P5PMC^PNPOPO1a6@%q^60G6R^,ASRM/!xD%RPO!#6e&1]6]R],ZM,;O!s<,P>J0FK0ECPPRPO1Z]M!s]&1ZPS,;OS0BPR1[MP,;O,n!~K$CP!yC,!}{%WP153`/14155`RM@0B;:[11;M%T;15:`#@g00bWS0C[[[!~C&^PzP3&0A_P_P<PoP5fHRzO6b9WCW0!~E6!s/&b=b0W5WB!sH>GbVb8b7b6b0b4bDbEb=b@bAbF:0?0aP0Pa170aPdC>17=aP615a3S0D/6:Rd,4BP6&0>6R]&0=6%:DR9#8S0E15a5R8/6>S0F#:R7#8%Q?!wU$5P4!s-'20<53R?#QRF&0;?R?n011!to$30010103!s'$!s]+?PF!sH9!s<$0!s<,2!s'$Xi6Xh6P]P9P7P6^b6R7^R6R9P6P7P]!s|$]P]CmRFCmR?!s<$F!s<%&0:6ClCl:099?P1PDQ0FP3P<P<1k6<R1N:08P1K07168ZR8P81k68N906WdP517BaR1#C1431R1eP113D!s7&>!s7&2A_%BX'6!s<%W!s<%%`_%B_R1#0Q09Q0:Q0;PeAYka_%0n\fAWmai%0p\f1KoaPqPaQ0<PrC>\h1Hqa%0tS0G?dta\j1Isa13waRp=Map\l1LwafCRn/7a!}~%na13ua/4u\g17uaS0HP6fER?/3aS0IP6P212AzR9#0119C15`q#8AFaqn5DnP?fJR9!~'%KR],2AS0J!~,%?O1Q0?PoPv!}y%Q0@Q0AfIRF15`v!si$vF3DP5P!}R%LP51e6:C^S0KPN1A^QS0L1]6\R\'A,OS1A\^/AQS0M/OS'[!#6u/!|X%X?615`5RL/5;15;`/55S0N/635D3!|F&?6!x$$9fMR7O3b9XCyX0x!#;_=>!|@FJ!|@4>!|B%bI15`3#8=D:dP6%8L,6>S0O%E0Rd9Fa;S0P,4[X3616YL%83Q0P!#9j$7DaRY#C145YS0QeS0RQ0Q13W!s<&0YS0SeS0TQ0S12Ai/61!yS%X1S0UeS0VQ0U%`iS0W%Bi#0S0X!y\-1jX<%0XS0Y1V4<R1%:i#0[[AYoak%0r\fAWqam17saS0Z#0\f1Kk<A?6<4Rr#sRYPmP<%:m%=mC>[1Hm<%=oS0[Q0[#<'G\c1Io<11<4R4%=qR[=M<[[1Lq<%:s#@\r1Js<%=w/4w\r%:wS0\P6%=nS0]P61KzaPFPa17Fa13Fa!{6%Fa139aS0^Q0^/1a'G\j1I9a13]aRI=MaI\l1L]afLRG!{;+Ga137a/47\g177aS0_P6fNRH!{;$`P6P2fQRb,2AR{#011{CA\W`F#8PaPF%8WC>PHfSR{!{@%TR|!#:D'H!{=%sfOS0aO1%0iS0b%<i'NPzfPR}!#:N&B11BaA\q`}!s{$}%8qR~C>P;%0W11XaP2%0w%<wA\u`|!sI$|%8uC>P0%0uR0%<?PJPKQ0KPNQ0L,OS/A\Q0M1AS\'O!{e<63L/5;Q0N153;3i!{\0fXR`PzO3b9W8!#8t7!{Z&W7W6!{V>Lb0b5WHWO!sJ>XbWbNbMbCb5bB!|0:L!|2'Q0O#:P>PLP<Q!{O$Q!{?$Q!{+$Q0WQ!z|0AYmai13oa#0\fAWoakQ0<!zd%qaPsPaQ0ZPt!yO%sa11pa,Gp\j1Iwa13n!#5\,naQ0H!yC%uaQ0I/4?\g17?aP613va!#5N%FRp#011pCPYPvQ0J#012AG!xy%v!xy%oQ0=!#59-PY!#5&$1e65PNPOQ!#>D$S!#>D'!x#0%T3%@5Q0C[[^1!wn$P7O2!#4H~!w<%H04DUQ0FP3Eob4O2%EBQ0D;iUP813daRB133aRy'4X36!w]GWm<i%:oRe#0\11j_<%0_%:k#0\1[AYqamQ0G\fAWsao17w!x+$1Km<PoP<PeQ0[C>\Y1Ho<%<[,G[\c1Iq<%=sRq=M<q\41Ls<Q0\!#3G$w<Q0]/4n\r%:nP6%=uP61KFaP9Pa179aQ0^!xo%9a11Ia,GI\j1I]a13GaR]=Ma]\l1LGaQ0_!xo%7aQ0`/4H\g17HaP6Q0a/3aP61K}<PbP<%:b%=b!tq%b<fRRY#=Rg%<g!#5F$Y<%={RY=M<Y\41L{<%:|!tx%|<fUR{#=/4{\r%:{P6fVR{#=P6P2fYRr,2AR4#0114C15baAFab~5D~P{f[!#4%$\!#4#'{O1Q0>%<>'NPsfWO1Q0b?diaPFP`O1%<u,N0PbPr!zI%Px%<D%8zRz15raAFarz3DP:Q0Y%<_P2%0n11na%8GRGf]Rn/5aAFanG3DP=%0?11vaP2%0H%<H%8}RHfaR2!sJ%2H3DPW%0}%<b!#4P'1ASQRS1AQ^R^,A\'O1A^\!#==?35RV15;MAFM;V3D!#4W,feP<P|O3b9WH!#4U?5W8!{c=!#4sAQb0b5bHW]W\!sL>gbeb[bZbYbHbO!#5'IQ!#>9+5a=DZ8P6A\d;aR8%E=/3aR=/4yX36PB14=3X36%CB138aB02d;aDUQ0P!}I%Q0EP3DUb_bVb^b`bfQ00#Q,u@g04I3EpQ07#E,RAQ08'4eQ06,2A1cAUDUQ031cA:DUQ05,2AQ04,cADUO4b4babKb3Q0120153$0LQ02$0M3?eWcWRo"). Qed.

Lemma page_base_of_aligned : ltac2:(zQ "70!knf!htd!h9!pjd!mm3!mnb!hv9>1z$0@3$1$0@2$5@2$6@1$2#k0@1$3^1$4Z").
Proof.
  intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
  rewrite (Z.mul_comm (z / page_size) page_size).
  rewrite Zmult_mod_distr_l.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma page_insert_nodup : ltac2:(zQ "50!h9!jc!pid!ho2!pl5>1p@1$1@1$0#k0>5pages@1$3@1$1@1$0#k0>0@2$2@1$1@1$0#k0^1@2$2@1$1@1$0#k0@2$4^3^2").
Proof.
  intros p pages Hnd. unfold page_insert.
  destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
  constructor; [|exact Hnd].
  intros Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma page_mem_false_not_in : ltac2:(zQ "90!h9!jc!m2!iqf!ho2!htd!ko2!pm4!inb>1p@1$1@1$0#k0>5pages@1$4@1$1@1$0#k0>0@3$5$2@2$7^2^1$3@1$6@3$8@1$1@1$0#k0^3^2").
Proof.
  intros p pages Hm Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : ltac2:(zQ "70!h9!jc!pid!ho2!ip5!knf!pn0>1n$4>4base$5>5pages@1$3@1$1@1$0#k0>0@2$2@1$1@1$0#k0^1@2$2@1$1@1$0#k0@3$6^3^4^2").
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : ltac2:(zQ "70!h9!jc!ho2!pid!ip5!it9!po5>4accs@1$2@2$5@1$1@1$0#k0$4>5pages@1$2@1$1@1$0#k0>0@2$3@1$1@1$0#k0^1@2$3@1$1@1$0#k0@2$6^3^2").
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : ltac2:(zQ "70!h9!jc!inb!ho2!htd!pp7!pl5>1p@1$1@1$0#k0>1q@1$1@1$0#k0>5pages@1$3@1$1@1$0#k0>0@3$2@1$1@1$0#k0^3@2$6^2^1@2$5@3$4@1$1@1$0#k0^4^3@3$2@1$1@1$0#k0^4^2").
Proof.
  intros p q pages Hin. unfold page_insert in Hin.
  destruct (page_mem q pages); [right; exact Hin|].
  destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : ltac2:(zQ "f0!h9!jc!ip5!inb!ho2!jv5!htd!lo1!pp7!isb!knf!pn0!pjd!io1!ipb>1n$2>4base$a>5pages@1$4@1$1@1$0#k0>1p@1$1@1$0#k0>0@3$3@1$1@1$0#k0^1@3$b^3^4^2@2$8@3$3@1$1@1$0#k0^2^3@2$7$2\1k$2@2$5@2$9^1^6@3$6@1$1@1$0#k0^3@1$c@2$d^5@1$e^1").
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
  - left; exact Hin.
  - destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin''.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : ltac2:(zQ "h10!h9!jc!ip5!lo1!inb!ho2!it9!jv5!iu0!htd!pp7!isb!po5!pjd!io1!ipb!hv9>4accs@1$5@2$6@1$1@1$0#k0$2>5pages@1$5@1$1@1$0#k0>1p@1$1@1$0#k0>0@3$4@1$1@1$0#k0^1@2$c^3^2@2$a@3$4@1$1@1$0#k0^2^3@2$3@1$1@1$0#k0\1a@1$1@1$0#k0@2$3$2\1n$2@2$3$2\1k$2@2$7@3$4@2$6@1$1@1$0#k0$2@4$8@1$1@1$0#k0$2^3^2^7@2$7@2$b^1^2@3$9@1$1@1$0#k0^5@1$d@2$e@2$h0@1$0#k0^3@1$f^1").
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
  - left; exact Hin.
  - destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : ltac2:(zQ "h50!h9!jc!ho2!inb!jv5!m2!it9!htd!knf!hu3!ip5!ko2!ppd!mr3!mm3!pra!ng5!lpe!pid!mnb!hv9>1H>0@1$1@1$0#k0$5>1A@1$2@2$6$8$8>4lazy@1$2@2$6@1$1@1$0#k0@1$1@1$0#k0>3mat@1$2@1$1@1$0#k0>6ranges@1$2@2$6@1$1@1$0#k0$a>0@3$f^5^3^4>0@2$h1^6^2=3new@1$2@1$1@1$0#k0@3$c^5^4^3@2$4@2$h2@1$1@1$0#k0^1@2$4>1p@1$1@1$0#k0>0@3$3@1$1@1$0#k0^1^2@1$b@3$3@1$1@1$0#k0^2^7@2$4>1p@1$1@1$0#k0>0@3$3@1$1@1$0#k0^1^2@3$7$8@2$h3@2$h4@1$0#k0^2$eZ@2$4>1p@1$1@1$0#k0>0@3$3@1$1@1$0#k0^1^2@3$7$5@2$d^2^8$9>1p@1$1@1$0#k0>0@3$3@1$1@1$0#k0^1^2@3$7$5@2$h0^9^2$9").
Proof.
  intros H A lazy mat ranges Hcov Hav new.
  assert (Hchar : forall p, In p new ->
            page_in_ranges p lazy = true /\ page_mem p mat = false
            /\ exists a n k, In (a, n) ranges /\ (k < n)%nat
                             /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
    destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter.
    apply accesses_pages_nodup. constructor.
  - intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
    apply page_base_of_aligned.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
    pose proof (Hav a n Hin k Hk) as Hw.
    rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
    exact (Hcov (woff a k) Hl Hw).
Qed.

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : ltac2:(zQ "80!h9!jc!ho2!it9!htd!nh6!nme!nqc>1l@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0>1X@1$2@1$1@1$0#k0>1m$5@3$4@1$2@1$1@1$0#k0@1$6@3$7^3^2^1^2").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : ltac2:(zQ "82!h9!jc!ho2!it9!htd!nh6!nid!nqc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1l~1>1X@1$2@1$1@1$0#k0>1m$5@3$4~1@1$6@3$7^3^2^1^3").
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : ltac2:(zQ "90!h9!jc!ho2!nja!it9!htd!nh6!pg5!nqc>1l@1$2@2$4@1$1@1$0#k0@1$1@1$0#k0>1X@1$2@1$1@1$0#k0>1m$6@3$5$7@1$3@3$8^3^2^1@1$3^1").
Proof. reflexivity. Qed.
Lemma eager_used_wvb : ltac2:(zQ "90!np7!ho2!htd!h9!knf!nh6!nid!nqc!jc>1X@1$1@1$8@1$3#k0>1m$5@3$2$4@1$0@3$7@1$6^1^2^1@1$0^1").
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : ltac2:(zQ "50!nh6!htd!nid!nme!nqc>1m$0@3$1$0@3$4@1$2^1@1$3^1^1^1").
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma MInv_wvb : ltac2:(zQ "h90!h9!jc!htd!knf!inb!m2!ho2!hu3!nid!it9!nh6!nja!mr3!mm3!ps8!nqc!pgf!pt4!np7!ng5!pid!io1!io8!mnb!hv9>1A@1$6@2$9$3$3>1m$a>1X@1$6@1$1@1$0#k0>0@2$h4@1$1@1$0#k0^1>0>1p@1$1@1$0#k0>0@3$4@1$1@1$0#k0^1^3@3$2$3@2$h7@2$h8@1$0#k0^2$dZ>0>1p@1$1@1$0#k0>0@3$4@1$1@1$0#k0^1^4@3$2$5@2$h3^7^2$7>0>1p@1$1@1$0#k0>0@3$4@1$1@1$0#k0^1^5@3$2$5@2$c^2@1$8^7$7>0@2$h6@2$h5@1$h2^6@1$h0^7@1$e@1$b^6@2$h1^8@3$f@1$8^7^6^7").
Proof.
  intros A m X H1 H2 H3 H4 H5. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
    assumption.
Qed.

(* [comment removed for export] *)
Theorem materialize_restricted : ltac2:(zQ "h40!ho2!h9!jc!nh6!nid!it9!knf!nqc!pt4!jte!m2!ip5!l9!jv5!htd!lo1!ptc!pi5!pra!lpe>1H>0@1$2@1$1#k0$a>1A@1$0@2$5$6$6>1m$3>6ranges@1$0@2$5@1$2@1$1#k0$b>0@3$h2^4@1$4^2^3>0@1$h1^4>0@2$8^5^4>0@2$h3^7^4@2$f@1$0@1$2@1$1#k0\4mat'@1$0@1$2@1$1#k0@2$d@3$e@1$c$3@2$h0^7^6@2$9$3@3$7@1$4^7^1^7@2$8^8@3$7@1$4^7^1^7").
Proof.
  intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
  destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
    as (Nnd & Nfresh & Nal & Nlz & Npa).
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
                      (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
  assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
                      page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
  pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
    as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  destruct new as [|p0 new'] eqn:Enew.
  - exists (m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true.
    2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
    exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
Qed.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!ho2!hre@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)
Variable H : ltac2:(zQ "30!m2!h9!jc>0@1$2@1$1#k0$0").
Hypothesis HH : ltac2:(zQ "10!sja@2$0?4segs?1H").
Hypothesis Hwx : ltac2:(zQ "10!sgf@1$0?4segs").

(* [comment removed for export] *)
Definition node_ok : ltac2:(zQ "30!qi7!ho2!qj1>1c$0>1IT>3evs>0^1@1$1$2>2nx>0^2$0P") := ltac2:(zQ "a0!ho2!qj1!jv5!htd!qja!qi7!qk3!ql0!qp2!lo1\1c$5\1IT\3evs>0^1@1$0$1\2nx>0^2$5@2$2>1i^3@5$6?4segs@1$8?2SC^5@1^3^1@1$4@1^2^1>1e@1$0$1>2st$7>0@5$6?4segs@1$8?2SC^6^2^1@2$9^6\1i^6@2$2@3$3@1$0$1^4@1^6^1@3$3$7^3@1$4@1^5^1").

(* [comment removed for export] *)
Theorem mi_account_step_restricted : ltac2:(zQ "h80!q7!nh6!ho2!it9!nid!jv5!htd!h9!knf!lkd!lg2!nqc!qpe!jc!iu0!lo1!u3!mhb!qq6!qr9!ls6!qs1!lt0!ltc>1A@1$2@2$3$8$8>2ms$0>4msr'$0>5model$1>0@3$h5?1H@1$4^1^4>0@1$h3^5>0@2$c^6^3>0@3$6@1$a$0@2$h1?4segs@2$h6?1H^6@2$9$0^5@2$f@1$2@1$d@1$7#k0\4mat'@1$2@1$d@1$7#k0@2$5@3$6@1$a@2$3$0$1@3$h2?4segs^8^6@2$9@2$3$0$1@4$e$0$1@3$h7?1H@1$h0^8^7@3$b@1$4^6^1^6@2$5@2$c^9@3$b@1$4^6^1^6@2$h4?1H^7").
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
    as (mat' & Hmat & Hinv').
  exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
  split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.

(* [comment removed for export] *)
Lemma sstep_instr_det : ltac2:(zQ "h60!q7!nh6!htd!qj1!ho2!it9!h9!qsf!ql0!jc!m9!jh5!l9!iu0!jv5!lkd!lg2!hh5!qja!qq6!qk3!qp2>2ms$0>5model$1>3ms1$0>6model1$1>1e@1$4$3>2st$8>0@3$2@1$c@1$9@1$6#k0@1$h1^6@1$a@1$9@1$6#k0>0@3$2@1$h0@2$5$0$1@3$h3?4segs^7^6@2$f@2$5$0$1@4$d$0$1^5^4>0@5$h4?4segs@1$h5?2SC@2$7^8^7^4^3@2$e@3$2@1$4$3^5@1$b$3@3$2$8^4@1$h2@2$7^7^6").
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss. apply sstep_cfg_sub in Hss.
  inversion Hss; subst;
    match goal with
    | Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
    | Ha : mi_account_step segs ms model = _ |- _ =>
        rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
    end.
Qed.

(* [comment removed for export] *)
Theorem node_instr_restricted : ltac2:(zQ "i10!q7!nh6!jv5!htd!h9!jc!it9!qt8!m9!l9!knf!lkd!lg2!u3!qsf!qpe!ltc!ho2!jh5!iu0!lo1!hh5!mhb!qq6!qj1!og7!nid!qr9!ri0!ls6!qs1!lt0!rib>1A@1$h1@2$6$a$a>2ms$0>4msr'$0>5model$1>0@3$he?1H@1$ha^1^4>0@1$hb^5>0@2$f^6^3>0@3$3@1$9@1$5@1$4#k0@1$h9^4@1$8@1$5@1$4#k0>0@3$3@1$9@1$5@1$4#k0@1$h5^7@1$8@1$5@1$4#k0>0@3$3@1$c$0@2$h6?4segs@2$hf?1H^8@2$b$0^7@2$h4$1\6model'$1@2$2@2$f^b^1@2$2@2$i0^8^1@2$2@2$hd?1H^9@2$2@3$3@1$c@2$6$0$1@3$h7?4segs^a^8@2$b@2$6$0$1@4$h3$0$1@3$h0?1H@1$d^a^9^1@4$hc@2$e^a^8$7\0$7@1$h2$h8\0$7@2$e@3$h0?1H@1$d^b^a^2").
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
    as (mat' & Hacc & Hinv' & Hcl).
  exists (with_vm_backing (m_vm_lazy model) mat' model).
  split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
  split; [exact Hacc|].
  split.
  - intros []. apply sstep_cfg_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt.
    exact (sstep_instr_det ms model _ _ e st Hsvc Hacc Hss).
Qed.

(* [comment removed for export] *)
Lemma step_hclean : ltac2:(zQ "60!q7!ls6!htd!lkd!lg2!mhb>2ms$0>3ms'$0>0@2$1?1H^2>0@3$2@1$4$0@2$5?4segs^3@2$3$0^2@2$1?1H^3").
Proof.
  intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
  destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
  exact Hcl.
Qed.

Lemma msteps_hclean : ltac2:(zQ "30!q7!ls6!rne>2ms$0>3ms'$0>0@3$2?4segs^2^1>0@2$1?1H^3@2$1?1H^3").
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
  - exact Hc.
  - apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.

Lemma unrestrict_munrestrict : ltac2:(zQ "71!h9!jc!l9!q7!ltc!htd!ro8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1f~0>1g~0>3ms'$3@3$5$3@3$4?1H@3$6?1H^3^2^1@3$4?1H^3^1").
Proof.
  intros f g ms'. unfold unrestrict. f_equal.
  apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

(* [comment removed for export] *)
Variable P : ltac2:(zQ "10!qi7>0$0P").
(* LPS 727298f3: a silent step is an instruction ([ShapeAlg.rz_node] asks [RomBase.sys_rob],
   which an instruction configuration has for nothing) *)
Hypothesis P_silent1 : forall c c',
  node_ok c unit (fun _ => []) (fun _ => c') -> ms_svc_pending (cfg_ms c) = None -> P c' -> P c.

Theorem rz_msteps_restricted : ltac2:(zQ "h50!q7!htd!h9!knf!qsf!nh6!qpe!jc!m9!ho2!l9!it9!u3!og7!nid!qr9!qs1!lt0!rib!ltc!rne>1A@1$9@2$b$3$3>4msr0$0>4msr'$0>0@3$h4?4segs^2^1>2ms$0>5model$5>0@3$1$0^5@2$h1?1H^2>0@3$h0?1H@1$e^2^7>0@1$f^8>0@2$6^9^4>0@3$1@1$a@1$7@1$2#k0@1$d^5@1$8@1$7@1$2#k0>0>6model'$5>0@2$6^c^1>0@2$h2^8^2@1?1P@2$4@3$h3?1H@1$c^a^c^3@1?1P@2$4^8^7").
Proof.
  intros A msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
    intros ms model -> Hcov Hwf Hinv Hh Hk.
  - specialize (Hk model Hinv (same_but_materialized_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
    apply (P_silent1 _ _ Hnode Hsvc).
    pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
    + exact Hwf.
    + exact Hinv1.
    + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
    + intros model' Hinv' Hsame'.
      rewrite unrestrict_mem, unrestrict_munrestrict.
      apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
(* [comment removed for export] *)
Theorem rz_msteps_restricted' : ltac2:(zQ "h60!h9!knf!q7!qsf!nh6!qpe!jc!m9!ho2!l9!it9!htd!u3!og7!nid!qr9!ls6!qs1!lt0!rib!ltc!rne>1A@1$8@2$a$1$1>2ms$2>4msr'$2>5model$4>0@3$h1?1H@1$e^1^4>0@1$f^5>0@2$5^6^3>0@3$b@1$9@1$6@1$0#k0@1$d^4@1$7@1$6@1$0#k0>0@3$h5?4segs@2$h2?1H^7^6>0>6model'$4>0@2$5^a^1>0@2$h3^8^2>0@2$h0?1H^a@1?1P@2$3@3$h4?1H@1$c^c^b^4@1?1P@2$3^9^7").
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
  apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma materialize_model_accesses_nil : ltac2:(zQ "a0!nh6!jte!ip5!jh5!l9!it9!htd!h9!ptc!jc>1m$0@3$6@1$4$0@2$8^1@1$3@2$5@1$9@1$7#k0$2@2$1$0^1").
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
End FPX3.

Section SyscallNode.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : list Segment.
Context {SC : StepCfg}.
Variable H : word -> bool.

(* [comment removed for export] *)
End SyscallNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX4. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Definition seg_top : ltac2:(zQ "20!knf!hre>3seg$1$0") := ltac2:(zQ "50!ihf!hre!iie!ikc!io1\3seg$1@2$4@1$0@1$2^1@1$0@1$3^1").

Definition wx_segs_nowrap_b : ltac2:(zQ "30!m2!ho2!hre>4segs@1$1$2$0") := ltac2:(zQ "b0!hre!ii7!ho2!rp7!rpe!ija!il8!ru4!ruf!mi2!ioe\4segs@1$2$0@3$8$0\3seg$0@2$4@1$3@2$1@1$5^1@1$6^1@2$9@1$7^1@2$a+2+k0^1").

Lemma wx_segs_nowrap_of_b : ltac2:(zQ "70!m2!ho2!hu3!htd!hre!rva!sgf>4segs@1$1$4>0@3$3$0@1$5^1$2@1$6^2").
Proof.
  intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
  rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
  apply Z.leb_le in Hb. exact Hb.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma MInv_transport : ltac2:(zQ "h00!ho2!h9!jc!it9!htd!knf!nh6!nid!nme!qpe!nja!ps8!si1!sic!io1!io8>1A@1$0@2$3$5$5>1m$6>2m'$6>0@2$9^3^2>0@3$4@1$0@1$2@1$1#k0@1$8^2@1$8^3>0@3$4@1$0@2$3@1$2@1$1#k0@1$2@1$1#k0@1$7^3@1$7^4>0@2$f@2$e@1$d^4@1$c^6@1$b@1$a^4@2$9^7^5").
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.

End FPX4.
(* [comment removed for export] *)
