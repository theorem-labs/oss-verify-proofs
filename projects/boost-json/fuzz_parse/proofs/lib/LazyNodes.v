(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the mmap decline premise (place_declined_b). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Scfg SimInv ExitSim PropExec CatSim MmapSim AllocSim RelSpec
  ShapeAlg Nodes AgentNodes Gap04 RefNodes SReach AllocNodes
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_LazyNodes () := KReplay.lz_vm "#&p:C47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?Krespectful_per_oblig!t3$_1C4ELinuxProcessSemantics?!s<22Fs4path!t6,4Init5Logic6eq_ind!sB88eq_trans!sD87f_equal!sa<ind_rI!tsJ5State7Fs!s-$00!s|29Datatypes3appC46Stdlib9micromega5Tauto5eKindI!sE;8GFormula!t-#!tf95Riscv7Prelude5bvmapC35stdpp7tac!sJ#<!up&_helpC!uWQPipeBufI!uU;6op!xL#00K!y+,Numbers7BinNums8positive02!sK=1N02I4!u-%9bitvector;defini!t0#s2bv00!tV<4prod!tT/!sF3list01!utQJmaterialize_model_ac!sH#esK!v/C1I!y~72eq!ts#!tSO5M!tG#!sv4!uQ3!s|R7Vm!zx%1K!tv;1I!tvW!xwH3!uC<3nat!xU#!}<Qd!}<&I!uzY!s^SIo!s^X9!s7#!s`X8Li!tyY9Time!s`X6VmMaps!#4$<!s]4Monad4bindC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd:ex_introF4C13~~~C7!skN8ShapeAlg7node_ok!sj&!#9iL2Fs!~{Q8m_halted!~iD2!t#K>!#7s#!sE+>ms_svc_pending!v/P4Scfg8the_scfg!v+Q3Run9sys_input!#4v9x!y0NSpecs<syscall_specK!ykP7outcome!vh#!t[63notK!uRPstep_cfg04!vsP5NodesA!se+!wd$inv!v}Q!yU%G!v,'effect!#9O'!w583and!w6O!z^&killed!s]Q4m_fs!vlO6config!#8}L!wI20K!uh<!#:::x01!xw89False_ind!#<QQevent04!vHQI!w#'_of_!~k'_none!{DZ1!}WODspurious_refusal!vk#!sgO<apply!z=&!s_O@advance_past!{i#!yDO7!xf$to!xJ#!wiV3!#CgA2!#4\8or!#;ER=S!}U%E!v=$!sdM!uZ00!v8X2I!v8W!tpL!#9[1=machine_s!#>d&!v_64Tru!sB;5!}'$!}}:!s_%1c!#6dN9Lazy!#6h#C!#=c#chk_ev_mat_!#:i'I!|pY0!#968iff!tp`family!tp1!#9OO7RelSpec6Ok_inj!sh^<Un!#Ko#ed_O!#A;%!uQZN!#Lk<_nil!t&`?!vU2!#</P!{$25ms_pc!scZ:fetch_word!shZ8is_ecall!}7[!vt%_repor!}~]>!}~'result!#>lL!sn2Ddec!wc#exec!x_+!srZ6ms_mem!sdZ=!wa,_ov!#GjZ!sk%tail_any!tYafailur!#=uK!whB1!snj2!snj3!v;Z7m!z{#g!y;[8ms_f!sf^9!~]$_val!#VxF1!#\q=Z!vi#!#\qB1!{r^reg!w&`sv!se^fcsr!u2_om!y~Z!#?H1!v_<!#cQ%D!#4-#C:!#46%!}k$!w[?7Z_to_bvK!s}@3Sem4cor!tND!sO$exe!#9GZCinterp_eff!#6=b<!#8h%value!u+E6c!}=@!sO,7c!}#A!vP/!#<H=!tH2!z[=!sO0!zE^?!vn&d_ranges!y_IBis_!yE$ed_illegal!tNZ=!#Hp#!xC,!zT?4BvWf!|?[!#>P0!#fx=bool!#ik>!sF$!#4`Z=memory!ug&I!w3@5Instr5i!s+#!#JF-!#6b50I!}_J0!#G#O<LazyRestrict8r!s/&!#GpU6!so#SR8hid_same!#K7%!siPSReach6sr!s,#00!#GR_G!z40!#EA$_gen!#`bT?mi!sn#ount_!s{#!v5W;lzok!#X:%!v{V?!wl/Alg<!#J##!tc&!svV!xd0?lazy!~z&_okb!#c|Ucfg!#LZ$I!z:]!tT$inv!xf'!tOO6!tO$s!w`W>hidden_zero_on!{`]4rsub!#cYV8m_vmmap!#jgQ7vm_!s\#K!tzW!zM#01!yPc7!vZ%b!vSW!~J%>!~J%_silent1!#3;V!uH/!yQ&!#8$<!#{5#!#eIO!#e~&!#6UP7MmapSim6unfill!w/c<!#7?&!#O~#!yz&!#<6>;bv_unsignedC5!$%^%6ZArith6BinInt1Z3leb!sC=ad!s`?tb!$'A;4andb!$'B'!#[r$HFunc!th#alExtens!s1$ityIf!s?+_e!s@0!{tQ;region_free!tJ+4Bool!s'$=!tb#_true_iff!t%Q:iv_overlap!uj=negb!$/f8and!$0I5!sa,8list!sH$6!zTJSys2Mm4!yy#Bmmap_off_al!x[$_b!smW;!sm$anon_bC5!sfM7!#fm%5w_is0!tHW>!tH$!#_b&!u3X?!si$no!#D,%!sjXE!sj$fix!#nI#!sp_?!sp-rw_b!z&Q9alloc_top!}2<2le!|%Rvm_reserv!#u'R<!uA#contains!#e-WC!#\u#!#48&!#?K$!#;jV<!v6+_l!#q+K!#i<$!wc#!x7]pglen_ok!{~Y7err_re!u$R9u!#h[&!u-WA!u-%lain!~0^:errno_from!wpQ?page_round_up_Z!u9WH!~0&!zt&_backed_ok!{_U!~''!z,Rvm_start_br!tCR6vm!s[U8vm_limit!tuU!vI$bas!~sR:vm_init_sp!#yHP!$4O&!$=jQ;with!#Ff&!{<W!sf$!uc&cking!#@'<eq!#6tQ=!td#_subtrac!wJR9!|7%!~C#!uMVM!#9n6span_next!w`Q!#|j11!t^WL!#:\0!tX$budget!}4#!swVG!sw6!uQ#!srWI!~u+place!#=?aC!st2!#=C#!#;&V<!so$err_ou!#T;&!#=S<t!sB<6leb_g!sF=>pow_pos_nonne!{f>pow!sC<:!sk#!sg&!$Ln49SatDivModCZ_mod!sP&!t@C7div!sU#!ta=div!sC=mul!sC<=!tT#!uk#bound!sMA!tx#!sM15!uL$8PreO!s/#1Z;!tx#0_r_!zA#!sL=!st#!sL'!$B3R9LiaTuning9zify_done!y+B7compare!#Qn;!$Hm#2K!ww5=RingM!$Qu'Psatz!sOM6!sO6:Z!sL+;!tu%!uk$!s{86VarMap1t!sDB1!sD@3I!sD?0I!uCC7!$T\'!t567Env!sT#5PExpr!tv8!sI21!sIE7!sIE3K!u,L1!$WN;8B!sJ&C!wn@=Z!sT$CheckerC!vl<4f!#Q>#!sq?C!sq0_s!|\$!#he+!$\g3?eq_p!$^##!s,#xy!sR?M!$[k#_co_!$[<#v_impl_m!sE&!#GIP>bind_get!#PI$!$@?8or!#;KX!#:R1!#;F'!t4<2!#KXQa!#8T?tb!#LR#!t:65proj2!sa=eqb_eq!#9W@le!v1W9!v1$spec!t+=modulo!v%Q4pure!sYQ!t6#ify!s[Rchoos!uqXE!#EP+!#>i%men!#@N]!yn%destroyed!#AD[C!tf,!ss+!snWB!{T1!t]$!#3&&5Lists4!s+#2InK!#4V;!$d_'4!sJF3!sJF5!sJF8!#wgA2!#I?Q!#Qo#size!$-j?!#LfQ:two_pow_64!#z-<unit!$[8R9!#5S'!xcW;!#F2&nos!#:HC3Op2!wX>4ki!$PC5!uU3!$c]Q<!#L;%Input!$T2R6EINVAL!t@Q7MemCopy!t;UNOMEM!s[SEXIST!y%<:!#D@$ison!#A87!#C+:0!#Dq@1!#CwM1!y-I3!#>14!$u82>iff_Tran!$8[$!#}gY4keff!#arV7eff_ret!tFZ6sysre!$GR'!v};or!#VsK!$8t2set!$:B#!#sgV5z!#sfY8PropExec:bv_eqb_neq!v|Q!$:L5gpr!w+[kflags!tP%!sjZ5kpro!wo'!#5kU@m!#bU1!voP:!tV#Ledger;gran!#7D&!zpV6in_arg!s[Q8in_sysno!y^QExitSimB!sd'_!$hP'!ykV!#Xa&@!$hC-_222!xF`;!#sd#_false!tc^E!xM&!#[{%!$WC%!sw&!$pIVand_elim!$pI'!sk`5!uQ^!#nj$rw!uK2!#3WVA!z:%5!xva!ss14!sso3!ss3!ylZB!su%2!su,'!svg1!sv4!}FX!uc&0!ucj6kgate!#6]`!#5u$kerne!~7%!uUV!$-T/:in!$9,%b!sqc@!sq,!#3-/!#6@O>!$+r,_In!$+u5>!$+u#f!$oU$ff!#Ts@g!#qIQ=!$:`%terio!#<6ZB!u:/not_in!v%W9m_vm_!t_#!wZ]7li!sh%!xJU!#<:,@!#<:,!sufH!su/!$eA,d!s}aB!s}/!#u<%!sw`<!sw%!sq0!x0PA!x0$!uX/!$G/Z!$t_-_mem_un!tc,!s{ZF!s{4zero!sz&!#URE6!#98W:!$<<$!#q^,!slW9z!sk^!$G`0!$=,-_by!svcD!$HX1_con!vr&I!#Zq55NoDup!$OW_li_nodup!u0c9all_page!{R+!t}54incl!#4=`!sh$!yz%!uj^!$K/&1!}NW4m_f!%+JTio!#J`Qm_fsys!s[Tproc!s[Q5!$-8#!t7Ttim!#;eR!tj#st!$Rc&!#6VYG!$+v3_nonvm!z52!#=g%:!s,%_dec;Z_lt_le!s2#!#ZU16Specif7sum!$[`$!#AI]z!#@W&!#AIcA!$Ms%!~c$!#<$-!#@e4<or!$F[,!#4}\!#Bc,!#4$+!#M+`3!u}V!$Y&&rsu!ut&r!slh2!v_'!#[J:fst!sC=s!#vz,!wA-!#E$,!#CzZ8k!#]x%!tn%!$~[Z!#:''!#^//!x|\@!z>'!yo+!tl_!st#_frame!tmj>!#;r+!$]K,!}o]eager_us!#DxW!sq0;!#;N#_tota!#:K&!#AGD7!#y#76eq_sym!}9T?P!#u>&SearchB!$Bs1_!$HT+!$VD>5!#b9#!tLdG!tL3!$Qb%!tQG7bv_wrap!sLA=!sL&_small!sRA@!$uO%!$K\'!$k==N!$,j7!#jd5!${f@3!#;4Z>entries_no!u{$!#5\[!$\/+svc!#3m`!#gM$_!$mAdD!$j2#!#=\&!}0#_l!#UNW?vm!sm0!t[W8!t[$!%Js+!~\\9li!$,H%!~Z<!$31&3Po!%\O4!#?s%3s!$bR#!sB89proj1_si!#n1X>!$@~$!ue$tro!ugV:Alloc!x}$A!$Bi&t!%G7&!x0Q!$mU#!%Gq&bK!v&=!%HtOL!%Ht3!to/!vSP!$Wo&!$Ck-_eno!$e_+!suO!%Uv#D!%<p%off!#FH$true!wMaE!$KL$i!ug,!t##!~G`D!#ae-!#Wt$!%Z~'!ttZF!$Zd$!tq'!wk'!tu`!#ZX/!$v_-!svZ=k!%,Y/!sq_E!%BM-!#nv#!%E~Y!#3g/E!#bE/!#<:1!w_P!#9^+<entry!#9\\!sq-K!#B#+!yL&cover!#8'-!t$ZF!t$4rw!s{+!#6eB3!sGC2!xSZA!#f/-app!#Kr&!suk!%Ih`@!#:u#after!vR%!wIV!$wQ%;!$wQ%!{;#!{}a!#D=0n_fact!#P{]9ex!#Pz$1!xy<!$Ll74!y%>!$I<%5!uYZ6f!$%D,!#^J67ex!s2#b!sB7>!sB&_!s-%!|=[2lo!|~a2hi!w[]!#UX+2!#5GbB!#dD2In!sycCseg_disjoint!#ZN0!ws7forallb!$9FJ<MemImageType7Segm!%[p#!#@O:!&#206!$1E$!$X|<su!$]=XB!$c/'!$~X+!#69B!{m&4!#@rT>!#CZ'!#?p,!#:=[commi!$0_/!}OZ!$cf1!s~&!$&T0!$:nC;r!&1$%ity!uI[J!tW8!uWe6f!#~g,!}oa7!v-K=iff_!&44+!v0Z5zcovb!y?a4zin!sibC!tU$_!$m$0!sx`!$$j-!uZ-!#vxZ!#5d2!#C;fA!z>/!#}<eI!sv0!#}=lC!s~0!#|K\!#^N$outside!%#|%!#8G56filte!#fUZE!#do&!yb7!#h5:6length!$,p<of_na!%~\3Peano2le00!s`34Znat5Nat2Z6inj_l!u`8<!#yA#_!uf%!sG79!sA%!$/}-!sD-A!se%incl_!u7&!#=2[@!#yA'!sq'!xOVG!#[Y,within!$|N%!v<=9i!$ph&!$M;M3!u^]E!#]L1_spli!#3qa:zinb!$A_[!so-9!so$!#W>Y!u]0M!#4^2!#6XmB!~m0!#xV-!v^\!#8K#!#uS,!soZ=!th&!$2if9no!%>}&!snU!%PN/!%Z^%!t\`L!#T4,!u[&!#U72!#h$[!%8|,!#I[X!tv-G!tv5!#V,,!#7yZaddr!#b&-!#_MdF!#D7,!tv&!$B:Y8!#_O#SimB!%0:,!%V20!#juSforge!#M8%!t[QRef!uV%!sl2!#`2fA!#W|,!vR%!uV'!#7_%!#}6+;!%I/+r!uuQ7!w^#has!#5Q\!$&--!#6I,!tTP:!$O?#emov!%K]7neg!#}7+!vl[!#3f'_In!#Rt#!vl<A!{a#!t=%s!#9]%!#ZO^2!#6cam!$?p#!#8M$L!srV!#ox&<!so/!sn^=!#]p/!so^>!t_&args!#k<X!$S;'!sp&!#RA%_si!ss^:!ss&!$e_+!x$Z4cut!#9~a:rem!%1d$!sob3r!#r$&!|NZ:!#3/%!#:QcD!#:Q,!w0&!#:Na@!{?/_eqL!toaB!}#0!#P6eJ!sw1!#P7l!~y'!#B^fD!ts1!sy\!|T'C!w[0!%lB[!#C`%7!#;R#LM!y>`?!$;'#!#9a,!ss_F!#=4,!#e:'o!#5e&!#}\M<injected_arm!v:P!#ba#!#:K#!#~G'n!%<5'!#;m\!#wt1!su`C!$Ob/!%fe-!swZG!#pe764!w>Q!$[E%TASK_SIZE!%iaN;I!wv&Arm!$G'Q!ww$E!x^/!ww$_21!$j5%".
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State05Model37Corelib4Init9Datatypesj54Somej53natj53nilj56optionj54prod37Corelib4Init5Logicn02eq37Corelib7Numbers7BinNumso94Npos0hamaterialize_model_accesses35stdpp9bitvectorbdefinitionss62bv0dSyscallEffect3h5LinuxProcessSemanticsfLinuxProcessSem3Runv79sys_inputj54list3h5LinuxProcessSemanticsfLinuxProcessSem5Specshj6csyscall_spec05eventn03not3h5LinuxProcessSemanticsfLinuxProcessSem5Monadho12Okj54Nonen03andv75mkCfgv7h4spurious_refusal_cfg08m_halted69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~huc8the_scfgn02exho19Unmodeled3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsik1dmachine_stateik1ems_svc_pendingv7h0advance_past_svcv7capply_effect0h7syscall_effect_accesses69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~it87node_okho17outcomen03iffik1daccess_reportj54boolj54truen01Iik1h3Build_machine_stateik19MachineOkik1afetch_wordik18is_ecallik1emachine_resultik1dmemory_accessik1emkAccessReportik17ms_fcsrik18ms_fregsik16ms_memik15ms_pcik19ms_pc_valik16ms_regik17ms_regsik17ms_resvik16ms_romik1dstep_accessess62BVs64BvWf69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~kk48restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~kof4lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~kt06sreachv76configkof8hid_samekk4crestrict_mem69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~lj86unfill0bregion_freej53appo91Zj55falses6bbv_unsignedj54consj54pairn02or07MemCopy09mkEffectU0cSyscallInput06VmMaps09alloc_top09errno_ret08m_vmmaps0cmap_contains0fpage_round_up_Z09page_size07vm_maps0bvm_reserved0bwith_vmmaps5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapml3bmmap_anon_bml3bmmap_errnosml3h9mmap_fixed_destroyed_nextml3h5mmap_fixed_noaccess_bml3fmmap_fixed_rw_bml3h7mmap_fixed_rw_budget_okml3h2mmap_fixed_rw_nextml3emmap_modeled_bml3fmmap_noaccess_bml3h2mmap_off_aligned_bml39mmap_specml3h3with_mmap_destroyedml3h5with_mmap_replacement4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscallnpe5w_is069OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~ntbcmmap_err_out36Stdlib5Lists4Listoi52In46Stdlib6ZArith6BinInt1Zoje3addoje2leoje2ltoje6modulos67Z_to_bv07eff_ret79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LazyNodes8WithSegs~~~~~~oo64keffik17set_regs66bv_addoo66sysretkk47hiddenblj85zfillik16ms_gpr06in_argoo66kflagsoo65kprotj54negbml3h0mmap_noreserve_bml3h8mmap_noreserve_backed_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~pm3bgrant_modelkk4ain_rangesbj54andbj53orb0dlazy_interior08vm_limitkk4aeager_usedkk4elazy_range_okbkk4bpages_totaloje3muloje3powpm3eentries_nowrapoo66fflagspm32hipm32lokk4flazy_ranges_okbv79refusal_b08in_sysnopm3ccommit_model0dmaps_subtractpm34zinb0bvm_noaccesskk4azin_rangebpm39nooverlap0h1m_vm_materialized09m_vm_lazyoi55NoDup07map_haskof4rsub0amap_removepm3dmunmap_modelLlj8cmunmap_model09TASK_SIZEpm34cutspm33rem3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTyperk07Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma materialize_model_accesses_nil : ltac2:(zQ "a0!ie!kd!l4!la!m0!m9!o4!q2!q9!u3>1m$0@3$6@1$4$0@2$8^1@1$3@2$5@1$9@1$7#k0$2@2$1$0^1").
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

End FPX1.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hif!rn5@1$0$1").
(* [comment removed for export] *)
Context {SC : StepCfg} {AF : AllocForced SC}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_chk_ev_mat_cfg : ltac2:(zQ "hc0!ie!u8!o4!q2!u3!hi3!hif!m0!hm4!hn4!hnb!hqf!hr5!kd!hrc!hs2!hsa!hu2!ii3!iif!ij4!in8!io9!ipb!iqf!q9!ire!jh3>2ms$h5>5model$0>2x8@1$4@1$3#k0>1IT>4effs>0^1$1>3ms'>0^2$0>4ms''>0^3$0>3evs>0^4@1$6$9>0@3$2@1$7@1$4@1$3#k0@1$h1^7@1$c@1$4@1$3#k0>0@3$2@1$7@1$4@1$3#k0@1$h6^9@2$d@1$4@1$3#k0^7>0>1i^7@3$8@3$5?4segs^b^9^a@4$b$1@1^7^1@1^6^1@1^4^1>0>1i^8@1$a@4$h0@1$h2?2SC@3$5?4segs^c^a^b@1^8^1>0>3eff$1>2m'$0>2ev@1$6$9>0@3$8@3$5?4segs^f^d^e@4$b$1^3^2^1>0@1$a@4$h0@1$h2?2SC@3$5?4segs^h0^e^f^4@2$h3^e\1i^e@2$e@3$2$1^6@1^e^1@2$e@3$2$0^5@1^d^1@3$2@1$6$9^4@1^b^1>0>3eff$1>2m'$0>2ev@1$6$9>0@3$8@3$5?4segs^h0^e^f@4$b$1^3^2^1@3$2@1$7@1$4@1$3#k0@1$h1^3@1$c@1$4@1$3#k0>0@1$a@3$8@3$5?4segs^e^c^d@1$h4$1>0>1i^c@3$2@1$7$0@2$h9@1^b^1@1$ha@1^c^1@2$d$0@1^a^1@6$hb?4segs?2SC@2$f^h0^f^d^9\1i^d@2$f@1$h7@2$h8^h1@1^d^1@1^b^1").
Proof.
  intros ms model x8 I effs ms' ms'' evs Hh Hsvc Hok Hns Hinv Hnh Hnu Hmat. split.
  - intros i. apply (sstep_cfg_syscall segs the_scfg ms model x8 (effs i) (ms' i) (ms'' i) (evs i)
                       Hh Hsvc (Hok i) (Hns i) (Hnh _ _ _ (Hok i)) (Hmat i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hs & Hm & ->)
                                     | [(Hh2 & -> & Hs & Hm & ->)
                                     | [(code & Hh2 & _ & -> & ->)
                                     | (sig & Hk & -> & ->)]]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + exfalso. rewrite (Hnh _ _ _ Hc) in Hh2. discriminate Hh2.
    + exfalso. rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hc)) in Hk. discriminate Hk.
    + exfalso. exact (Hnu Hc).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_family_mat_cfg : ltac2:(zQ "he0!u8!ie!o4!q2!u3!hif!m0!hn4!hnb!hqf!hi3!hr5!kd!hrc!jhe!hs2!hsa!hu2!ii3!iif!ji9!ij4!in8!io9!ipb!iqf!hm4!q9!ire!jh3>2ms$h6>5model$1>2x8@1$4@1$3#k0>1IT>4effs>0^1$0>3ms'>0^2$1>4ms''>0^3$1>3evs>0^4@1$5$7>1R>0@1$e$0P>0@3$2@1$6@1$4@1$3#k0@1$h1^8@1$b@1$4@1$3#k0>0@3$2@1$6@1$4@1$3#k0@1$h7^a@2$c@1$4@1$3#k0^8>0>1o@1$e$0@2$h4@3$ha@3$a?4segs^c^a^b^1@1^4^1>0>1i^9@1^5@4$9$0@1^9^1@1^8^1@1^6^1>0>1i^a@1$8@4$h0@1$h2?2SC@3$a?4segs^e^c^d@1^a^1>0>3eff$0>2m'$1>2ev@1$5$7>0@1^9@4$9$0^3^2^1>0@1$8@4$h0@1$h2?2SC@3$a?4segs^h2^h0^h1^4@2$h3^h0\1i^h0@2$d@3$2$0^6@1^h0^1@2$d@3$2$1^5@1^f^1@3$2@1$5$7^4@1^d^1>0>3eff$0>2m'$1>2ev@1$5$7>0@1^a@4$9$0^3^2^1@3$2@1$6@1$4@1$3#k0@1$h1^3@1$b@1$4@1$3#k0>0@1$8@1^8@1$h5$0>0>1i^e@3$2@1$6$1@2$hb@1^d^1@1$hc@1^e^1@2$c$1@1^c^1@6$hd?4segs?2SC@2$f^h2^h1^f^b\1i^f@2$f@1$h8@2$h9^h3@1^f^1@1^d^1").
Proof.
  intros ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hmat.
  apply (node_chk_ev_mat_cfg ms model x8 I effs ms' ms'' evs Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc Hs. apply HR in Hc. exact (Hout _ _ _ Hc Hs).
  - intros eff m' ev Hc. apply HR in Hc. exact (Hnh _ _ _ Hc).
  - intros Hc. apply HR in Hc. exact (Hnu Hc).
  - exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_family_mat : ltac2:(zQ "hc0!q2!u8!u3!o4!ie!m0!jhe!hr5!kd!hqf!hs2!hi3!hu2!hif!iif!ji9!hnb!in8!io9!ipb!iqf!hsa!hm4!hn4!q9!ire!ii3!jh3>2ms$h1>5model$4>2x8@1$2@1$0#k0>1IT>4effs>0^1$1>3ms'>0^2$4>4ms''>0^3$4>3evs>0^4@1$d$h7>1R>0@1$6$1P>0@3$3@1$5@1$2@1$0#k0@1$c^8@1$7@1$2@1$0#k0>0@3$3@1$5@1$2@1$0#k0@1$h2^a@2$8@1$2@1$0#k0^8>0>1o@1$6$1@2$f@3$h6@3$b?4segs^c^a^b^1@1^4^1>0>1i^9@1^5@4$9$1@1^9^1@1^8^1@1^6^1>0>1i^a@1$h0@4$h5@1$ha?2SC@3$b?4segs^e^c^d@1^a^1>0>1o@1$6$1>0@1^7^1@2$e^d\1i^d@3$3@1$6$1^3@4$9$1@1^d^1@1^c^1@1^a^1>0>1i^c@3$3@1$5@1$2@1$0#k0@1$c@1^b^1@1$7@1$2@1$0#k0>0>1i^d@3$3@1$5$4@2$h8@1^c^1@1$h9@1^d^1@2$8$4@1^b^1@6$hb?4segs?2SC@2$a^h1^h0^e^a\1i^e@2$a@1$h3@2$h4^h2@1^e^1@1^c^1").
Proof.
  intros ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hns Hout Hh' Hmat.
  apply (node_family_mat_cfg ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hns).
  - intros eff m' ev Hc _. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
  - intros eff m' ev Hc. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->). apply Hh'.
  - intros Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
  - exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_family_noacc_cfg : ltac2:(zQ "i00!u8!q2!u3!o4!hif!ie!hn4!m0!hnb!hqf!hi3!hr5!l4!m9!hrc!jhe!hs2!hsa!hu2!ii3!kd!la!iif!ji9!ij4!in8!io9!ipb!iqf!hm4!ire!jh3>2ms$h9>5model$5>2x8@1$2@1$1#k0>1IT>4effs>0^1$0>3ms'>0^2$5>3evs>0^3@1$4$6>1R>0@1$f$0P>0@3$3@1$7@1$2@1$1#k0@1$h2^7@1$b@1$2@1$1#k0>0@3$3@1$7@1$2@1$1#k0@1$ha^9@2$h4@1$2@1$1#k0^7>0>1o@1$f$0@2$h7@3$hd@3$a?4segs^b^9^a^1@1^4^1>0>1i^8@1^5@4$9$0@1^8^1@1^7^1@1^6^1>0>1i^9@1$8@4$h1@1$h3?2SC@3$a?4segs^d^b^c@1^9^1>0>3eff$0>2m'$5>2ev@1$4$6>0@1^9@4$9$0^3^2^1>0@1$8@4$h1@1$h3?2SC@3$a?4segs^h1^f^h0^4@2$h6^f\1i^f@2$e@3$3$0^6@1^f^1@2$e@3$3$5^5@1^e^1@3$3@1$4$6^4@1^d^1>0>3eff$0>2m'$5>2ev@1$4$6>0@1^a@4$9$0^3^2^1@3$3@1$7@1$2@1$1#k0@1$h2^3@1$b@1$2@1$1#k0>0@1$8@1^8@1$h8$0>0>1i^d@3$3@1$4@2$d@1$2@1$1#k0$c@1$he@1^d^1@1$h5@2$d@1$2@1$1#k0$c@6$hf?4segs?2SC@2$h0^h1^h0^e^b\1i^e@2$h0@1$hb@2$hc^h2@1^e^1@1^d^1").
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hacc.
  apply (node_family_mat_cfg ms model x8 I effs ms' ms' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu).
  intros i. rewrite (Hacc i). apply materialize_model_accesses_nil.
Qed.

Lemma node_family_noacc : ltac2:(zQ "he0!q2!u3!u8!o4!jhe!m0!hr5!hif!l4!m9!hqf!hs2!hi3!ie!hu2!kd!la!iif!ji9!hnb!in8!io9!ipb!iqf!hsa!hm4!hn4!ire!ii3!jh3>2ms$h4>5model$d>2x8@1$1@1$0#k0>1IT>4effs>0^1$2>3ms'>0^2$d>3evs>0^3@1$7$ha>1R>0@1$4$2P>0@3$3@1$5@1$1@1$0#k0@1$e^7@1$6@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#k0@1$h5^9@2$f@1$1@1$0#k0^7>0>1o@1$4$2@2$h2@3$h9@3$c?4segs^b^9^a^1@1^4^1>0>1i^8@1^5@4$a$2@1^8^1@1^7^1@1^6^1>0>1i^9@1$h3@4$h8@1$hc?2SC@3$c?4segs^d^b^c@1^9^1>0>1o@1$4$2>0@1^7^1@2$h1^c\1i^c@3$3@1$4$2^3@4$a$2@1^c^1@1^b^1@1^a^1>0>1i^b@3$3@1$5@1$1@1$0#k0@1$e@1^a^1@1$6@1$1@1$0#k0>0>1i^c@3$3@1$7@2$9@1$1@1$0#k0$8@1$hb@1^c^1@1$h0@2$9@1$1@1$0#k0$8@6$hd?4segs?2SC@2$b^h0^f^d^a\1i^d@2$b@1$h6@2$h7^h1@1^d^1@1^c^1").
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hns Hout Hh' Hacc.
  apply (node_family_mat ms model x8 I effs ms' ms' evs R Hh Hsvc HR Hin Hns Hout Hh').
  intros i. rewrite (Hacc i). apply materialize_model_accesses_nil.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_accesses_ecall_gen : ltac2:(zQ "he0!q2!in8!u3!o4!kd!jif!jk0!la!m0!jk7!jke!jl2!jma!jn7!jo5!jp1!jq3!jr4!js6!jt1!jtd!ju7!jv0!jvd!kg7!kh2!khd!ki7!kj8!kjd>2ms$1>1w@1$2@1$0#i0>0@3$3@1$8@1$2@1$0#i0@2$d?4segs@1$h5^2@2$4@1$2@1$0#i0^1>0@3$3$6@1$e^2$9@3$3@1$f@1$5$1@2$hb?4segs^4@2$c@1$5$1@3$h1$1@8$b@1$h8^4@1$h3^4@1$h6^4@2$4@1$2@1$0#k0@2$h7^4@3$hc@1$0#5+h1Kv$a@2$hd@1$0#5+h1@1$h9^4@1$h2^4@1$h4^4@1$ha^4@1$7$h0").
Proof.
  intros ms w HF HE. unfold step_accesses. rewrite HF. unfold decode_exec_accesses. rewrite HE.
  destruct ms; reflexivity.
Qed.

Lemma sreach_ecall_lazy : ltac2:(zQ "i22!q2!u3!o4!in8!hs2!hif!m9!kd!m0!ko3!ks8!lg9!hr5!jk0!jk7!jke!jl2!jn7!jo5!js6!jt1!jtd!ju7!jv0!jvd!kg7!kh2!khd!io9!lh3!ie!lhc!kj8!kjd&@2$6@1$1@1$0#k0@1$1@1$0#k0&@1$5~0>1L~1>1S~1>2Zr~1>2ms$3>3msF$3>2mo$he>1w@1$1@1$0#i0>1Q>0$hdP>0@5$a?4segs^8^7^6@2$4^4^3>0@3$2$3@3$9^9^8^5^6>0@3$2@1$8@1$1@1$0#k0@1$hc^7@1$c@1$1@1$0#k0>0@3$2@1$8@1$1@1$0#i0@2$h1?4segs@1$h6^8@2$7@1$1@1$0#i0^5>0@3$2$d@1$h2^6$e>0>4msF'$3>0@5$a?4segs^e^d^c@2$4^1^9>0@3$2$3@3$9^f^e^2@8$h0@1$h9^c@1$h4^c@1$h7^c@2$7@1$1@1$0#k0@2$h8^c@3$i0@1$0#5+h1Kv$f@2$i1@1$0#5+h1@1$ha^c@1$h3^c@1$h5^c@1$hb^c>0@4$hf^h0^f^c^3@4$b?4segs?2SC^a@2$4^4^c@4$b?4segs?2SC^7@2$4^a^9").
Proof.
  intros L S Zr ms msF mo w Q Hok Hr Hsvc HF HE Hk.
  set (msF' := {| ms_regs := ms_regs msF; ms_fregs := ms_fregs msF; ms_pc_val := ms_pc_val msF;
                  ms_svc_pending := Some (ms_reg msF 17); ms_resv := ms_resv msF;
                  ms_fcsr := ms_fcsr msF; ms_mem := ms_mem msF; ms_rom := ms_rom msF |}).
  assert (Hacc : mi_account_step segs msF mo = MachineOk (msF', mo)).
  { unfold mi_account_step.
    assert (HF' : fetch_word segs (ms_pc msF) = Some w) by (rewrite <- Hr in HF; exact HF).
    rewrite (step_accesses_ecall_gen msF w HF' HE). cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  assert (HsvcF : ms_svc_pending msF = None) by (rewrite <- Hr in Hsvc; exact Hsvc).
  eapply sreach_silent1.
  - apply node_account; [exact (lzok_halted Hok) | exact HsvcF | exact Hacc].
  - apply RomBase.sys_rob_instr. exact HsvcF.
  - apply Hk.
    + destruct Hok as [HL Hinv Hh HZ]. split; cbn in *; assumption.
    + subst ms. destruct msF. reflexivity.
    + intros a Ha. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma restrict_mem_unfill : ltac2:(zQ "83!q2!u3!hif!m0!m9!li8!ln2!o4&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$2~0&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1L~1>1S~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m~2@3$7~2@3$5^5^4@3$6^3^2^1@3$6^3^2@3$5^5^4^1").
Proof.
  intros L S a n m. apply functional_extensionality. intros x.
  unfold restrict_mem, restrict_mem_by, unfill.
  destruct (hiddenb L S x), ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma region_free_app_r : ltac2:(zQ "92!q2!u3!m9!jk0!hif!jk7!o4!lnc!lo9&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2X1~1>2X2~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$6$3@3$7@3$8~0^4^3^2^1$5@3$6$3@3$7^4^3^2$5").
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [exact H|].
  cbn in H. apply andb_true_iff in H. apply IH. tauto.
Qed.

Lemma region_free_app_l : ltac2:(zQ "92!q2!u3!m9!jk0!hif!jk7!o4!lnc!lo9&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2X1~1>2X2~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$6$3@3$7@3$8~0^4^3^2^1$5@3$6$3@3$7^5^3^2$5").
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [reflexivity|].
  cbn in H |- *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. cbn. eapply IH; exact H2.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_rw_commit_outcome : ltac2:(zQ "ja4!q2!u3!o4!la!jk0!m9!jk7!lof!u8!lp3!lpb!jhe!lq9!hif!l4!lr0!hrc!lr7!hqf!lrc!hn4!ls5!iif!ji9!ie!lt0!lte!lu6!lv1!lvc!mg6!mh4!mi5!lnc!mj0!mj9!mk6!mo7!mp6!mq5!ms3!mtd!mv0!ngc!ni3!nj5!nk8!nlf!nmc!no4!nt2!oh5!oj8!ol6!old!om3!om9!on3&@2$5@1$1@1$0#k0@1$d@1$1@1$0#8&@1$3~0&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$3~2>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$h9>1m$h8>1o@1$b$8>0@3$2$4@1$ie^4$6>0@3$2$4@1$i5^7$6>0@3$2$4@1$j2^a$9>0@3$2$4@3$ic^a^9^7$9>0@3$2$4@3$id^b^a^8$9>0@3$2$4@3$i8^c^b^9$9>0@3$2$4@3$i9^d^c^a$6=1h$ha@1$hd^9=2nZ$7@1$hf@2$a@1$0#k0^h0=1n@1$1@1$0#k0@2$j9@1$0#k0^1>0@2$j6@2$j5@2$a@1$0#k0^h3^2@1$hb^3>0@3$2$7@2$j8@2$a@1$0#k0^h4$i0Z>0@2$j7Z@2$a@1$0#k0^h5>0@3$2$4@3$i1@1$i3^6^h6^4$6>0@3$2$4@3$he@1$i2^7^h7^5$6@2$h7@9$if^h8^h7^h6^h5^h4^h3^h2^h1^h0@2$h1@2$j3^h1^h0@2$h1@2$h0@3$2$4@4$ia^h5^h1^h8^6$6@3$2@1$b$8^h0@4$h2$8@6$h5^h8~1@3$c~2@4$f@1$1@1$0#k0@1$1@1$0#k0^h8^6~3~3@1$3$h3@1$3@2$5@1$1@1$0#k0$e@4$j1^h5^h8^6@2$i4@3$ib^8^h8^6^h1@1$3$h4@2$h6$7\1e$7@2$h0@3$j4$7^1$i6@3$2@1$b$8^h1@4$h2$8@6$h5@1$hc^1~1~3@3$c~2@4$f@1$1@1$0#k0@1$1@1$0#k0^h9^7~3@1$3$h3@1$3@2$5@1$1@1$0#k0$e@4$j0^h9^7@3$i7^9^h9^7^h2@1$3$h4").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption | reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. split; [exists tt; split; [exact Hb | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kprot : ltac2:(zQ "20!jk0!lof>2na$0$1") := ltac2:(zQ "20!jk0!lof\2na$0M0\2na$0$1^1Z+3").
Definition kflags : ltac2:(zQ "20!jk0!lof>2nr$0$1") := ltac2:(zQ "20!jk0!lof\2nr$0M0\2nr$0$1^1+kgi2+i2").
(* [comment removed for export] *)
Definition fflags : ltac2:(zQ "20!jk0!lof>2nr$0$1") := ltac2:(zQ "20!jk0!lof\2nr$0M0\2nr$0$1^1+kgj2+j2").

(* [comment removed for export] *)
Definition keff : ltac2:(zQ "40!q2!u3!jk0!u8>2na$2>1a@1$1@1$0#k0>1n@1$1@1$0#k0$3") := ltac2:(zQ "c6!q2!u3!la!m9!jk0!lq9!hif!l4!lr0!lrc!ls5!u8&@2$3@1$1@1$0#k0@1$6@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2&@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1&@3$5~2~4~3\2na$4\1a@1$1@1$0#k0\1n@1$1@1$0#k0M4\2na$4$b^3@6$a^2~1~3~5@1$2$9@1$2@2$3@1$1@1$0#k0$7@6$a^2~1~5~3@1$2$9@1$2@2$3@1$1@1$0#k0$7").

Lemma keff_ret : ltac2:(zQ "60!q2!u3!jk0!o4!ond!osb>2na$2>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$3@1$1@1$0#k0@1$4@3$5^3^2^1^2").
Proof. intros [|] a n; reflexivity. Qed.
Lemma keff_accesses : ltac2:(zQ "a0!q2!u3!l4!m9!jk0!hif!la!o4!ire!osb>2na$4>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$7@1$5@2$3@1$1@1$0#k0$2@1$8@3$9^3^2^1@1$6@2$3@1$1@1$0#k0$2").
Proof. intros [|] a n; reflexivity. Qed.

(* [comment removed for export] *)
Definition sysret (ms : machine_state) (r : word) (M : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs (set_reg ms 10 r); ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc ms + Z_to_bv 64 4; ms_svc_pending := None;
     ms_resv := None; ms_fcsr := ms_fcsr ms; ms_mem := M; ms_rom := ms_rom ms |}.

Lemma restrict_sysret : forall L S L' S' msF eff,
  restrict L' S' (advance_past_svc (apply_effect msF eff))
  = sysret (restrict L S msF) (eff_ret eff)
      (restrict_mem L' S' (ms_mem (apply_effect msF eff))).
Proof. intros. destruct msF. reflexivity. Qed.

Lemma hid_frame_sysret : ltac2:(zQ "f2!q2!u3!hif!m9!o4!jtd!iqf!jk0!m0!jk7!in8!ipb!u8!ov1!lhc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>3msF$a>3eff$c>0>1a@1$1@1$0#k0>0@3$4$7@3$d^5^4^1$9@3$4@1$8@1$1@1$0#8@2$5@2$6^4^3^2@2$5^4^2@4$e^5^4^3@1$b@2$6^3^2").
Proof. intros L S msF eff H a Ha. cbn. apply H. exact Ha. Qed.

(* [comment removed for export] *)
Lemma apply_effect_mem_zeros : ltac2:(zQ "h02!q2!u3!la!m9!jtd!lq9!hif!l4!m0!lr0!o4!in8!iqf!lrc!ls5!ovc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2ms$b>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a>0@1$1@1$0#k0@1$8@1$1@1$0#8@1$4@2$c^3@6$e^2@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8@3$5~0@4$9@1$1@1$0#k0@1$1@1$0#k0^2^1~1~1@1$2$d@1$2@2$3@1$1@1$0#k0$7@3$f^2^1@1$4^3").
Proof.
  intros ms a n. cbn. apply functional_extensionality. intros x.
  unfold zfill, zmem, zeros_cover. cbn.
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.

Lemma apply_effect_mem_unmaps : ltac2:(zQ "h02!q2!u3!la!m9!jtd!lq9!hif!l4!m0!lr0!o4!in8!iqf!lrc!ls5!ln2&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2ms$b>1r@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a>0@1$1@1$0#k0@1$8@1$1@1$0#8@1$4@2$c^4@6$e^3@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~1@3$5~0@4$9@1$1@1$0#k0@1$1@1$0#k0^2^1~1@1$2$d@1$2@2$3@1$1@1$0#k0$7@3$f^2^1@1$4^4").
Proof.
  intros ms r a n. cbn. apply functional_extensionality. intros x.
  unfold unfill. cbn. 
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.



Lemma w_is0_false : ltac2:(zQ "80!q2!o4!u3!jk0!lp3!hnb!nt2!on3>3len@1$2@1$0#k0>0@1$5@3$1@1$2@1$0#k0^1@2$7@1$0#k0Z@3$1$3@1$6^2$4").
Proof. intros len H. unfold w_is0. apply bv_eqb_neq. exact H. Qed.

Lemma in_arg1_sys_input' : ltac2:(zQ "70!q2!u3!o4!in8!pg5!hi3!pgf>2ms$3>2x8@1$1@1$0#k0@3$2@1$1@1$0#k0@2$6@3$5?4segs^2^1N1@2$4^2N1").
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input' : ltac2:(zQ "70!q2!u3!o4!in8!pg5!hi3!pgf>2ms$3>2x8@1$1@1$0#k0@3$2@1$1@1$0#k0@2$6@3$5?4segs^2^1N2@2$4^2N2").
Proof. reflexivity. Qed.

Lemma kgates : ltac2:(zQ "e0!q2!on3!jk0!o4!hrc!ph7!jk7!pi1!pia!mo7!ni3!nj5!pj1!nk8>2na$2>2nr$2@2$4@3$3$2@1$d@2$1@1$0#k0Z$6@2$4@3$3$2@1$9@2$1@1$0#k0@1$5^1$6@2$4@3$3$2@3$a@2$1@1$0#k0@1$7^2@2$1@1$0#k0@1$5^1@2$1@1$0#k0Z@1$8^2@2$4@3$3$2@3$b@2$1@1$0#k0@1$7^2@2$1@1$0#k0@1$5^1@2$1@1$0#k0Z^2@3$3$2@1$c@2$1@1$0#k0@1$5^1^1").
Proof. intros [|] [|]; vm_compute; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_kernel_spec : forall (na nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  (* LPS 727298f3: off the hint decline ([Mmap.place_declined_b]) *)
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0) nZ = false ->
  syscall_spec (sys_input segs ms x8) mo o <->
  mmap_err_out mo o
  \/ exists a, (linux_place h (kb_thp (m_kernel mo)) (ms_gpr ms 0) nZ (bv_unsigned a)
                /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true))
               /\ o = Ok (keff na a n) (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) [].
Proof.
  intros na nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hdecl.
  destruct (kgates na nr) as (Go & Ga & Gm & Gn & Gb).
  rewrite (syscall_spec_222 _ mo o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  destruct na.
  - rewrite (mmap_noaccess_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Hdecl).
    unfold grant_model, grant_vmmaps, keff.
    split; (intros [He | (a & Hc & ->)]; [left; exact He | right; exists a; split; [|reflexivity]]);
      [split; [exact Hc | discriminate] | exact (proj1 Hc)].
  - rewrite (mmap_rw_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Hdecl).
    unfold grant_model, grant_vmmaps, keff. cbn [negb].
    split; (intros [He | (a & Hc & ->)]; [left; exact He | right; exists a; split; [|reflexivity]]);
      [destruct Hc as (C1 & C2); split; [exact C1 | intros _; exact C2]
      |destruct Hc as (C1 & C2); split; [exact C1 | exact (C2 eq_refl)]].
Qed.

(* [comment removed for export] *)
Lemma mmap_kernel_grant_ok : forall (na nr : bool) ms mo x8 (g : word),
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0) nZ = false ->
  linux_place h (kb_thp (m_kernel mo)) (ms_gpr ms 0) nZ (bv_unsigned g) ->
  (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true) ->
  syscall_spec (sys_input segs ms x8) mo (Ok (keff na g n) (grant_model (Z_to_bv 64 (kflags nr)) g n na mo) []).
Proof.
  intros na nr ms mo x8 g Hno. cbv zeta. intros Hlen H2 H3 H5 Hdecl G1 G5.
  apply (proj2 (mmap_kernel_spec na nr ms mo x8 _ Hno Hlen H2 H3 H5 Hdecl)). right. exists g. split; [|reflexivity].
  split; assumption.
Qed.


(* The four admissibility facts of a placed address
   ([Checks.Placement.linux_place_admissible]); from spirv-tools bpA/HF/LazyNodes.v. *)
Lemma linux_place_conj4 : forall h thp hint nZ (a : word),
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  linux_place h thp hint nZ (bv_unsigned a) ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h thp hint nZ a H0 Hal Hp.
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_admissible
              h thp hint nZ (bv_unsigned a) H0 Hal Hp) as (A1 & A2 & A3 & A4).
  replace (Z_to_bv 64 (bv_unsigned a)) with a in A4
    by (symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_in : ltac2:(zQ "f0!q2!u3!lpb!jk0!o4!lp3!hif!m9!jk7!hrc!lnc!pqf!ol6!old!om3>4maps@1$6@2$7@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1x@1$1@1$0#k0>0@3$4$3@3$a^4^3^2$8>0@2$9@2$d@2$2@1$0#k0^4@2$2@1$0#k0^2@2$e@2$2@1$0#k0^2@2$c@2$2@1$0#k0^4@2$2@1$0#k0^3@3$4$3@2$b^3^6$5").
Proof.
  intros maps a n x Hf Hx. apply in_rangesb_false. intros lo sz Hin Hr.
  pose proof (State.region_free_In maps a n lo sz Hf Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov.
  destruct Hov as [D | D]; apply Z.ltb_ge in D; lia.
Qed.

(* [comment removed for export] *)
Lemma lzok_after_grant : ltac2:(zQ "ic4!q2!u3!m9!jk0!hif!o4!la!lr0!ko3!lq9!jk7!in8!lo9!hrc!jtd!hs2!ie!ks8!prd!pia!m0!ps4!ipb!iqf!lte!psa!lvc!mi5!lnc!pt9!mj0!pj1!pq0!osb!ou7!pu3!pv1!qg3!lhc!ln2!ovc!ol6!old!qh2&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0&@4$7@1$1@1$0#k0@1$1@1$0#k0^7^6&@1$6~0>2na$3>2nr$3>5flags@1$1@1$0#k0>1L~1>1S~1>2Zr~1>3msF$b>2mo$h0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@5$h1?4segs^7^6^5@2$f^4^3>0@3$5$3@1$hf^9^a=1h$h8@1$ha^5>0@3$5$3@3$hc@1$he^1^5^4$a>0>0@3$5$3^d$a@3$5$3@2$i4?4segs~2$a>0@3$5~1@2$h9^7^6@3$9~0~2~3=3mo'$h0@5$i0^e^8^7^h0^9>0@2$ia@2$i9@1$i3^1@2$ib@1$i5^d$hb@1$hd^5=2L'~1@3$c~0M3\2nr$3~1^h1@3$9~0@4$7@1$1@1$0#k0@1$1@1$0#k0^a^9~3~3^f=3Zr'~1@3$c~0M3\0$3~1@2$h2^h2@1$h3^h3@3$9~0@4$7@1$1@1$0#k0@1$1@1$0#k0^b^a~3~3^e=4msF'$b@1$h6@2$h7^e@3$i1^h4^c^b@2$d@5$h1?4segs^3^h1^2@2$f^1^5@2$d@3$5$b@3$8^3^h1^1@3$i2@3$8^h2^h1^f^dM3\0$3>0@1$1@1$0#k0@1$h4@1$1@1$0#8@2$h5^h5^h4@3$i7^d^c@1$e@3$8^h2^h1^f@3$i8^d^c@1$e@3$8^h2^h1^f@4$i6^h2^h1^f^1").
Proof.
  intros na nr flags L S Zr msF mo a n Hok Hfl. cbv zeta. intros Hfree Hrok Hli Hbud.
  destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. cbn in *.
  (* [comment removed for export] *)
  assert (Hnew : forall x, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
                 in_rangesb x L = false /\ in_rangesb x S = false /\ in_rangesb x Zr = false).
  { intros x Hx. pose proof (region_free_not_in _ a n x Hfree Hx) as HM.
    assert (HxL : in_rangesb x L = false).
    { destruct (in_rangesb x L) eqn:E; [|reflexivity]. rewrite (HLM x E) in HM. discriminate. }
    assert (HxZ : in_rangesb x Zr = false).
    { destruct (in_rangesb x Zr) eqn:E; [|reflexivity]. rewrite (HZL x E) in HxL. discriminate. }
    assert (HxS : in_rangesb x S = false).
    { destruct (in_rangesb x S) eqn:E; [|reflexivity]. rewrite (HSZ x E) in HxZ. discriminate. }
    auto. }
  assert (Hold : forall x, in_rangesb x L = true ->
                 ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z).
  { intros x HxL Hx. destruct (Hnew x Hx) as (E & _). rewrite E in HxL. discriminate. }
  (* [comment removed for export] *)
  assert (Elazy : m_vm_lazy (grant_model flags a n na mo) = (if nr then [(a, n)] else []) ++ L).
  { rewrite grant_model_lazy, Hli, Hfl. rewrite (li_lazy _ _ _ Hinv). reflexivity. }
  assert (Emat : m_vm_materialized (grant_model flags a n na mo) = m_vm_materialized mo)
    by apply grant_model_materialized.
  assert (Emaps : m_vmmaps (grant_model flags a n na mo) = grant_vmmaps (m_vmmaps mo) a n na)
    by apply grant_model_vmmaps.
  (* [comment removed for export] *)
  assert (Emem : ms_mem (apply_effect msF (keff na a n))
                 = if na then unfill a n (ms_mem msF) else zfill a n (ms_mem msF)).
  { destruct na; [apply apply_effect_mem_unmaps | apply apply_effect_mem_zeros]. }
  assert (Hmem_old : forall x, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
                     ms_mem (apply_effect msF (keff na a n)) x = ms_mem msF x).
  { intros x Hx. rewrite Emem. destruct na; [apply unfill_out | apply zfill_out]; lia. }
  split; [|split].
  - (* [comment removed for export] *) split; cbn.
    + destruct nr; [|exact HL]. cbn [app]. apply (proj2 (lazy_ranges_okb_cons segs (a, n) L)).
      split; [exact (Hrok eq_refl) | exact HL].
    + split.
      * exact Elazy.
      * rewrite Emat. exact (li_nodup _ _ _ Hinv).
      * rewrite Emat. exact (li_incl _ _ _ Hinv).
      * rewrite Emaps. cbn. exact Hbud.
    + unfold grant_model. destruct (with_mmap_backing_nonvm flags a n
          (with_vmmaps (grant_vmmaps (m_vmmaps mo) a n na) mo)) as (_ & _ & _ & Hp & _).
      unfold m_halted in *. rewrite Hp. cbn. exact Hh.
    + intros x Hx Hz. cbn [ms_mem advance_past_svc].
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge];
      [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)) as [Hlt2|Hge2]].
      * (* [comment removed for export] *) rewrite Hmem_old by lia.
        assert (HxL : hiddenb L S x = true).
        { destruct nr; [|exact Hx]. cbn [app] in Hx. rewrite hiddenb_cons_lazy in Hx.
          apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [|exact Hx].
          apply andb_true_iff in Hx. destruct Hx as [Hx _]. unfold zin_rangeb in Hx. cbn [fst snd] in Hx.
          apply andb_true_iff in Hx. destruct Hx as [Hx _]. apply Z.leb_le in Hx. lia. }
        apply HZ; [exact HxL|].
        destruct nr, na; cbn [andb negb app] in Hz; try exact Hz;
          rewrite in_rangesb_cons in Hz; apply orb_true_iff in Hz; destruct Hz as [Hz|Hz]; try exact Hz;
          unfold zin_rangeb in Hz; cbn [fst snd] in Hz; apply andb_true_iff in Hz; destruct Hz as [Hz _];
          apply Z.leb_le in Hz; lia.
      * (* [comment removed for export] *)
        destruct (Hnew x ltac:(lia)) as (ExL & ExS & ExZ).
        destruct nr, na; cbn [andb negb app] in Hz, Hx.
        -- rewrite ExZ in Hz. discriminate.
        -- rewrite Emem. unfold zfill, zmem.
           rewrite (proj2 (Z.leb_le _ _) Hge), (proj2 (Z.ltb_lt _ _) Hlt2). reflexivity.
        -- rewrite ExZ in Hz. discriminate.
        -- rewrite ExZ in Hz. discriminate.
      * (* [comment removed for export] *) rewrite Hmem_old by lia.
        assert (HxL : hiddenb L S x = true).
        { destruct nr; [|exact Hx]. cbn [app] in Hx. rewrite hiddenb_cons_lazy in Hx.
          apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [|exact Hx].
          apply andb_true_iff in Hx. destruct Hx as [Hx _]. unfold zin_rangeb in Hx. cbn [fst snd] in Hx.
          apply andb_true_iff in Hx. destruct Hx as [_ Hx]. apply Z.ltb_lt in Hx. lia. }
        apply HZ; [exact HxL|].
        destruct nr, na; cbn [andb negb app] in Hz; try exact Hz;
          rewrite in_rangesb_cons in Hz; apply orb_true_iff in Hz; destruct Hz as [Hz|Hz]; try exact Hz;
          unfold zin_rangeb in Hz; cbn [fst snd] in Hz; apply andb_true_iff in Hz; destruct Hz as [_ Hz];
          apply Z.ltb_lt in Hz; lia.
    + (* [comment removed for export] *) destruct nr, na; cbn [andb negb app]; try exact HSZ. apply rsub_cons_r. exact HSZ.
    + (* [comment removed for export] *) destruct nr, na; cbn [andb negb app]; try exact HZL.
      * apply rsub_cons_r. exact HZL.
      * apply rsub_cons_2. exact HZL.
    + (* [comment removed for export] *) rewrite Emaps. cbn. destruct nr; cbn [app].
      * apply rsub_cons_2. exact HLM.
      * apply rsub_cons_r. exact HLM.
  - (* [comment removed for export] *)
    rewrite (restrict_sysret L S). rewrite keff_ret. f_equal.
    apply functional_extensionality. intros x. rewrite Emem.
    unfold restrict_mem, restrict_mem_by.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge];
    [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)) as [Hlt2|Hge2]].
    + (* [comment removed for export] *)
      assert (Ehid : hiddenb ((if nr then [(a, n)] else []) ++ L) S x = hiddenb L S x).
      { destruct nr; [|reflexivity]. cbn [app]. rewrite hiddenb_cons_lazy.
        unfold zin_rangeb. cbn [fst snd].
        replace (bv_unsigned a <=? bv_unsigned x)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      rewrite Ehid. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
      destruct na, nr; cbn [orb]; unfold unfill, zfill, zmem;
        replace (bv_unsigned a <=? bv_unsigned x)%Z with false by (symmetry; apply Z.leb_gt; lia); cbn [andb];
        reflexivity.
    + (* [comment removed for export] *)
      destruct (Hnew x ltac:(lia)) as (ExL & ExS & ExZ).
      cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
      destruct na, nr; cbn [orb app]; unfold unfill, zfill, zmem;
        rewrite ?hiddenb_cons_lazy; unfold zin_rangeb; cbn [fst snd];
        rewrite (proj2 (Z.leb_le _ _) Hge), (proj2 (Z.ltb_lt _ _) Hlt2), ?ExS; cbn [andb orb negb];
        try reflexivity.
      all: unfold hiddenb; rewrite ExL; reflexivity.
    + (* [comment removed for export] *)
      assert (Ehid : hiddenb ((if nr then [(a, n)] else []) ++ L) S x = hiddenb L S x).
      { destruct nr; [|reflexivity]. cbn [app]. rewrite hiddenb_cons_lazy.
        unfold zin_rangeb. cbn [fst snd].
        replace (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity. }
      rewrite Ehid. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
      destruct na, nr; cbn [orb]; unfold unfill, zfill, zmem;
        replace (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z with false by (symmetry; apply Z.ltb_ge; lia);
        rewrite ?andb_false_r; reflexivity.
  - (* [comment removed for export] *) apply hid_frame_sysret. intros x Hx. apply Hmem_old.
    apply Hold. apply hiddenb_true_iff in Hx. tauto.
Qed.


Lemma ms_gpr_restrict : ltac2:(zQ "92!q2!u3!hif!m9!pg5!l4!o4!in8!ko3&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>2ms$7>1k$5@3$6@1$1@1$0#k0@2$4@3$8^4^3^2^1@2$4^2^1").
Proof. reflexivity. Qed.

Lemma grant_model_halted : ltac2:(zQ "80!q2!u3!hu2!jk0!m0!o4!ie!pq0>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2na$3>1m$6@3$5@1$4@1$1@1$0#k0@1$2@5$7^5^4^3^2^1@1$2^1").
Proof.
  intros flags a n na m. unfold grant_model.
  destruct (with_mmap_backing_nonvm flags a n (with_vmmaps (grant_vmmaps (m_vmmaps m) a n na) m)) as (_ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. destruct m; reflexivity.
Qed.

Lemma page_round_up_n_facts : ltac2:(zQ "d0!q2!o4!lof!hrc!om3!on3!u3!lpb!hnb!mh4!mi5!om9!qh9>3len@1$6@1$0#k0>0@1$8@3$1@1$6@1$0#k0^1@2$5@1$0#k0Z=2nZ$2@1$9@2$7@1$0#k0^2>0@2$4^1@2$c+2+k0@2$3@2$4Z^2@2$3@3$1$2@2$b^2$aZ@3$1$2@2$7@1$0#k0@2$5@1$0#k0^2^2").
Proof.
  intros len Hlen. cbv zeta. intros Hce.
  pose proof (PlacementSearch.page_round_up_Z_ge (bv_unsigned len)) as Hge. pose proof (word_unsigned_range len) as Hr.
  assert (bv_unsigned len <> 0%Z).
  { intros E. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
  split; [lia|]. split; [apply PlacementSearch.page_round_up_Z_aligned|].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
Theorem sreach_mmap_kernel_lazy : forall (na nr : bool) L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (* LPS 727298f3: off the hint decline ([Mmap.place_declined_b]); a NULL hint
     proves it by [RelSpec.place_declined_b_null] *)
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0) nZ = false ->
  entries_nowrap (vm_maps h) ->
  (na = false -> nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (exists g : word, (bv_unsigned g mod page_size = 0)%Z /\ (0 < bv_unsigned g)%Z
                    /\ (bv_unsigned g + nZ <= alloc_top h)%Z
                    /\ region_free (vm_reserved h ++ vm_maps h) g n = true
                    (* at the revision Linux places only in [page_size, mmap_top)
                       or [task_unmapped_base, alloc_top) ([Mmap.topdown_search]) *)
                    /\ ((bv_unsigned g + nZ <= mmap_top h)%Z \/ (task_unmapped_base <= bv_unsigned g)%Z)) ->
  (nr = true -> forall a : word, region_free (vm_reserved h) a n = true ->
                (bv_unsigned a + nZ <= alloc_top h)%Z -> lazy_range_okb segs (a, n) = true) ->
  (forall (a : word) (msF' : machine_state),
     (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z ->
     region_free (vm_reserved h ++ vm_maps h) a n = true ->
     let mo' := grant_model (Z_to_bv 64 (kflags nr)) a n na mo in
     lzok segs ((if nr then [(a, n)] else []) ++ L) S ((if nr && negb na then [(a, n)] else []) ++ Zr)
          (mkCfg msF' mo') ->
     restrict ((if nr then [(a, n)] else []) ++ L) S msF'
       = sysret ms a (if na || nr then unfill a n (ms_mem ms) else zfill a n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ))%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros na nr L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hdecl Hnw Hbud (g & Hgal & Hgpos & Hgce & Hgfree & Hgwin) Hrok Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (alloc_top_lt (m_vmmaps mo)) as Htop.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen ltac:(pose proof (word_unsigned_range g); unfold two_pow_64 in Htop; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (lzok_backing_used_le segs L S Zr _ Hok) as Hbk. cbn [cfg_model] in Hbk.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).

  assert (Hbk' : na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true).
  { intros ->. unfold mmap_noreserve_backed_ok. destruct (kgates false nr) as (_ & _ & _ & _ & ->).
    destruct nr; [reflexivity|]. specialize (Hbud eq_refl eq_refl). apply Z.leb_le. lia. }

  (* the address Linux gives: it exists because the gap [g] lies in one of
     the two windows ([Checks.Placement.linux_place_exists]) *)
  pose (thp := kb_thp (m_kernel mo)). pose (hint := ms_gpr msF 0).
  assert (Hex : exists a0, linux_place (m_vmmaps mo) thp hint nZ a0).
  { apply LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_exists; [lia | exact HnZal |].
    exists (bv_unsigned g). unfold gap_fits.
    replace (Z_to_bv 64 (bv_unsigned g)) with g
      by (symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    destruct Hgwin as [Hw | Hw]; [left | right]; (repeat split; [exact Hgal | | | ]);
      first [exact Hgfree | lia | unfold page_size in *; Z.div_mod_to_equations; lia]. }
  destruct Hex as (a0 & Ha0).
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_admissible (m_vmmaps mo) thp hint nZ a0 ltac:(lia) HnZal Ha0)
    as (_ & Ha0pos & Ha0ce & _).
  set (g0 := Z_to_bv 64 a0).
  assert (Hg0 : bv_unsigned g0 = a0) by (unfold g0; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus, two_pow_64 in *; lia).
  rewrite <- Hg0 in Ha0.
  pose (I := {a : word | linux_place (m_vmmaps mo) thp hint nZ (bv_unsigned a)
                         /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)}).
  pose (effs := fun i : I => keff na (proj1_sig i) n).
  pose (ms' := fun i : I => grant_model (Z_to_bv 64 (kflags nr)) (proj1_sig i) n na mo).
  assert (Hg : linux_place (m_vmmaps mo) thp hint nZ (bv_unsigned g0)
               /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)).
  { split; assumption. }
  assert (Hplace : forall a, (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
                   (bv_unsigned a + nZ <= alloc_top (m_vmmaps mo))%Z ->
                   region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
                   refusal_b (sys_input segs msF x8) mo a = false).
  { intros a A1 A2 A3 A4. apply (place_not_refusal (sys_input segs msF x8) mo a nZ Hno'); [|lia].
    apply place_ok_intro; assumption. }
  assert (Hnode : node_ok segs (mkCfg msF mo) I (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect msF (effs i))) (ms' i))).
  { apply (node_family_noacc_cfg msF mo x8 I effs ms' (fun _ => []) _ (lzok_halted Hok) Hsvc
             (fun o => mmap_kernel_spec na nr msF mo x8 o Hno Hlen H2 H3 H5 Hdecl)).
    - intros [a Ha]. right. exists a. split; [exact Ha | reflexivity].
    - intros [a (Ap & A5)]. apply spurious_refusal_not_refusal. unfold effs. cbn [proj1_sig].
      rewrite keff_ret. destruct (linux_place_conj4 _ _ _ _ a HnZpos HnZal Ap) as (A1 & A2 & A3 & A4).
      apply Hplace; assumption.
    - intros eff m' ev [He | (a & Ha & E)] Hns.
      + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
        apply (alloc_refusal_spurious _ mo _ (keff na g0 n) (grant_model (Z_to_bv 64 (kflags nr)) g0 n na mo) []).
        * apply family_off_mmap_true. exact Hno'.
        * cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
        * apply (mmap_kernel_grant_ok na nr msF mo x8 g0 Hno Hlen H2 H3 H5 Hdecl Ha0 Hbk').
        * rewrite keff_ret. destruct (linux_place_conj4 _ _ _ _ g0 HnZpos HnZal Ha0) as (A1 & A2 & A3 & A4).
          apply Hplace; assumption.
      + apply Ok_inj in E as (-> & -> & ->). exists (exist _ a Ha). auto.
    - intros eff m' ev [He | (a & _ & E)].
      + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
      + apply Ok_inj in E as (-> & -> & ->). rewrite grant_model_halted. exact (lzok_halted Hok).
    - intros [He | (a & _ & E)]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E].
    - intros i. apply keff_accesses. }
  apply (sreach_node segs _ I _ (exist _ g0 Hg) _ Hnode ltac:(RomBase.rob_auto)).
  intros [a (Hap & Ha5)]. cbn [proj1_sig].
  destruct (linux_place_conj4 _ _ _ _ a HnZpos HnZal Hap) as (Hal & Hpos & Hce & Hfree).

  assert (Hli' : lazy_interior a n = [(a, n)]).
  { apply lazy_interior_aligned; [exact Hal | rewrite Hun; exact HnZal | rewrite Hun; exact HnZpos]. }
  assert (He : entry_nowrap (a, n)).
  { unfold entry_nowrap, hi. cbn [fst snd]. rewrite Hun. unfold two_pow_64 in Htop. lia. }
  assert (Heag : (eager_used (grant_model (Z_to_bv 64 (kflags nr)) a n na mo)
                  <= eager_used mo + (if na || nr then 0 else nZ))%Z).
  { destruct (kgates na nr) as (_ & _ & _ & _ & Gb).
    destruct na; [|destruct nr]; cbn [orb].
    - pose proof (eager_used_grant_covered_le (Z_to_bv 64 (kflags nr)) a n true mo Hnw He (or_introl eq_refl)). lia.
    - pose proof (eager_used_grant_covered_le (Z_to_bv 64 (kflags true)) a n false mo Hnw He (or_intror (conj Gb Hli'))). lia.
    - rewrite <- Hun. apply (eager_used_grant_rw_le (Z_to_bv 64 (kflags false)) a n mo Gb Hnw He). }
  assert (Hbud' : (eager_used (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) + pages_total S * page_size
                   <= vm_limit (m_vmmaps mo))%Z).
  { destruct na; [|destruct nr]; cbn [orb] in Heag; [lia | lia |]. specialize (Hbud eq_refl eq_refl). lia. }
  destruct (lzok_after_grant na nr (Z_to_bv 64 (kflags nr)) L S Zr msF mo a n Hok (proj2 (proj2 (proj2 (proj2 (kgates na nr)))))
              (region_free_app_r _ _ _ _ Hfree)
              (fun Hnr => Hrok Hnr a (region_free_app_l _ _ _ _ Hfree) Hce) Hli' Hbud')
    as (Hok' & Hvis & Hhs).
  apply (Hk a _ Hal Hpos Hce Hfree Hok' Hvis Hhs Heag).
Qed.



(* [comment removed for export] *)

Lemma fgates : ltac2:(zQ "h10!q2!on3!jk0!o4!hrc!qj2!pi1!lp3!jk7!pia!mo7!ms3!mtd!ni3!nj5!pj1!nk8>2na$2>2nr$2@2$4@3$3$2@1$h0@2$1@1$0#k0Z$8@2$4@3$3$2@1$a@2$1@1$0#k0@1$5^1$8@2$4@3$3$2@3$d@2$1@1$0#k0@1$6^2@2$1@1$0#k0@1$5^1@2$1@1$0#k0Z$7@2$4@3$3$2@3$e@2$1@1$0#k0@1$6^2@2$1@1$0#k0@1$5^1@2$1@1$0#k0Z$7@2$4@3$3$2@3$b@2$1@1$0#k0@1$6^2@2$1@1$0#k0@1$5^1@2$1@1$0#k0Z^2@2$4@3$3$2@3$c@2$1@1$0#k0@1$6^2@2$1@1$0#k0@1$5^1@2$1@1$0#k0Z@1$9^2@3$3$2@1$f@2$1@1$0#k0@1$5^1^1").
Proof. intros [|] [|]; vm_compute; repeat split; reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma map_contains_In : ltac2:(zQ "h01!q2!u3!m9!lpb!hrc!old!jk0!hif!jk7!o4!iif!mg6!qjc!qk2!oj8!ol6&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$7~0>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$9$6@3$b^3^2^1$8@2$a~0\1e~0@2$4@3$e~0^1^5@2$4@2$5@1$d^1@2$3@1$0#k0^4@2$5@2$f@2$3@1$0#k0^4@2$3@1$0#k0^3@1$c^1").
Proof.
  intros maps addr n H. unfold map_contains in H. apply existsb_exists in H.
  destruct H as (e & Hin & Hc). exists e. split; [exact Hin|].
  apply andb_true_iff in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold lo, hi. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_ranges_okb_nowrap : ltac2:(zQ "90!q2!u3!jk0!hif!m9!jk7!o4!qi0!qk8>1L@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>0@3$6$2@2$8?4segs^1$5@1$7^2").
Proof.
  intros L H e He. pose proof (lazy_ranges_okb_In segs L e H He) as Hr.
  unfold lazy_range_okb, range_nowrapb in Hr. destruct e as [b s]. cbn [fst snd] in Hr.
  apply andb_true_iff in Hr. destruct Hr as [Hnw _]. apply Z.leb_le in Hnw.
  unfold entry_nowrap, hi. cbn [fst snd]. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma addr_not_refusal_mmap : ltac2:(zQ "e0!q2!o4!lpb!jk0!lp3!lof!qlb!ie!lt0!lu6!qm7!lvc!old!u3>1i$8>1m$7>1a@1$d@1$0#k0>0@3$1$5@2$2@1$0#k0@1$a^3+te>0@2$c@2$2@1$0#k0^2@1$9@1$b^3@3$1$3@3$6^5^4^3$4").
Proof.
  intros i m a Hno Ha. rewrite (refusal_b_mmap i m a Hno). apply bv_eqb_neq. intros E. subst a.
  rewrite (errno_ret_unsigned ENOMEM) in Ha by (unfold ENOMEM; lia).
  pose proof (word_unsigned_range (vm_init_sp (m_vmmaps m))).
  unfold ENOMEM, alloc_top, stack_max_size, two_pow_64 in *. lia.
Qed.

Lemma mmap_fixed_commit_spec : ltac2:(zQ "j54!q2!u3!la!o4!m9!on3!lof!pg5!u8!lpb!jk0!jk7!jhe!qj2!lq9!hif!l4!lr0!hrc!lr7!hqf!lrc!hn4!ls5!lp3!iif!ji9!hnb!in8!hi3!hm4!ie!lte!lu6!lv1!lvc!mg6!mh4!mi5!lnc!mj0!mj9!mp6!mq5!mv0!nmc!qn1!oh5!oj8!ol6!old!om3!om9&@2$4@1$1@1$0#k0@1$f@1$1@1$0#8&@1$2~0&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$2~2>2nr$a>2ms$hc>2mo$hf>2x8@1$1@1$0#k0>1o@1$c$8>0@3$3$6@2$9@1$0#k0^2+te=4addr@1$1@1$0#k0@2$7^5N0=3len@1$1@1$0#k0@2$7^6N1=2nZ$6@1$i5@2$9@1$0#k0^1=1n@1$1@1$0#k0@2$5@1$0#k0^1=1h$i0@1$i3^8>0@1$hb@3$3@1$1@1$0#k0^4@2$5@1$0#k0Z>0@3$3@1$1@1$0#k0@2$7^bN2@2$5@1$0#k0+3>0@3$3@1$1@1$0#k0@2$7^cN3@2$5@1$0#k0@1$d^d>0@3$3@1$1@1$0#k0@2$7^dN5@2$5@1$0#k0Z>0@2$j2@2$j1@2$9@1$0#k0^9^7@1$i1^5>0@3$3$6@2$j4@2$9@1$0#k0^a$i6Z>0@2$j3Z@2$9@1$0#k0^b>0@3$3$a@3$i7@1$i9^8^c^9$b>0@3$3$a@3$i4@1$i8^9^d^a$b@2$ha@3$he@3$hd?4segs^h3^h1^h2^h0@2$h3@2$if^h2^h0@2$h3@2$h2@3$3$a@4$ic@2$5@1$0#k0@1$d^h4^h2^e^b$b@3$3@1$c$8^h0@4$h4$8@6$h7^e~1@3$e~2@4$h1@1$1@1$0#k0@1$1@1$0#k0^e^b~3~3@1$2$h5@1$2@2$4@1$1@1$0#k0$h0@5$ie@2$5@1$0#k0@1$d^h4^e^b$h8^h2@1$2$h6@2$h9$6\1e$6@2$h2@3$j0$6^1$ia@3$3@1$c$8^h1@4$h4$8@6$h7@1$i2^1~1~3@3$e~2@4$h1@1$1@1$0#k0@1$1@1$0#k0^f^c~3@1$2$h5@1$2@2$4@1$1@1$0#k0$h0@4$id^f^c@3$ib^b^f^c^h3@1$2$h6").
Proof.
  intros nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hce Hal Hpos Hrf Hmc.
  destruct (fgates false nr) as (Go & Ga & Gm & Gn & Gfn & Gfr & Gb). cbn [negb kprot] in *.
  rewrite (syscall_spec_222 _ mo o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  rewrite (mmap_fixed_rw_commit_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Gfn Gfr Hce Hal Hpos Hrf Hmc).
  rewrite mmap_fixed_rw_commit_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hiddenb_maps_subtract : ltac2:(zQ "f2!q2!u3!hif!m9!lof!ov1!old!prd!jk0!pia!o4!qo1!qi0!qp0!lpb&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1L~1>1S~1>1l$4>1h$4>1x@1$1@1$0#k0>0@1$c^5>0@2$6Z^4>0@2$6^5^4@3$a$8@3$5@3$b^8^6^5^7^4@2$7@3$5^8^7^4@1$9@3$d^6^5@2$e@1$0#k0^4").
Proof.
  intros L S l h x HL Hl Hlh. unfold hiddenb. rewrite !in_rangesb_zcovb, (zcovb_maps_subtract L l h _ HL Hl Hlh).
  destruct (zcovb L (bv_unsigned x)), (zinb l h (bv_unsigned x)), (zcovb S (bv_unsigned x)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lzok_after_commit : ltac2:(zQ "j73!q2!u3!m9!jk0!o4!la!lpb!hif!lr0!jk7!hrc!ko3!old!lq9!lp3!in8!pqf!on3!m0!lof!jtd!hs2!ie!qi0!qj2!ks8!ol6!om3!kd!prd!lo9!l4!ipb!iqf!lrc!lte!psa!lvc!qo1!ls5!mi5!pt9!mj0!qp8!mv0!qn1!ou7!pu3!pv1!qg3!qq5!lhc!ovc!qh2!qh9&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$7~0&@1$5~0>2nr$3>1L~1>1S~1>2Zr~1>3msF$f>2mo$h6>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>0@5$h9?4segs^7^6^5@2$h5^4^3=1h$i3@1$i5^4=1l$h3@2$6@1$0#k0^4=2hh$h3@2$ha@2$6@1$0#k0^5@2$6@1$0#k0^4>0@2$c^1@2$j6+2+k0>0@1$h7@1$ia^4>0@1$h7@1$ib^5>0@3$4~1@2$i4^9^8@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^9^8~2>0>0@3$4$3^h0$e>1x@1$1@1$0#k0>0@2$a@2$c^8@2$6@1$0#k0^1@2$hb@2$6@1$0#k0^1^7@3$4$3@2$h0^2^h0$e>0>0@3$4$3^h1$9>1x@1$1@1$0#k0>0@2$a@2$c^9@2$6@1$0#k0^1@2$hb@2$6@1$0#k0^1^8@3$4$3@2$h0^2^h1$9>0>0@3$4$3^h2$9@3$4$3@2$j0?4segs@4$8@1$1@1$0#k0@1$1@1$0#k0^d^c$9=3mo'$h6@5$id@2$h1@1$0#k0@1$h8^h3^d^c$e^e>0@2$c@2$ha@1$if^1@2$j5@1$j1^h2$i8@1$i9^b=2L'~1@3$he~0M3\2nr$3~1^h5@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^f^e~2~2@3$i6^h4^b^a=4msF'$f@1$i0@2$i1^h2@6$i7^h0@1$5@2$2@1$1@1$0#k0@1$7@1$1@1$0#8@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^h0^f~2~2@1$5$i2@1$5@2$2@1$1@1$0#k0$hf@2$a@5$h9?4segs^2^h5^h4@2$h5^1^4@2$a@3$4$f@3$b^2^h5^1@3$ie@3$b^h6^h5^h3^h1M3\2nr$3>0@1$1@1$0#k0@1$h2@1$1@1$0#8^h7\1x@1$1@1$0#k0M3\0$3@1$h2@1$1@1$0#8@2$hd@2$j2@2$6@1$0#k0^1@4$8@1$1@1$0#k0@1$1@1$0#k0^h2^h1@2$h0^1^h6@2$hc@1$1@1$0#8@2$h1@1$0#8Z@2$h4@3$b^h7^h6^h4^1@3$j4^h1^h0@1$h4@3$b^h6^h5^h3@2$a@4$j3^2^h5^h3^1@3$4$3@4$ic@2$h1@1$0#k0@1$h8^h7^h2^h1^h0$9").
Proof.
  intros nr L S Zr msF mo addr n Hok. cbv zeta. intros Hnw HX HNA Hli HZfree HZin Hrok Hbud.
  destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. cbn in *.
  pose proof (lazy_ranges_okb_nowrap L HL) as HLnw.
  pose proof (word_unsigned_range addr) as Har. pose proof (word_unsigned_range n) as Hnr.
  destruct (fgates false nr) as (_ & _ & _ & _ & _ & _ & Gb).
  set (l := bv_unsigned addr) in *. set (hh := bv_unsigned addr + bv_unsigned n) in *.
  assert (Hlh : l <= hh) by (unfold l, hh; lia). assert (Hl0 : 0 <= l) by (unfold l; lia).
  (* [comment removed for export] *)
  assert (Elazy : m_vm_lazy (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                  = (if nr then [(addr, n)] else []) ++ maps_subtract L l hh).
  { rewrite commit_model_lazy, Gb, Hli, (li_lazy _ _ _ Hinv). destruct nr; reflexivity. }
  assert (Emat : m_vm_materialized (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                 = List.filter (page_outside_range l hh) (m_vm_materialized mo))
    by apply commit_model_materialized.
  assert (Emaps : m_vmmaps (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                  = commit_vmmaps (m_vmmaps mo) addr n false) by apply commit_model_vmmaps.
  assert (Emem : ms_mem (apply_effect msF (mkEffect addr [] [(addr, n)])) = zfill addr n (ms_mem msF))
    by apply apply_effect_mem_zeros.
  (* [comment removed for export] *)
  assert (Hhid' : forall x, hiddenb ((if nr then [(addr, n)] else []) ++ maps_subtract L l hh) S x
                            = if zinb l hh (bv_unsigned x) then (if nr then negb (in_rangesb x S) else false)
                              else hiddenb L S x).
  { intros x. destruct nr; cbn [app].
    - rewrite hiddenb_cons_lazy, (hiddenb_maps_subtract L S l hh x HLnw Hl0 Hlh).
      replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
      destruct (zinb l hh (bv_unsigned x)), (in_rangesb x S), (hiddenb L S x); reflexivity.
    - rewrite (hiddenb_maps_subtract L S l hh x HLnw Hl0 Hlh).
      destruct (zinb l hh (bv_unsigned x)), (hiddenb L S x); reflexivity. }
  assert (HRL : nr = true -> forall x : word, l <= bv_unsigned x < hh -> in_rangesb x L = true).
  { intros Hn x Hx. apply HZL. apply (HZin Hn x Hx). }
  (* [comment removed for export] *)
  assert (Hlen : (Z.of_nat (length (List.filter (page_outside_range l hh) (m_vm_materialized mo)))
                  <= pages_total S)%Z).
  { rewrite <- all_pages_length. apply Nat2Z.inj_le.
    apply (NoDup_incl_length (l:=List.filter _ _) (l':=all_pages S)).
    - apply NoDup_filter. exact (li_nodup _ _ _ Hinv).
    - intros p Hp. apply filter_In in Hp. apply (li_incl _ _ _ Hinv). tauto. }
  assert (Elim : vm_limit (commit_vmmaps (m_vmmaps mo) addr n false) = vm_limit (m_vmmaps mo)) by reflexivity.
  assert (Hbok : mmap_fixed_rw_budget_ok (Z_to_bv 64 (fflags nr)) mo addr n = true).
  { unfold mmap_fixed_rw_budget_ok. rewrite mmap_fixed_rw_commit_model.
    unfold vm_backing_within_limit. apply Z.leb_le. rewrite vm_backing_used_split, Emat, Emaps, Elim.
    unfold page_size in *. nia. }
  (* [comment removed for export] *)
  assert (Hout : forall x, zinb l hh (bv_unsigned x) = false ->
                 ms_mem (apply_effect msF (mkEffect addr [] [(addr, n)])) x = ms_mem msF x).
  { intros x Hx. rewrite Emem. apply zfill_out. apply zinb_false in Hx. unfold l, hh in Hx. lia. }
  assert (Hin : forall x, zinb l hh (bv_unsigned x) = true ->
                ms_mem (apply_effect msF (mkEffect addr [] [(addr, n)])) x = Some (Z_to_bv 8 0)).
  { intros x Hx. rewrite Emem. apply zinb_true in Hx. unfold zfill, zmem. unfold l, hh in Hx.
    rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  split; [|split; [|split; [|exact Hbok]]].
  - (* [comment removed for export] *) split; cbn.
    + destruct nr; cbn [app].
      * apply (proj2 (lazy_ranges_okb_cons segs (addr, n) _)). split; [exact (Hrok eq_refl)|].
        apply lazy_ranges_okb_maps_subtract; [exact Hnw | exact HL].
      * apply lazy_ranges_okb_maps_subtract; [exact Hnw | exact HL].
    + split.
      * exact Elazy.
      * rewrite Emat. apply NoDup_filter. exact (li_nodup _ _ _ Hinv).
      * rewrite Emat. intros p Hp. apply filter_In in Hp. apply (li_incl _ _ _ Hinv). tauto.
      * rewrite Emaps, Elim. exact Hbud.
    + destruct (commit_model_nonvm (Z_to_bv 64 (fflags nr)) addr n false mo) as (_ & _ & _ & Hp & _).
      unfold m_halted in *. rewrite Hp. exact Hh.
    + intros x Hx Hz. cbn [ms_mem advance_past_svc]. rewrite Hhid' in Hx.
      destruct (zinb l hh (bv_unsigned x)) eqn:Ein.
      * apply Hin. exact Ein.
      * rewrite (Hout x Ein). apply HZ; assumption.
    + exact HSZ.
    + (* [comment removed for export] *) intros x Hx. rewrite in_rangesb_zcovb in *.
      destruct nr; cbn [app]; rewrite ?zcovb_cons, (zcovb_maps_subtract L l hh _ HLnw Hl0 Hlh).
      * replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
        pose proof (HZL x) as HxL. rewrite !in_rangesb_zcovb in HxL. rewrite (HxL Hx).
        destruct (zinb l hh (bv_unsigned x)); reflexivity.
      * pose proof (HZL x) as HxL. rewrite !in_rangesb_zcovb in HxL. rewrite (HxL Hx). cbn [andb].
        destruct (zinb l hh (bv_unsigned x)) eqn:Ein; [|reflexivity].
        apply zinb_true in Ein. pose proof (HZfree eq_refl x Ein) as C. rewrite in_rangesb_zcovb in C.
        rewrite C in Hx. discriminate.
    + (* [comment removed for export] *) rewrite Emaps. cbn. intros x Hx. rewrite in_rangesb_zcovb in Hx |- *.
      destruct nr; cbn [app] in Hx; rewrite ?zcovb_cons, (zcovb_maps_subtract L l hh _ HLnw Hl0 Hlh) in Hx.
      * destruct (zin_rangeb (bv_unsigned x) (addr, n)) eqn:Ein.
        -- pose proof (HRL eq_refl x ltac:(apply zinb_true; exact Ein)) as HxL.
           rewrite <- in_rangesb_zcovb. apply HLM. exact HxL.
        -- cbn in Hx. apply andb_true_iff in Hx. rewrite <- in_rangesb_zcovb. apply HLM.
           rewrite in_rangesb_zcovb. tauto.
      * apply andb_true_iff in Hx. rewrite <- in_rangesb_zcovb. apply HLM. rewrite in_rangesb_zcovb. tauto.
  - (* [comment removed for export] *)
    rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    apply functional_extensionality. intros x.
    unfold restrict_mem, restrict_mem_by. rewrite Hhid'.
    cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
    destruct (zinb l hh (bv_unsigned x)) eqn:Ein.
    + rewrite (Hin x Ein). destruct nr.
      * replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
        rewrite Ein. cbn [andb]. destruct (in_rangesb x S) eqn:ES; cbn [negb]; [reflexivity|].
        replace (hiddenb L S x) with true; [reflexivity|]. symmetry. apply hiddenb_true_iff.
        split; [apply (HRL eq_refl); apply zinb_true; exact Ein | exact ES].
      * unfold zfill, zmem. apply zinb_true in Ein. unfold l, hh in Ein.
        rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb]. reflexivity.
    + rewrite (Hout x Ein). destruct nr.
      * replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
        rewrite Ein. cbn [andb]. reflexivity.
      * unfold zfill, zmem. apply zinb_false in Ein. unfold l, hh in Ein.
        destruct ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + bv_unsigned n)) eqn:E.
        -- apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
        -- destruct (hiddenb L S x); reflexivity.
  - (* [comment removed for export] *)
    intros x Hx. cbn [ms_mem advance_past_svc]. rewrite Hhid' in Hx.
    destruct (zinb l hh (bv_unsigned x)) eqn:Ein.
    + destruct nr; [|discriminate Hx]. rewrite (Hin x Ein). symmetry. apply HZ.
      * apply hiddenb_true_iff. split; [apply (HRL eq_refl); apply zinb_true; exact Ein|].
        destruct (in_rangesb x S); [discriminate Hx | reflexivity].
      * apply (HZin eq_refl). apply zinb_true. exact Ein.
    + apply Hout. exact Ein.
Qed.


(* [comment removed for export] *)
Theorem sreach_mmap_fixed_commit_lazy : ltac2:(zQ "jb3!q2!u3!o4!jk0!lpb!m9!on3!ol6!jk7!pg5!hif!in8!old!lp3!lof!hs2!m0!lr0!mj0!pu3!pqf!om3!kd!la!hrc!jtd!ie!mi5!qi0!qj2!ko3!ks8!lg9!prd!lo9!lq9!hnb!io9!lh3!lte!lu6!lvc!mg6!qo1!mh4!lnc!pt9!qp8!mj9!qn1!qr3!ou7!pv1!qg3!qq5!lhc!ovc!om9!qh2&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$a~0&@1$h7~0>2nr$3>1L~1>1S~1>2Zr~1>3msF$b>2ms$b>2mo$ha>2x8@1$1@1$0#k0>1Q>0$i6P>0@5$hf?4segs^8^7^6@2$f^5^3>0@3$2$b@3$he^9^8^6^5>0@3$2@1$h0@1$1@1$0#k0@1$i5^6@2$h6@1$1@1$0#k0^4>0@3$2$e@2$4@1$0#k0^5+te=4addr@1$1@1$0#k0@2$9^8N0=3len@1$1@1$0#k0@2$9^9N1=2nZ$e@1$ic@2$4@1$0#k0^1=1n@1$1@1$0#k0@2$6@1$0#k0^1=1h$i7@1$i9^b>0@1$i4@3$2@1$1@1$0#k0^4@2$6@1$0#k0Z>0@3$2@1$1@1$0#k0@2$9^eN2@2$6@1$0#k0+3>0@3$2@1$1@1$0#k0@2$9^fN3@2$6@1$0#k0@1$hd^h4>0@3$2@1$1@1$0#k0@2$9^h0N4@2$6@1$0#k0-1>0@3$2@1$1@1$0#k0@2$9^h1N5@2$6@1$0#k0Z>0@2$c@2$7@2$4@1$0#k0^a^8@1$i8^6>0@3$2$e@2$j9@2$4@1$0#k0^b$hbZ>0@2$h5Z@2$4@1$0#k0^c>0@3$2$3@3$id@1$j0^9^d^a$8>0@3$2$3@3$ia@1$h2^a^e^b$8>0@1$hc@1$h2^b>0@1$hc@1$if^c>0@1$j2@1$h2^d>0>0@3$2$3^hf$d>1x@1$1@1$0#k0>0@2$h8@2$c@2$4@1$0#k0^h4@2$4@1$0#k0^1@2$h5@2$4@1$0#k0^1@2$7@2$4@1$0#k0^h4^h2@3$2$3@2$h4^2^hf$d>0>0@3$2$3^i0$8>1x@1$1@1$0#k0>0@2$h8@2$c@2$4@1$0#k0^h5@2$4@1$0#k0^1@2$h5@2$4@1$0#k0^1@2$7@2$4@1$0#k0^h5^h3@3$2$3@2$h4^2^i0$8>0>0@3$2$3^i1$8@3$2$3@2$j4?4segs@4$h1@1$1@1$0#k0@1$1@1$0#k0^h5^h2$8>0>0@3$2$3^i2$d@2$c@2$7@2$7@1$h3^hd@2$ja@1$j5^i1$hb^h4@1$ie^h2>0>4msF'$b=3mo'$ha@5$j1@2$6@1$0#k0@1$hd^i4^h7^h4$d^he=2L'~1@3$i2~0M3\2nr$3~1^i5@3$i3~0@4$h1@1$1@1$0#k0@1$1@1$0#k0^h8^h5~2~2@3$ib^i4@2$4@1$0#k0^h8@2$7@2$4@1$0#k0^h8^h6>0@5$hf?4segs^1^i4^i3@2$f^3^2>0@3$2$b@3$he^2^i5^4@3$j3^i2^haM3\2nr$3>0@1$1@1$0#k0@1$h0@1$1@1$0#8^i7\1x@1$1@1$0#k0M3\0$3@1$h0@1$1@1$0#8@2$i1@2$j6@2$4@1$0#k0^1@4$h1@1$1@1$0#k0@1$1@1$0#k0^hb^h8@2$h4^1^i6@2$h6@1$1@1$0#8@2$6@1$0#8Z@2$h9^i3^1@3$j8^ha^h7@1$h9^i2>0@4$j7^3^i6^i4^5>0@2$c@1$h3^5@2$7@1$h3^i3M3\2nr$3$e^i9Z^ha@4$i0?4segs?2SC^i2@2$f^7^6@4$i0?4segs?2SC^hc@2$f^i0^he").
Proof.
  intros nr L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hce Hal Hpos Hrf Hmc HX HNA Hno_ov HZfree HZin Hrok Hbud Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (alloc_top_lt (m_vmmaps mo)) as Htop.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen ltac:(pose proof (word_unsigned_range addr); unfold two_pow_64 in Htop; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  pose proof (lazy_ranges_okb_nowrap L (lzok_ranges Hok)) as HLnw.
  destruct (fgates false nr) as (_ & _ & _ & _ & _ & _ & Gb).
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hli' : lazy_interior addr n = [(addr, n)]).
  { apply lazy_interior_aligned; [exact Hal | rewrite Hun; exact HnZal | rewrite Hun; exact HnZpos]. }
  assert (Hhh : bv_unsigned addr + bv_unsigned n <= 2 ^ 64).
  { rewrite Hun. unfold two_pow_64 in Htop. lia. }
  assert (HLm : m_vm_lazy mo = L) by exact (li_lazy _ _ _ (lzok_inv Hok)).
  assert (Heag : (eager_used (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                  <= eager_used mo + (if nr then 0 else nZ))%Z).
  { destruct nr.
    - pose proof (eager_used_commit_covered_le (Z_to_bv 64 (fflags true)) addr n false mo HX HNA
                    ltac:(rewrite HLm; exact HLnw) (or_intror (conj Gb Hli'))). lia.
    - rewrite <- Hun. apply (eager_used_commit_rw_le (Z_to_bv 64 (fflags false)) addr n mo HX HNA
                    ltac:(rewrite HLm; exact HLnw) Hno_ov).
      destruct (map_contains_In _ _ _ Hmc) as (e0 & He0 & He1 & He2). exists e0.
      unfold lo, hi in *. cbn [fst snd]. auto. }
  assert (Hbud' : (eager_used (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo) + pages_total S * page_size
                   <= vm_limit (m_vmmaps mo))%Z).
  { destruct nr.
    - replace (if true then 0 else nZ) with 0 in Heag by reflexivity. lia.
    - replace (if false then 0 else nZ) with nZ in Heag by reflexivity. specialize (Hbud eq_refl). lia. }
  rewrite <- Hun in HZfree, HZin.
  destruct (lzok_after_commit nr L S Zr msF mo addr n Hok Hhh HX HNA Hli' HZfree HZin Hrok Hbud')
    as (Hok' & Hvis & Hhs & Hbok).
  assert (Haddr : refusal_b (sys_input segs msF x8) mo addr = false).
  { apply (addr_not_refusal_mmap _ mo addr Hno'). lia. }
  pose proof (mmap_fixed_commit_spec nr msF mo x8) as Hspec. cbv zeta in Hspec.
  specialize (fun o => Hspec o Hno Hlen H2 H3 H5 Hce Hal Hpos Hrf Hmc) as Hsp. clear Hspec.
  fold nZ in Hsp. fold n in Hsp. fold addr in Hsp.
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF (mkEffect addr [] [(addr, n)])))
                                    (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo))).
  { apply (node_family_noacc_cfg msF mo x8 unit (fun _ => mkEffect addr [] [(addr, n)])
             (fun _ => commit_model (Z_to_bv 64 (fflags nr)) addr n false mo) (fun _ => []) _ (lzok_halted Hok) Hsvc Hsp).
    - intros []. right; left. split; [exact Hbok | reflexivity].
    - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. exact Haddr.
    - intros eff m' ev [He | [[_ E] | (e & He & E)]] Hns.
      + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
        eapply (alloc_refusal_spurious _ mo _ (mkEffect addr [] [(addr, n)]));
          [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
          | apply (proj2 (Hsp _)); right; left; split; [exact Hbok | reflexivity] | cbn [eff_ret]; exact Haddr].
      + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
      + exfalso. apply Hns. apply Ok_inj in E as (-> & -> & ->).
        unfold mmap_errnos in He. destruct He as [<- | []].
        eapply (alloc_refusal_spurious _ mo _ (mkEffect addr [] [(addr, n)]));
          [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
          | apply (proj2 (Hsp _)); right; left; split; [exact Hbok | reflexivity] | cbn [eff_ret]; exact Haddr].
    - intros eff m' ev [He | [[_ E] | (e & He & E)]].
      + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
      + apply Ok_inj in E as (-> & -> & ->). exact (lzok_halted Hok').
      + apply Ok_inj in E as (-> & -> & ->).
        unfold with_mmap_destroyed. rewrite vm_forget_range_halted, with_vmmaps_halted. exact (lzok_halted Hok).
    - intros [He | [[_ E] | (e & He & E)]]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E | discriminate E].
    - intros []. reflexivity. }
  apply (sreach_node segs _ unit _ tt _ Hnode ltac:(RomBase.rob_auto)). intros [].
  rewrite Hun in Hok', Hvis, Hhs. apply (Hk _ Hok' Hvis Hhs Heag).
Qed.

Local Close Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lzok_after_disjoint_op : ltac2:(zQ "i72!q2!u3!o4!old!jk0!hif!m9!hrc!lvc!lpb!lof!qs0!qo1!pt9!pqf!m0!jk7!in8!jtd!hs2!ie!qt4!ov1!ks8!oj8!om3!hr5!lp3!hnb!hu2!mi5!mj0!pu3!qg3!lhc!qtf!ol6!qh2!qh9&@2$6@1$1@1$0#k0@1$1@1$0#k0&@1$5~0>1L~1>1S~1>2Zr~1>3msF$h1>2mo$h4>4msF'$h1>3mo'$h4>1l$a>2hh$a>0@5$h7?4segs^9^8^7@2$h3^6^5>0@2$3Z^3>0@2$3^4^3>0@2$3^4@2$i6+2+k0>0>1x@1$1@1$0#k0>0@2$7@2$3^7@2$9@1$0#k0^1@2$h9@2$9@1$0#k0^1^6@3$2$4@2$e^2^f$hb>0@3$2~1@1$h5^8@3$c@1$h5^a^7^6>0>1p@1$1@1$0#k0>0@3$h8@1$1@1$0#k0^1@1$b^a@3$h8@1$1@1$0#k0^2@1$b^d>0@2$i3@1$1@1$0#k0@1$b^a>0@3$2$a@1$d@1$8^b@1$d@1$8^d>0@2$3@2$i4@1$i0^c@2$i5@1$i1^h1$he@1$d@1$8^e>0@3$2@1$f@1$1@1$0#k0@1$hd^d@1$ha@1$1@1$0#k0>0>1x@1$1@1$0#k0>0@3$2$4@2$e^1^h5$h0@3$2$4@2$e^2@1$hf@1$8^h0$h0>0>1x@1$1@1$0#k0>0@1$hc@2$7@2$3^f@2$9@1$0#k0^1@2$h9@2$9@1$0#k0^1^e@3$2@1$f@1$1@1$0#8@2$h2^h2^2@2$h2^h4^2@2$7@5$h7?4segs@3$c^h6^f^e^h5^h4@2$h3^h1^h0@2$7>1x@1$1@1$0#k0@3$2$4@3$h6@3$c^h7^h0^f^h6^1@3$h6^h7^h6^1@4$i2^h6^h5^h3^h1").
Proof.
  intros L S Zr msF mo msF' mo' l hh [HL Hinv Hh HZ HSZ HZL HLM] Hl0 Hlh Hnw HRL Elazy Hmat Hnd Elim Hbud Hh' HLM' Hmem.
  cbn in *. pose proof (lazy_ranges_okb_nowrap L HL) as HLnw.
  assert (Hhid : forall x, hiddenb (maps_subtract L l hh) S x = hiddenb L S x).
  { intros x. rewrite (hiddenb_maps_subtract L S l hh x HLnw Hl0 Hlh).
    destruct (zinb l hh (bv_unsigned x)) eqn:E; [|apply andb_true_r].
    apply zinb_true in E. unfold hiddenb. rewrite (HRL x E). reflexivity. }
  assert (Hcov : forall x, in_rangesb x (maps_subtract L l hh) = in_rangesb x L).
  { intros x. rewrite !in_rangesb_zcovb, (zcovb_maps_subtract L l hh _ HLnw Hl0 Hlh).
    destruct (zinb l hh (bv_unsigned x)) eqn:E; [|apply andb_true_r].
    apply zinb_true in E. pose proof (HRL x E) as C. rewrite in_rangesb_zcovb in C. rewrite C. reflexivity. }
  assert (Hhs : hid_same L S msF msF').
  { intros x Hx. apply Hmem. intros HxR. apply hiddenb_true_iff in Hx. destruct Hx as [HxL _].
    rewrite (HRL x HxR) in HxL. discriminate. }
  split; [|split; [exact Hhid | exact Hhs]].
  split; cbn.
  - apply lazy_ranges_okb_maps_subtract; [exact Hnw | exact HL].
  - split.
    + rewrite Elazy, (li_lazy _ _ _ Hinv). reflexivity.
    + exact Hnd.
    + intros p Hp. apply (li_incl _ _ _ Hinv). apply Hmat. exact Hp.
    + rewrite Elim. exact Hbud.
  - exact Hh'.
  - intros x Hx Hz. rewrite Hhid in Hx. rewrite (Hhs x Hx). exact (HZ x Hx Hz).
  - exact HSZ.
  - intros x Hx. rewrite Hcov. apply HZL. exact Hx.
  - intros x Hx. rewrite Hcov in Hx. apply HLM'. exact Hx.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma map_has_In : ltac2:(zQ "a1!q2!u3!m9!jk0!hif!lr0!jk7!o4!qu8!oj8&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$4~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$7$3@3$8^3^2^1$6@3$9~0@4$5@1$1@1$0#k0@1$1@1$0#k0^3^2^4").
Proof.
  intros maps a n H. unfold map_has in H. apply existsb_exists in H. destruct H as ([b s] & Hin & Hb).
  apply andb_true_iff in Hb. destruct Hb as [H1 H2]. cbn [fst snd] in H1, H2.
  unfold bv_eqb in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  apply bv_eq in H1. apply bv_eq in H2. subst. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma nooverlap_In_disj : ltac2:(zQ "b1!q2!u3!m9!lr7!qjc!qk2!oj8!old!hif!o4!qr3&@2$2@1$1@1$0#k0@1$1@1$0#k0>1X@1$8~0>1e~0>2e'~0>0@1$a^3>0@3$6~0^3^4>0@3$6~0^3^5@2$3@3$9~0^5^4@2$3@2$7@1$4^5@1$5^4@2$7@1$4^4@1$5^5").
Proof.
  induction X as [|x X IH]; intros e e' HX He He'; [destruct He|].
  destruct HX as [Hx HX]. destruct He as [<- | He], He' as [<- | He'].
  - left; reflexivity.
  - right. apply Hx. exact He'.
  - right. destruct (Hx e He); lia.
  - apply IH; assumption.
Qed.

Lemma rsub_map_remove : ltac2:(zQ "h22!q2!u3!lpb!m9!hif!qv1!om3!jk0!lp3!lr0!hrc!o4!qv9!qr3!pqf!oj8!ol6!old&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>1L~1>4maps~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@1$d^3>0@3$f~0@4$9@1$1@1$0#k0@1$1@1$0#k0^3^2^4>0@2$6Z@2$2@1$0#k0^3>0>1x@1$1@1$0#k0>0@2$a@2$h1@2$2@1$0#k0^6@2$2@1$0#k0^1@2$6@2$2@1$0#k0^1@2$h0@2$2@1$0#k0^6@2$2@1$0#k0^5@3$b$7@2$e^2^9$8>0@2$5^8^7@2$5^9@2$c^8^7").
Proof.
  intros L maps a n Hno Hin Hn HRL HLM x Hx.
  pose proof (HLM x Hx) as Hm. apply in_rangesb_true in Hm. destruct Hm as (b & s & Hbs & Hr).
  apply in_rangesb_true. exists b, s. split; [|exact Hr].
  unfold map_remove. apply filter_In. split; [exact Hbs|]. cbn [fst].
  apply negb_true_iff. apply Bool.not_true_is_false. intros Heq.
  unfold bv_eqb in Heq. apply Z.eqb_eq in Heq.
  destruct (nooverlap_In_disj maps (a, n) (b, s) Hno Hin Hbs) as [E | [D | D]].
  - injection E as <- <-. rewrite (HRL x Hr) in Hx. discriminate.
  - unfold hi, lo in D. cbn [fst snd] in D. lia.
  - unfold hi, lo in D. cbn [fst snd] in D. lia.
Qed.

Lemma rsub_maps_subtract : forall L maps (a n : word),
  entries_nowrap maps ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x L = false) ->
  rsub L maps -> rsub L (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)).
Proof.
  (* 08b1429: the unmap CUTS the range out of [vm_maps] instead of removing the
     entry based at [a] ([Mmap.mmap_fixed_destroyed_next]); a lazy range avoids
     the cut range, so it still lies under the ledger (recipes/lazyledger-munmap.md) *)
  intros L maps a n HNW HRL HLM x Hx.
  pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ n) as Rn.
  rewrite in_rangesb_zcovb.
  rewrite zcovb_maps_subtract by (try exact HNW; lia).
  apply andb_true_iff. split.
  - rewrite <- in_rangesb_zcovb. exact (HLM x Hx).
  - apply negb_true_iff. apply zinb_false. intros Hin.
    rewrite (HRL x Hin) in Hx. discriminate.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_n_facts64 : ltac2:(zQ "d0!q2!o4!lof!hrc!om3!on3!u3!lpb!hnb!mh4!mi5!om9!qh9>3len@1$6@1$0#k0>0@1$8@3$1@1$6@1$0#k0^1@2$5@1$0#k0Z=2nZ$2@1$9@2$7@1$0#k0^2>0@2$4^1@2$c+2+k0@2$3@2$4Z^2@2$3@3$1$2@2$b^2$aZ@3$1$2@2$7@1$0#k0@2$5@1$0#k0^2^2").
Proof.
  intros len Hlen. cbv zeta. intros Hce.
  pose proof (PlacementSearch.page_round_up_Z_ge (bv_unsigned len)) as Hge. pose proof (word_unsigned_range len) as Hr.
  assert (bv_unsigned len <> 0%Z).
  { intros E. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
  split; [lia|]. split; [apply PlacementSearch.page_round_up_Z_aligned|].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma munmap_model_eqL : ltac2:(zQ "60!q2!ie!u3!o4!rg5!rh6>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1@3$3$1@3$5^3^2^1@3$4^3^2^1").
Proof. reflexivity. Qed.

Theorem sreach_munmap_lazy : ltac2:(zQ "j22!q2!u3!lpb!o4!ol6!in8!hs2!jk0!hif!m9!lof!qo1!mj0!old!on3!pg5!ie!qi0!pu3!ov1!ko3!ks8!lg9!kd!lp3!m0!lr0!jk7!hrc!hnb!jtd!io9!lh3!ri6!lte!lvc!qu8!mh4!mi5!qp8!rj1!qr3!rj9!ou7!pqf!lhc!rh6!ln2!om3!om9&@2$9@1$1@1$0#k0@1$1@1$0#k0&@1$8~0>1L~1>1S~1>2Zr~1>3msF$5>2ms$5>2mo$h0>2x8@1$1@1$0#k0>1Q>0$i0P>0@5$h5?4segs^8^7^6@2$6^5^3>0@3$3$5@3$h4^9^8^6^5>0@3$3@1$h9@1$1@1$0#k0@1$hf^6@2$h7@1$1@1$0#k0^4>0@3$3$a@2$2@1$0#k0^5+t7=1a@1$1@1$0#k0@2$f^8N0=3len@1$1@1$0#k0@2$f^9N1=2nZ$a@1$i5@2$2@1$0#k0^1=1n@1$1@1$0#k0@2$e@1$0#k0^1=1h$i2@1$i3^b>0@3$3$a@2$j1@2$2@1$0#k0^5$i6Z>0@1$hd@3$3@1$1@1$0#k0^5@2$e@1$0#k0Z>0@2$d@2$4@2$2@1$0#k0^7^5$i1>0@3$3$7@3$i4@1$c^4^8^5$hb>0@1$i9@1$c^5>0@1$h1@1$c^6>0@1$h1@1$i7^7>0>1x@1$1@1$0#k0>0@2$hc@2$d@2$2@1$0#k0^d@2$2@1$0#k0^1@2$j0@2$2@1$0#k0^1@2$4@2$2@1$0#k0^d^b@3$3$7@2$ic^2^ha$h8>0>4msF'$5=3mo'$h0@3$ie^e^b^h5>0@5$h5?4segs@3$b^hb@2$2@1$0#k0^f@2$4@2$2@1$0#k0^f^d^ha^h9@2$6^2^1>0@3$3$5@3$h4@3$b^hc@2$2@1$0#k0^h0@2$4@2$2@1$0#k0^h0^e^hb^3@3$ib^h8@2$e@1$0#k0Z@3$if^h0^d@1$he^h8>0@4$id^hd^hc^ha^4>0>1x@1$1@1$0#k0@3$3$7@3$h3@3$b^hf@2$2@1$0#k0^h3@2$4@2$2@1$0#k0^h3^h1^he^1@3$h3^hf^he^1>0@2$d@2$4@1$h2^5@2$ia@4$ha@1$1@1$0#k0@1$1@1$0#k0^h3^h0@1$i8^ha@1$h2^ha@4$h6?4segs?2SC^h9@2$6^7^6@4$h6?4segs?2SC^h3@2$6^h7^h5").
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hal Hlen Hnw2 Hhas Hno_ov HX HNA HRL Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (a := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (word_unsigned_range a) as Har.
  assert (Hts : TASK_SIZE = 0x800000000000%Z) by reflexivity.
  destruct (page_round_up_n_facts64 (ms_gpr msF 1) Hlen ltac:(lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 215%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hpr : page_round_up (ms_gpr msF 1) = n) by reflexivity.
  assert (Hargs : munmap_args_ok msF mo).
  { split; [exact Hal|]. split; [exact Hlen|]. split; [exact Hnw2|]. rewrite Hpr. exact Hhas. }
  pose proof (munmap_outcome_si segs msF x8 mo) as Hspec0.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  pose proof (lazy_ranges_okb_nowrap L (lzok_ranges Hok)) as HLnw.
  assert (HLm : m_vm_lazy mo = L) by exact (li_lazy _ _ _ (lzok_inv Hok)).
  pose proof (rem_bounds (a, n) (cuts mo)) as Hrb.
  assert (Heag : eager_used (munmap_model a n mo) + rem (a, n) (cuts mo) <= eager_used mo).
  { rewrite munmap_model_eqL. apply (eager_used_munmap_le a n mo HX HNA ltac:(rewrite HLm; exact HLnw) Hno_ov
      (map_has_In _ _ _ Hhas) ltac:(lia)). }
  set (msF' := advance_past_svc (apply_effect msF (munmap_eff msF))).
  assert (Emem : ms_mem msF' = unfill a n (ms_mem msF)).
  { unfold msF', munmap_eff. rewrite Hpr. cbn [ms_mem advance_past_svc]. apply apply_effect_mem_unmaps. }
  rewrite <- Hun in HRL.
  destruct (lzok_after_disjoint_op L S Zr msF mo msF' (munmap_model a n mo)
              (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hok ltac:(lia) ltac:(pose proof (word_unsigned_range n); lia)
              ltac:(lia) HRL) as (Hok' & Hhid & Hhs).
  - rewrite munmap_model_eqL, munmap_modelL_lazy. reflexivity.
  - intros p Hp. rewrite munmap_model_eqL, munmap_modelL_materialized in Hp. apply filter_In in Hp. tauto.
  - rewrite munmap_model_eqL, munmap_modelL_materialized. apply NoDup_filter. exact (li_nodup _ _ _ (lzok_inv Hok)).
  - rewrite munmap_model_eqL, munmap_modelL_vmmaps. reflexivity.
  - lia.
  - rewrite munmap_model_halted. exact (lzok_halted Hok).
  - rewrite munmap_model_eqL, munmap_modelL_vmmaps. cbn.
    apply (rsub_maps_subtract L (vm_maps (m_vmmaps mo)) a n HX HRL (lzok_LM Hok)).
  - intros x Hx. rewrite Emem. apply unfill_out. lia.
  - assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg msF' (munmap_model a n mo))).
    { (* 08b1429: munmap may also answer -ENOMEM; boost-json is alloc-forced
         (Statements.v:84 agrees_in_abort_modelled Env.alloc_forced_only, Statements.v:57
         halts_within_budget), so under AllocForced the refusal is spurious and the
         config-filtered step keeps only the cut. *)
      apply (node_family_noacc_cfg msF mo x8 unit (fun _ => munmap_eff msF)
               (fun _ => munmap_model a n mo) (fun _ => []) _ (lzok_halted Hok) Hsvc
               (fun o => Hspec0 o Hno Hargs)).
      - intros []. right. try rewrite Hpr; reflexivity.
      - intros []. apply Run.spurious_refusal_not_refusal. unfold Run.refusal_b. rewrite Hno'. reflexivity.
      - intros eff m' ev [(e & HIn & E) | E] Hns; apply Ok_inj in E as (-> & -> & ->).
        + exfalso. apply Hns.
          split; [apply family_off_munmap_true; exact Hno'|]. split.
          * unfold munmap_errnos in HIn. destruct HIn as [<-|[]]. unfold Run.refusal_b. rewrite Hno'. reflexivity.
          * exists (munmap_eff msF), (munmap_model (ms_gpr msF 0) (page_round_up (ms_gpr msF 1)) mo), [].
            split; [apply munmap_ok; assumption|]. unfold Run.refusal_b. rewrite Hno'. reflexivity.
        + exists tt. repeat split; try rewrite Hpr; reflexivity.
      - intros eff m' ev [(e & _ & E) | E]; apply Ok_inj in E as (_ & -> & _);
          [exact (lzok_halted Hok) | rewrite munmap_model_halted; exact (lzok_halted Hok)].
      - intros [(e & _ & E) | E]; discriminate E.
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode ltac:(RomBase.rob_auto)). intros [].
    rewrite Hun in Hok', Hhid. apply (Hk msF' Hok'); [| exact Hhs | exact Hhid | exact Heag].
    unfold msF', munmap_eff. rewrite Hpr. rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    rewrite apply_effect_mem_unmaps, restrict_mem_unfill. fold a.
    apply functional_extensionality. intros x. unfold unfill.
    destruct ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)) eqn:E; [reflexivity|].
    unfold restrict_mem, restrict_mem_by. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
    rewrite (Hhid x). reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

Local Close Scope Z_scope.


Local Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)

Local Close Scope Z_scope.

End WithSegs.
(* [comment removed for export] *)
