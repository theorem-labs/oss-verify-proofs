(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanCeil Scfg RelSpec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsanRefNodes () := KReplay.lz_vm "#$jAC47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?Krespectful_per_oblig!t3$_1C4ELinuxProcessSemantics?!s<22Fs4path!t6,4Init5Logic6eq_ind!srN2Fs!sTK5State7PipeBufK!u^,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!v0#s2bv00I!u\19Datatypes6op!sL#00!u4Q8m_haltedK!v]72eq01!uOG3I!tDP5Model!tzVvmmap!wgR;with!s`&I!u\;0K!u7W1!wU<4prod!wu>4list!tDS7Vm!s-$!tF#!s^PFd!s^%0I!t>Y!s^SIo!s^YFs!s^X9!s7#!s`X8Li!uYY9Time!s`X6VmMaps!{cS;vm_reserved!#4OQvm_!|DVvm_noac!s;#!s`Q<vm_start_brk!saQ6vm!s[U8vm_limit!tuU!~r#_base!saQ:vm_init_spK!xjX!#3>,!#8V3Z!y0#!#8V>;bv_unsign!xx#!sP?7Z_to_bv!sLA5bv_eq!spBbv_wrap!sLAD!th-_in_range!sYA=!t#&_small!sRA@!uE&!ut-!#7t58!#>1$_rI!#<Z>0!#8X73and00!#;7F!#@,;5Riscv7Prelude5bvmapC79OSSVerify6Proofs:boost_json:fuzz_parse3!tB#FileSim;adv_eff_retC13~~~!smP:AgentNodes5epend!sj%K!#:/@1!{6Q=SyscallEffect0!#C:K3Run<apply!uX#ect!s_O@advance_past_svcK!|[?2!yjA4BvWfK!#BVC1!wBP8PropExec6regupd!x,V!si,v_addi!si_4mks!yY&!#:IJ>!{+$!sE+=machine_s!#;8V7MemCopy!#AE=3nat!}//!}J-4True!wGSAllocSim?!y{%zeros_one!{kC!#C<#1!|3B2!zlO;!tP-!~fQMmapSim5zfill!xn&!|nUun!#>:#!yOX7fp_regs!vTB!#KA&1!sHD2!{jZfp_csr!tU'!{%g1!#AzQ!#7/&!tKY7ms!vg%!#9'G9!#9'#_s!t=\8ms_f!t>?!sfB9ms_pc_val!sgZ>ms_svc_pending!vT`sv!se^f!yM#!seY6ms_mem!sd^rom!#E-Q!y|#!}g&!s_P9!s_#!#3i$!t?Ucopies!#3aU!s_Q!t@-writ!t@X!s_'!#=E>6b!#;x#!#3pYb_npc4!#6l@!}d16!#Ge#b!#Eb79False!#\p$!#EE6not!tvY:!tC%_neq!#=o&!#:Q:bool!#<I3!sF32!#Az?1!#GS75!uS$!#Gp9!#=L$0!#;8W6un!#;9,56Stdlib6ZArith6BinInt1Z3leb!sC=!xp#!s`=t!wu3!v--and!sD=3orbC4!s~&4Bool!s'$;orb_f!xZ$r!sb=fst!sC=s!y:#!t#&5Lists4!s+#7ex!s2#b!sB-!v}#HFunc!{U#alExtens!s1$ityIf!s?+_e!s@0!v,<2lt!sB>e!ve=!{\#!sC;7!z\&K!u-'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!{E#!sQ47Env!sT#5PExpr01!sIE2K!t?L!st75Tauto8G!sJ'7C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!vJ<4fi!yS-!sq8C!sq0_soundC5!#6~ISys7!#OO%5w_is0C6!s`M2Mm4!~6#7min!#Zz#!sbV;brk_grow_ok!#f@8or00!#6a8iff!#n@>?eq_p!#oX#!s,#xy!~;6=!~p#_true_!ssBIr!#oy&_!s0,!s}&!s\3>!s\+_Prop@and!t,#_m!s=&!tW6<or!tV?!sx2?or!sw2!w?I2Fs9!#9T%eq!ud?:!#qs+!sM?NR!v%,artial_app!te+!#OZ7!#Y~#1K!xY;2!s@<!#IMQ?page_r!{t#_up_Z!#BTQalloc_top!#7}<app!#6?<sub!t@Q;region_free!|WW=!|W#budget_ok!yy7!{R$!#:h&!u/;:ltb_ir!{J#!sJ<6!sJ#ge!#8N?1!sD@3!~/85proj2!#UdXA!uu#resolut!ve#ok!#Pa&!#7sC4!sJF8!{m?Mtrans_co_!#b~#v_impl!}S-!s`=F!#3R/!#4X4!t_35eKind!#D?<unit!#;x7!se%4kin!#XR?!sf$1!#E#A1!uH5!$##2>iff_T!v4#!#e%#I!#:_?;!yu%!xY$!u38!#=?03Op205!sMI!tyF=!ty#!$$~,!#3+O!#3j#size!t]I3!~7W>!{@#model_next!siW@for!~v#vm!#k~$!#O?Q=maps_subtrac!tOX:!#=|$ants!se\!#SC%!seVD!u60!uy&c!#3mN<AsanRef!#k:#?!$#[,_eta!#3o$!sv]:!sq3!#d>Y!vC,_keep!srd!wv%!srd9!z~+!#O\Bpow!#S9X9u64!#t@%!t1A>pow_pos_nonneg!#;L<!sN#!sJ%!#5c;!#iN#!#JvD5Psatz!sOM6K!#6'L2!#LgD5!sIE7!wX=mul!xcRgentLib7!wX#li!#u4&!#>+67f_equal!#[9Dsub!u<E4!u<<4of_N!#<A5;Zify!#8T%!$8[#!#HH-!tw-8i!#gG#fl!sjB3inj!sIB5mkre!snC9and!#>|$!sOB;rew_!tk%!#~FA:bv!}9#ulu!#_HA?!w5%!#|u+!#49cgrow!#49j!sr-!#Er;!u]$o!vX69SatDivModCZ!v'#!~>&!~iC7di!vZ$!|3=div!sC<=!t7#pos_b!#TE$!sM?!t[#!sM15!u/$8PreO!s/#1Z;!t[#0_r_ext!sL>!st#!sL&!#FZE3!sJF!#3ME3!{bEapp!}>C!sK$2!#6s@1!#5yM1!t?68!t?#Inst7Inj_Z_Z!#=R\;!zX$_ok_na!zXC!#S}%!#Ml?!#`>=6leb_le!#@F]!tz-_pin!#j$@!#Fp9errno!#v,#!#f}ORelSpecB!se+!#3h+!tTV>!#TL'_room!#iW?3!zx>3Pol!yd8!#=07!#P6F!#asF:!sJ<!#N^$2!v'Q6ENOMEM!#qbQtwo_pow_64!wARstack_max!#Lf#!scQB!sc1_val!{5]F!{5%!{2%_not_!ys$!#H\b>mprotect!#F2/!u]J!#xx5gpr!vCQ<map_contains!$0\KMonad7outcom!#qSR!#<Z'F!#^r1!#:,$s!uzQ3Run9sys_inpu!$BWMpecs<s!#hZ$_spec!{mRin_arg!#P-Q8M!x\&=!xe+!tI$!#53V@!si+err_ou!#F{&!t`ZB!su+!#`d,!v0O8in_sysno!uDQ!$?J&!sd'_s!$9XV!v3+!x@/_226!v3aC!}T1!#X`V!sr+I!sr+grows!}&#fli!w6#!wye!tl$ed_b!vSXG!y`,xpose_!~6&!#Md2!#]j:;!#b5&ity!#6_]!w26_!$#{&!yjX:!}Z%2!yiZ!sl11!slh0!sl+K!#6iX!$YfQ!$G=1!$AeQ5event0!#wLO6Kernel4Fork@PID_MAX_ENVELOPE!#>tQiv_overla!#o}<4neg!$%~6:!#n=#assoc!sb<8list_i!$%e82In!xWQ!$,I%@!#pg,!~B#s!#EHV:live_bytes".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos3h5LinuxProcessSemanticsfLinuxProcessSem5Statehf8m_halted35stdpp9bitvectorbdefinitionsl82bv37Corelib4Init9Datatypesna6option37Corelib4Init5Logicpb2eqhf5Modelhf8with_tidhf8m_vmmapshfbwith_vmmapshf6VmMapshfcmkVmMapsFullhf6vm_brkhfavm_init_sphf8vm_limithf7vm_mapshfcvm_mmap_basehfbvm_noaccesshfbvm_reservedhfcvm_start_brk01Zl87Z_to_bvl8bbv_unsignedhffvm_forget_rangena3nilna4prodna4listna3natpb1I3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshq8dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhv0h0advance_past_svchv0capply_effecthf7MemCopyhf9mkEffectU3h5LinuxProcessSemantics5Riscv7Preludeil75bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAgentNodes~~~~~~io65epend69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~isc4mkstisc6regupdisc6v_addil82BVl84BvWfna4consna4pair69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~jjd5zfilljjd6unfill46Stdlib6ZArith6BinInt1Zjoa2lena4boolna4truepb3andpb3iffpb2or5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapjs7bbrk_grow_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AllocSim~~~~~~kgah1brk_resolution_okjoa2ltkga9brk_modeljoa3addhf9page_sizejoa6modulojoa3powna4andbna3apphf9alloc_tophfbregion_freejoa3eqbjoa3lebjoa3ltb79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanRefNodes8WithSegs~~~~~~ksefgrant_ok_na_pinksebgrant_ok_napb3nothf6ENOMEMhf9errno_rethfdmaps_subtract5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectlm3h3mprotect_model_nextkseemprotect_modelhq86ms_gprhfdSyscallEffect3h5LinuxProcessSemanticsfLinuxProcessSem5Monadltf7outcomehfcmap_containshffpage_round_up_Zltf2Okhv09sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Specsmkccsyscall_spechf5eventhfatwo_pow_64lm3h2mprotect_budget_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~mr6h0mprotect_err_out37Corelib4Init6Specifng53sig5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Forkni1h0PID_MAX_ENVELOPE36Stdlib5Lists4Listnme2Inhfalive_bytes3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypenp47Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_tid_halted : ltac2:(zQ "70!h9!kd!n5!p2!qf!r4!rc>1t@1$2@1$0#k0>1m$5@3$4@1$3@1$2@1$0#k0@1$1@2$6^2^1@1$1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["FPX1"] "##%~h01mh11tp;1p;2p-1R0p10000p4p710p9P!s6%S!s611?R1!s8,P!s2$2!s3/31!sS-]!sQ'p1002Up4p7!s?$3E!s?%R0p8!s6$a!sA$P!s5&4O!s5+g005Ej10Tg005jj15Tg006Hj12!s/$kj11Tg007Mj14Tg008Dj23!s/$^#0!s$-5#2R0g009C%10f0#4'3W0W1o"). Qed.

Lemma with_vmmaps_eta : ltac2:(zQ "40!r4!qf!s7!t2>1m$0@3$1$0@2$3@1$2^1^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["FPX1"] "##-4p'0h06m_fsysi0!s0'h14m_ioi0!s-%h25m_limi0!s/&h36m_proci0!s0'h46m_timei0!s0'h51mi051mh64m_fdi0!s-%h74m_vmi0!s-%h89vmst_lazyi0!s3-h9!s2%mapsi0!s3-h:A!s2&terializedi0!s;8;1vp;1p;2p;3p;7g00:9j13Tg00;0j25!s/$jj32Tg00<Dj74Tg005Ej10!s/$jj1:Tg006Hj19Tg00=:j28!s/$Zj11Tg00>:j37Tg008Dj26Tg009CR0P0f0R1#3/51=201P1g00?2g00?jR2P2g00@bR2g00AZR3g00BRR4g00CLR5g00DER6f7R7f5R8f4R9f3R:f2R;f1R<P1F4R=#3/5==20=]4]2]3]0]!t2%E?g008^#0!s$-:#9R=/8=#1%1=f<f6R==778P9P:P;P!sw$,60X46X25X34X03X12W:W8W9!sF%O3n0110;00013010910810:W7W6P=P!so-O7!sO$5000170106107101100103102104W5o"). Qed.

Lemma vmmaps_eta : ltac2:(zQ "b0!u0!qf!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke>1h$0@3$1$0@8$2@1$9^1@1$6^1@1$8^1@1$a^1@1$3^1@1$5^1@1$7^1@1$4^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["FPX1"] "##,Rp'0h01hh16vm_brki00!s0&h2:vm_init_spi01!s4-h38vm_limiti02!s2+h47vm_mapsi03!s1'h5<vm_mmap_basei04!s60h6;vm_noaccessi05!s5/h7;vm_reservedi06!s5/h8<vm_start!u/%7!s6281vp;1p;8p;3p;2g00F6j1?Tg00G0j1>!s/$fj13Tg00H`j12Tg00I[j1=Tg00JPj17Tg00KGj15Tg00LBj14Tg00M;j81Tg00;jj36Tg005Ej10!s/$jj18Tg006Hj19Tg00=:j2<!s/$Zj1:Tg008Dj2;Tg00E?R0P0f0R1#?%>1%31%21%=1%71%51%41G1=601P1g008^#0!s$-8#9R2/<2#:R3g00N2f7R4f6R5f5R6f4R7f3R8f2R9f1R:P1G1,;0X22X52W3X12X82X63X43W7P4P5P6P7P8P9P:P1O8n01108000180106103105107100102104101W0o"). Qed.

Lemma Z_to_bv_u_eq' : ltac2:(zQ "60!h9!qf!hld!n5!hm0!hma>1a@1$3@1$0#k0>1z$2>0@3$1$2^1@2$5@1$0#k0^2@3$1@1$3@1$0#k0@2$4@1$0#k0^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanRefNodes ()) ["FPX1"] "h01zh11Hh22b1h32b2h41nh51ap;1p;2p;3p;6g005Ej13Tg005jj1;Tg006Hj12Tg00NPj20Tg00;jj31Tg00O:j25Tg00O`j3:Tg00PDj29Tg00Pjj28Tg00Q]j37Tg00RIj26Tg00S8j64Tg008^#3#3#3#3#3#3#;R0#2R1g00N2R2f0R3f1R4,00512P2f2R5,001503f3R6511X02g00SVR1%23R7%24R8g00T4%25?14310651064512R9[10541053512%26?154[R:f4R;#2?165\9A:543P3n2001000000120000000W3W2W4P:^38^27^41P3P01006R1,50R7P6P21901100;9123X021806970110071601E4O4b1P4P3E4W1W0W5o"). Qed.

(* [comment removed for export] *)

Lemma vm_forget_range_halted : ltac2:(zQ "80!hld!kd!p2!qf!h9!r4!hn8!n5>2lo$0>2hi$0>1m$5@3$3@1$2@1$7@1$4#k0@1$1@3$6^3^2^1@1$1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["FPX1"] "##$Jh02hih12loh21mp;1p;2g005Ej10Tg005jj15Tg006Hj12!s/$kj11Tg007Mj14Tg008Dj23Tg00N2R0g009Cg008^#0!s$-5#2#1f0#4'3W2X00W1o"). Qed.
End FPX1.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hp7!ns9@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : ltac2:(zQ "h53!h9!n5!hoa!hp0!p2!hp7!hpe!hq4!qf!htf!ihc!ij1!ik1!ikb!ind!is3!jg7!jgf!jh9!ji3!ji8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$e@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0@3$8$9@1$a@2$b@6$f?2fx^6^5^4^3^2@6$d^1@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~2~2@1$2$c@1$2@2$3@1$1@1$0#k0$6@5$h0?2fx@3$h1^6@3$h3@1$0#5+aKv$7@2$h4@1$0#5+a^1@2$h2^5+4^4^3").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanRefNodes ()) ["WithSegs"] "h03memh12pch21rh34regsh43romh52x8p;1p;2p;7p;6p;3p;5g005Ej10Tg00TOj1DTg005jj13Tg006Hj14Tg00U4j2CTg006kj1;Tg00U`j7:Tg00Vgj68Tg00=Zj17Tg00=:j22Tg00Wkj11Tg00XKj66Tg00YIj29Tg00ZBj1BTg00[?j15Tg00[]j2ATg00\@j3<Tg00\cj3=Tg00]fj2>Tg00^ij5?Tg00;jj3@Tg008^#0R0#DR1#3R2%00R0#0R3#0#0#0#3#4R4'C%33#4R3#;\4R5p,2fxR6f5R7f4R8f1R9f3R:f2R;f0R<F:g00_jP6P7P8P:P;P9E8P<%73,24#11244#1R3P3g00a1#1g00ai,24#1E6'9#BP6%01#5R1g00bH1A21d5<2==7<%50,>8P:P;D?3@eX24X54X45W0X14W3o"). Qed.

Lemma adv_zeros1_epend : ltac2:(zQ "h83!h9!n5!hoa!hp0!p2!jif!hp7!hpe!jj6!hq4!qf!htf!ihc!ij1!ik1!ikb!ind!is3!jn7!jg7!jgf!jh9!ji3!ji8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$h0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a$b@1$c@2$d@6$h1?2fx^8^7^6^5^4@6$f^3@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8@3$5~1@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1~2~2@1$2$e@1$2@2$3@1$1@1$0#k0$7@5$h3?2fx@3$h4^8@3$h6@1$0#5+aKv$9@2$h7@1$0#5+a^3@2$h5^7+4@3$h2^2^1^6^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##=,p'0h01nh11Hh22Hch31bh42b1h52b2h62Hmh71ah81eh93memh:1oh;2pch<1rh=4regsh>3romh?2x8i001zp;1p;2p;3p;4p;8p;6p;5g005Ej16Tg00TOj1lTg005jj1ETg006Hj14Tg00U4j2k!s8$kj1fTg00bdj3\Tg00=:j2GTg00d0j4DTg00Wkj1@!s8$Pj3CTg00e0j27!s/$hj3LTg00;jj31Tg00fij2=Tg00gbj1iTg00hfj2WTg00iHj1^!s/$jj1]Tg00jmj80Tg00[?j1VTg00\@j3H!tU$Zj1ZTg00XKj6FTg00l4j1S!s/$jj1;Tg00mij5?Tg00nYj1ATg00oYj1:Tg010Zj1BTg011`j18Tg012_j1>Tg013^j1<Tg014\j19Tg015Zj1QTg016Sj1PTg017Kj1RTg018Dj3OTg019=j1TTg01:6j2UTg00O:j2j!s8$oj3N!u3$cj3MTg00]fj2KTg00^ij5ITg008Dj2hTg00S8j6JTg01;Tj1eTg01<Wj3dTg00NPj23!t$$`j3_Tg003Ej6`Tg01=Dj2a!s/$cj1bTg01><j4cTg00YIj2XTg00ZBj1YTg00Vgj6[!vt$]j2gTf7R0f6R1#Af5R2f4R3f3R4f2R5#>f1R6f0R7G0p=2g00_jR8?167p=5g008^#6R9#lR:#ER;%69R9#6R<#6!s$$ER=#4R>'k%E<#4R<#f\>R?A\2671G>>R@P>P>P6P7CD%@@RA3CRB,72AL672RC51?e1=2A/7B=1?CRDePDg0!s0$g01?cPDP8P7f9REp,2fxRF#iRGf8RH1W>2RI%^>RJ%]FRKP0P1G0RLP;P>%6:#VR:g00bHRM5H;RNP3%Z<,G>#@R<!t_$4P5CD=C@AROPAg00a1#@RPg00ai!sM%QEFRR#S%;LD?%ALRS%:L%BL%8L%>LRT%<L%9LG0n010!s#$20001RL#;PL!sP+PL%<LRU%QR,=U%PR'7%RR3O%TR'U%9LG2!sV,V9R9,j=RR5N=PJ!sb'!sK$PFAMEN31KH9RLAL450RUP1DI'5X3DP>1K09RDP;P>PNP3PED?REPEPEPSPHPIPJPT!v:&T#AR!s:&%>TRT1=0A/7ORO!sD$VP7PJPJPVPOP1G2PEPGPL!s8$KPU!sH$U'5X3>P?AL561RO!t227!t2%!sZ&!s6%2/5UX:?!tj&4PHD?RUPGPD!s~&OP2G0,h81=1A!w\$5P6!w\&@'7R8P7EJAN=0RRT%e0EJPU!s$$HPGP01W>3RG!sm$1P2G0RK#ARUP0PGPJ%>KRL!s=&I!s9%PIP8P2G2RIPT!tL$!s6&PFAMHN4PDPOP2DIRO'5e!t~+<P@PAPPPQEFR@#S%;KD?PU%:K%BK%8KPL%<K%9KG0!xf;@!xf$@'7%R@3O%T@!xf3=N=R!x]2/5ORLePLeg01@CRL=H;MRJ9d;NP;PNPJ%4;?1NJRRg00SVR=%47RU%46RDg00T4%45?167g00N2RH1345134631[R81356135751H%44?156RI[1334133551H\IA_567P6n20!{='12!s-%0W5W4W0P8^5D^4U^0=P7!t^%P6O413;N13;J51HPHP:PHp-0P7g01@aRJg01A>PJn01!sz%3!t'&!s'$X8HPMPLP7E`PJ1aJ7b1b2b1W2%bReCcEJ1XK@#Y/5Oeb6PFP0P1P2P3P4E[P5P<PB!wg''X#YPFPM1g;:d9H;:=M051K19PCP3DI'5eX0>X7>X<>X?>X>?W9X;>W=o"). Qed.

Lemma adv_unmaps1_epend : ltac2:(zQ "h83!h9!n5!hoa!hp0!p2!jif!hp7!hpe!jj6!hq4!qf!htf!ihc!ij1!ik1!ikb!ind!is3!jo0!jg7!jgf!jh9!ji3!ji8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$h0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a$b@1$c@2$d@6$h1?2fx^8^7^6^5^4@6$f^3@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~2@3$5~1@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1~2@1$2$e@1$2@2$3@1$1@1$0#k0$7@5$h3?2fx@3$h4^8@3$h6@1$0#5+aKv$9@2$h7@1$0#5+a^3@2$h5^7+4@3$h2^2^1^6^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##A#p'0h01bh11nh21Hh32Hch42b1h52b2h62Hmh71ah81eh93memh:1oh;2pch<1rh=4regsh>3romh?1xh@2x8hA1zi001zp;1p;2p;4p;3p;6p;5p;8g005Ej14Tg00TOj1wTg005jj1JTg006Hj16Tg00U4j2v!s8$kj1uTg00=:j2NTg00d0j4MTg00Wkj1?!s8$Pj3ITg00fij2=j3eTg01AZj3Fj4dTg00NPj20Tg01B\j2STg01C9j2R!s/$Vj2QTg01D3j2HTg00iHj1\Tg00;jj31Tg008Dj2[!sJ$Qj2r!s/$nj1kTg00S8j6@Tg01EMj3i!s/$jj3gTg01FGj3f!s/$cj5cTg00e0j2<!uB$Zj1bTg01:6j2>Tg00gbj1aTg00hfj2V!tU$jj1`Tg00jmj82Tg00[?j1UTg00\@j3ETg00XKj6GTg00l4j1T!s/$jj17Tg00mij5DTg00nYj1BTg00oYj1:Tg010Zj1CTg011`j19Tg012_j1ATg013^j18Tg014\j1;Tg015Zj1_Tg016Sj1^Tg017Kj1YTg018Dj3WTg019=j1XTg00O:j2t!uN$oj3P!ty$cj3LTg00]fj2OTg00^ij5KTg01;Tj1qTg01<Wj3p!se$`j3oTg003Ej6lTg01=Dj2m!s/$cj1nTg01><j4jTg00YIj2ZTg00ZBj1]Tg00Vgj6h!vG$]j2sTf7R0f6R1#Bf5R2f4R3f3R4f2R5#Af1R6f0R7G2p=3g00_jR8?167p=5g008^#4R9#wR:#JR;%49R9#4R<#4!s$$JR=#6R>'v%J<#6R<#uR?\>R@P>P?1N>>RAP>P>P6P7CM%?ARB3IRC,=2RDAF672REg01?CRF10=5RG10=7RH'S10=6RI,RG,QH'HRHPFP?P7%\<RJP0P6O1RKn010!s#$20000PFP?10=4RL/SI1RLG,QI'HPJP!sN251?X0F!su$HPJP1P7!sr5RL,[?g01?cRG,rH%kHE@PFP?Ai>>7,0=RH/SIAg!s3%,RH!t9$XA!u_%5P6CM=IABRI5fA!tO5=1?LeAe1I7P5P6P1P7Cd51?eX?>Dc1<DB%b<,N>#?R<'>=1@ERDePDPFPGPFP8P7f9RGp,2fxRD#aR?f8RL1V>2RK%\>RJ%`DRHP0P1G2RMP;P>%4:#UR:g00bHRN5E;ROP3P<PB!t{$4P5!t{&Ag00a1#?RPg00ai!tP%QEGRR#T%7MDD%BMRS%:M%CM%9M%AMRT%8M%;MG2!uW01RM#7PM!sP+PM%8MRU%_R,=U%^R'<%YR3W%XR'>%;MG3!sV,U9R9,t=RR5P=PJ!sb'!sK$PDALGO31OL9RMAF450RUP1DK'5X0FP>1O09RFP;P>POP3PGDDRGPGPGPSPLPKPJPT!v2&T#BR!s:&%ATRT1=0A/<B/><RA!sG$VP7PJPJPVPAP1G3PGP?PM!s8$HPU!sH$U'5X0>P@AF561RA!t527!t5%!sZ&!s6%3/5UX:@!tm&4PLDDRUP?PF!s~&AP2G2,[81=1I!t[&8P7E@AP=0RRT%q0E@PU!s$$LP?P01V>3R?!sa$1P2G2RH#BRUP0P?PJ%AHRM!s=&K!s9%PKP8P2G3RKPT!t@$!s6&PDALLO4PFPAP2DKRA'5e!tr+<PBPIPPPQEGRI#T%7HDDPU%:H%CH%9HPM%8H%;HG2!x];I!x]$I'<%YI3W%XI!x]3=P=R!xT2/5ARMePMeg01@CRM=E;NRJ9p;OP;POPJ%6;?1OJRRg00SVR=%67RU%66RFg00T4%65?167g00N2RL1045104631[R81056105751L%64?156RK[1034103551L\KAo567P6n20!{4'1!}f$000W5W4W1P8^5F^4U^1=P7!t^%P6O410;O10;J51LPLP:PLp-0P7g01@aRJg01A>PJn01!sz%3!t'&!s'$X8LPNPMP7ElPJ1mJ7b2b3b2W3%nReCjE@1ZHI#]/5Aeb6PDP0P1P2P3P4EhP5!wg$C!wg%'Z#]PDPN1s;:d9E;:=L051O19PEP3DK'5eX1>X7>X<>X@>X>@W9X;>W=o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : ltac2:(zQ "h20!h9!hma!n5!qf!v8!jq2!jq8!jqf!jr6!jrc!js2!r4!u0!s7!hke!jvb!kk5!klb>1m$b>3req@1$2@1$0#k0>1r@1$2@1$0#k0=1h$c@1$d^3>0@2$h1Z@2$1@1$0#k0^3>0@2$5@2$1@1$0#k0@1$e^2@2$1@1$0#k0^4>0@2$5@2$1@1$0#k0@1$4^3@2$1@1$0#k0^5@2$9@3$h0^7^6^5@2$a@3$3@1$2@1$0#k0^5@1$4^4@2$8@3$3@1$2@1$0#k0^5^6@3$3$6@3$f^7^6^6$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##Kwh01Hh11bh24__x1h35lemmah41rh52Hgh67__arithh74__ffh88__varmaph95__with:4__x2h;1xh<1yh=1Bh>2E0h?2Hbh@4HposhA2HshB1hhC1mhD3reqp&0p;1p;2p;3p;4p;6p;;p;7p;8p;9g005Ej1?Tg005jk103Tg006Hj1nTg00:9j1HTg00NPj22Tg01Gej2^Tg00H`j1JTg01HAj2;Tg00I[j15!s8$]j2ITg00;jj30Tg01=cj1PTg01I:k202Tg00Wkk101Tg00=Zj1z!sC$[j2_Tg01J9j1t!s/$Wj1qTg01KBj2p!s/$ej2UTg01LHj4OTg00iHj1mTg01M3j6k!s/$Wj2hTg008Dj2DTg01N9j2f!s/$ej3eTg01ODj4dTg01P6j1RTg01Q0j1GTg01CVj24Tg01DQj2<Tg01<Wj3>!sJ$lj3@!sA$3j27Tg01RlR0j23Tg01SFR1j26Tg00T4R2j28!s<$_k20!u{$TKj2~!s/$lj3yTg01Ubj6MTg01VTj2wTg01W4R3j6v!s1$ej3`Tg01XZj4sTg01YAl;rTg01Z<j4E!s/$Wj3\Tg00S8j6ATg01[1j3[!s/$Kj1KTg01\Ij1ZTg01B\j2Y!w7$:j2oTg00F6j1VTg00G0j1XTg01]Aj3TTg00O:j2C!v+$9j2W!sA$^j2STg01^;j3QTg01_5j2]Tg01`7j1l!s/$Wj1uTg01a;j2a!s/$[j1xTg01b9j4j!s/$Wj4cTg01c2j3iTg01d@j7{!s/$dj8|Tg01eHl9}Tg01fBj4gTg01?CR4f0R5g01?cR630p=:f1R7g01g5R8g01gTR9P9g01h4R:P5g01hTF{p=Lf3R;P8P9P9P:f2R<P7P5G|p=bg01i4R=9045p=1A@<75=04=,8;p=9p-0R>P1g01iTf5R?f4R@P;P!sd$M9}p=FP>P1P7P5Cgp=N!sd+p==P4P6!sQ'EAp=Bg009Cg008^RA#?RB#?!s$'$03RC#nRD%H<g00E?g01@CRE12C<'^%J7,2C12C;';%5<!s2%@';g00N2RFP21I75#:A0F<7#PRG[A0F75#P1I<7#:[RH1I;<#:\G20275P5n20010!s#$12!s-%0X<FW;PH^<F^;FP5f6RH,2CRGPEg01jERI$01RJ%zIRI1_F7%tFRK%qFRLPF1pFERMg01k11UFARACO,LL%m9RNPL!w8'PFPAg01kXPM!sE$EkCb1hL:R:P5P<1D4=RM1f5<#1dAeFE7CdR9b7b8b9X2F1^E5A0F7Eg01@a[[^2FP5f7R8,2CROP@O2b6O3b0%R?RP#:RQePQP4P4%G?,2C,4O,<5%5?RQ9>CHRRP4P412CQRS,4ORTA>CH8RU/<RRVf8RW?@8HRX,7VRYn!vF'!vE$RZ!s61#1A0DHQRQA0DH8R[PWP8P8C9R\'3R]'6X14!t9$<65PRP!sc4/6]!sH&P5PVPY!sF9A>C?HRZ%5@R^9>C?R_'<R`A@8H?Ra'7Rb#1%1`Rc%1aRd'8'6%1Y%1VRV%1XRX'8RYP5P]P]200>]ReEFW31~`a%1ZRa%1_Rf'3,6cPY%1URU%1RRR'3RY/8XRcPVPYP5PXPXg01l?9y>1RV/NXRgEMP]P]P!st%wZ_A0D?HRZ,6aPc13[RRc/8XRaPYPcPUP[P5PRPR1NVREvPXPXP!sg0A`C?HA0D?^RU,6fPa13[QRa/8XRfPcPaP>P>^=>P1P>!|z$1CsP0P3P[1NV[PRPQP5M;r!s~9^13ZU/8dRdP][PZP8PHPHC9,3URUPf[P2PaPX%5H90D8RXA0D8WRaf9RfPWPWC9RZ'3P5A0DWfR]%58Re90DW'3P0f:Rg90DfRR%5WRV!s1$[f<R3f;R1;=g%5gR>90D1A0D13f=Rc?=33RY'8'3[!sy$g1RhPDP3f>Ri?=c5%5390D7RjA0D7iRkf?RlPiPiC9'3[X4DRm%51Rn90DcRoA0DccRpA=iccRq'8PpPq1DDcRrP5CE3\X5YP1P5EAW0P5O1%5f90DgPDP>PmA=c3>A0DnnA0Dnc/8q1DDn3[W5!sY/!#3',2!s-$!s'$W0P7P5O2!#3I/!s/&X0dP0PQP\13aXPfPWP8C9P5PDPeA0D5gA0D5V'3P1PgP5C9X4DA0DefR8A0DeeRa'3A=gfeR\1DDe9\8a!}^&VRa,4E/75!~1$KaRa/4a%ZW,Ya1oDDR8%VW%XW3T1CCag01loRQ,Wa/Sa,CC3Q'7P=!|i11]1V'7RV!s>3#1!}F/!sC8M12CeRM,4ERV/76%lVCB14MM%uMCB!tn$HgRV#5,2C!u+$14aM'7!u/+%KMRM'4%ZV,YM%VV%XV5T81CCa1WMQ!u$?ge!s<5#1eP\eCEPWP5EAX0XP5O1P2P]A=gff13R[!w2$f!wL&313kjPlPiP7C9\qX4D13poPqA[po!yM$!yK+X0h!xU6!#8x&0Z!y641000!s'$X0UCEO2!s$%12C^R^,4GRZ%:Z1;SO[1;^G%:T[1aG^PJPIPF1_F<P7%xFCjPKPL!#8v%mg1UFBCO,LLRLPNPLCbP:P!#8`+X:FR91;571;7<[^2F^:FRFP5POPSP<O3b6Cc!wW%1<66P_!xD$ZP`Pb!va1Rb!#6t4Ue%J@,2CR`!u1'%J?,2CRZ/;O[1;`G14OZ#:[1aG`P9P!tE%ZP;!tE/%G@,2C,4G,<6P_P!t59RHP5CBb>!{O&?R5%HHRU#G,2C'4,<P%5URU9>C@RP!sJ&U,45A>C@?/<PRPA@H?@,7P!t+1!t:3%5;90D@A0D@?PHP?P?C9'3R;'6RPePPeAiH?@/6;eW?WAW@bBX4DWDWCo"). Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : ltac2:(zQ "70!r4!qf!h9!s7!v8!km1!n5>1m$0>3req@1$6@1$2#k0@3$1$0@3$5^1@1$4@1$3^2^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##1;h01lh11bh21mh33reqh41vp;1p;2p;3p;8p;6g005Ej14Tg005jj1TTg006Hj1LTg00=:j2I!s/$Zj1STg00Wkj1RTg00:9j1@Tg00I[j1?Tg01nNj3=Tg00;0j21Tg01oQj27Tg00F6j19Tg00NPj2FTg01CVj28Tg01D3j2ETg00G0j1DTg020Vj3QTg021Rj3CTg01]Aj35!sJ$fj1ATg022Qj2BTg023Pj26Tg00H`j1>Tg00JPj1;Tg00KGj1:Tg00LBj1<Tg00M;j83Tg024Yj1KTg025ij1JTg00S8j62Tg0274j1HTg028@j2MTg01`7j1N!s/$Wj1GTg029Lj3O!u`$jj3PTg009CR0f1R1f0R23Pp=0g008^#4!s$-TR3#LR41I44R4#SR5%R4R6f2R7#@R8%?8R97=1/17,72/07X05g01?CR:g01?cR;%98R<P:P5g01@CR=1F39R>'8/E2%D8R??Q>>R>AC199=54?R@n010!s#$20000%A8RA1B99'6RB%>8RCP9%;8RD%:8RE%<8R8G3/17/07X1:P:P;P!t<$P2P>P!sr2PBPCP9PDPEP!s[05P6P<A542?!sH805!sH+6?16A2!sJ8g00E?R5%@1R8112!s<$45%K1%98R5%D8R7%A8RE%>8RD!vU$%;8RC%:8RA%<8R?G3%J8E2P5A546716E6PDP9PCPAP?G3/11/01e1B99R?%H9RAE2AC2991M29E2!vt$3,8=R=/E;%N=E21833%G3E2A=829/11R8!sh$76!s-$P?PAE217?!s4$AO29!t/$W3X20o"). Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : ltac2:(zQ "hc1!h9!hma!n5!kme!hm0!qf!hld!klb!r4!kn5!ko1!jif!jj6!hp0!u0!s7!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke!t2!km1!kob&@2$4@1$0#k0@2$3@2$1@1$0#k0^6^8>1m$8>1d$6=1h$e@1$f^2=1b@1$2@1$0#k0@1$h1^1>0@2$7Z^3>0@2$7Z@2$1@1$0#k0^2>0@2$7@2$3@2$1@1$0#k0^3^5@2$hb+2+k0>0@3$5$6@2$a@2$1@1$0#k0^4$9Z>0@3$5$6@2$a^7$9Z@3$5$8@3$ha~0~0^9@2$h9@8$h0@1$h7^7@3$b@2$d@1$2@1$0#k0@1$2@1$0#k0@4$c@1$2@1$0#k0@1$2@1$0#k0^6@2$4@1$0#k0^8@1$h4^7@1$h6^7@1$h8^7~0@1$h3^7@1$h5^7@1$h2^7^9").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "#$9Jh06__sat3h14__x1h24__x2h31Hh44__p1h54__p2h64__p3h74__p4h84__x3h94__x4h:4__x5h;4__x6h<2H0h=2H1h>3H10h?2H2h@2H3hA2H4hB2H5hC2H6hD2H7hE2H8hF2H9hG7__arithhH4__ffhI!tj%1hJ!s/%2hK!s/%4hL8__varmaphM5__withN1qhO2q0hP1rhQ2r0hR4__x7hS1zhT1bhU1EhV1lhW1nhX1xhY2HahZ4__p5h[2b1h\2b2h]1mh^3Hb0h_4Hbalh`3Hbrha2Hdhb4Hdalhc3Hlthd3Hnwhe5Hreq0hf5Hureqhg1dhh1hhi3reqhj1yp%0p%1p&0p;1p;2p;3p;4p;6p;8p;<p;7p;Bg00:9k10BTg00I[j1}Tg005Ej1V!s/$jk10HTg006Hj1\Tg00NPj21k10LTg01C9j29Tg00[?k107Tg02:RR0j2uTg01GeS00j22!s=$ok10uTg00O:j2dTg01HAj2HTg02<5k20Y!s0$]k30WTg00;jj3<Tg01=ck10;Tg02=Aj1e!s/$`j2_Tg02>Ij3aTg02?2j2xTg00Wkk10<Tg00=Zk10ATg01J9k10`!s0$Wk10_Tg00TOj1~Tg01KBk20?Tg00iHk10Z!st$^j3k!sC$ek20=Tg02@Ak30XTg01MWk20!v;$8Dj2QTg01N9k20!s0%ek30PTg01ODk40O!t9$4R1j2@!sl$dj2iTg02AAk208Tg01a[k10NTg00S8j6ITg02BEk60KTg003Ek606!uD$:k20ITg01nNj3t!v@$0j2=Tg01oQj2gTg00F6j1sTg00d0j4[Tg00G0j1r!s8$Pj3>!s8$fj1zTg00H`j1qTg00JPj1pTg00KGj1|Tg00LBj1oTg00M;j8J!xV$Vj2ZTg01D3j2nTg020Vk303Tg021Rj3mTg01]Aj3`Tg022Qj2hTg023Pj2f!uI$bk302!xl$`k30G!sU$^j2UTg00PDj2vTg02CGk301!s0$jR2k109Tg02DHk30F!s0$nk10ETg02ELk40D!s0$om<0CTg02FTk60TTg02G=k40U!s0$hk10!vL$Q]k30sTg02HQk30rTg02I?k30qTg02JKk60pTg01`7k10o!w`$;k20!uO$bWk40lTg029Lk30jTg02KWk20!x:$L7k20!ue$Lhk20gTg02MIk20!zX$Mfk20bTg02NMk20cTg02O4k20d!s0$Zk20eTg01I[k20f!t<$9k40^Tg01LHj4bTg01d@j7!tN$P@k60]!s0$dk70@!zO$3k60kTg02QHk30\!sW$dj8!|_$Qkm<0!ww$RPmB0[Tg01@CR3f0R4'2p=Cg01loR5-0i4p=4g00N2R6?<43p=6f1R7,H3/@4p=X20h45p=N1H34p=320g45p=D20a45p=:f2R81i57/945<6p=E20b45p=G1245,@7p>0420c45p=L12571H43'@p=F20d45p=M20e45p=KA<674p=51H371245'@p=Pg01jER9?>74p=yA>9749>98p>00f4R:f3R;!s;+5>95>9p=020f64p=^P6P8P7P4H0^p=A20=64p=WP8g01g5R<g01gTR=P=g01h4R>P6P7g01kXR?P4Cbg01hTR@Flp=BP8P<P=P=P!sK+1RAP4CbP!sF$8P7!sF+4J0]p=c!sX-7P4K0@p=R!sL1kp>0>B0\!ul$]!s~&mgP4Cbp=j!sR/!t3%{f5RB!s;+:P;!t14GYp=Sf6RC!s>+B!sN$!s4'!v'$GYGYp=7P!sK/!s{0GY!sM%p=;1274,@8p=w1H43p>0:P6P7P!up$p>0MP:!sa+;P8!u%3GYp=O!sW$!vn$p=T!tZ5p>0519749<68p>0Jg009CS01?<74p=?g00SVS02P6!s$$2P2!uI&!se$N<0np>0R!sD&!s$%0P4P7P8P0P;P:PBPCf7R0f8R2f9R<NB0[p>0SQ01&0B7g00E?%}4g008^R?#VR@#VRA#VS03#V#V#VRD$0HRE#\RF%C811E7RG#C11E8/9:&07@RH&07DRD'uRI'211E;RJ#4#6%4C#6&0uB11EBRK12KI'X11EC/92,dEPF11E0/9<RK%N<%3<1H35RLf;RM#4#3[[11E2RN#N%3Nf:RO,1ERP#4#3\L[20YHDS04%CH%3D%CI[[S05%3HRQg01A>RRB0WHD7UWYS06%3I\R^YQS0711EMRQ#DA<653RR$0;RSf<RT,1ERU%:U%4U3E[%GU1235RVf=RW,1ERX#4RY#3S08004Y[%LX1253RZf>R[,1ES09#4R\/F\[Q09#Mf?R],1ER^#:S0:#6\R%K^f@R_,1ER`#4S0;/5`\R%:`S0<P6fARa,1ERb#4RcP6fDRd#DfERe%:e%4e3E\S%GefFRf#4Rg/Pg\V%LffGRh#4Ri/Fi\Z%MhfHRj#:S0=!t?%jfIRk#4S0>/5k\R%:kS0?P6fJRl#4RmP6P111EkRn#312nI11ElRnfLRo'9Rp12pI'XfCRpfKRq!uY$@#311EoS0A/2IS0BPdP7O1S0C%3TS0D\LS0Ep-0Rrg02S6Rs#eRt#eS0F,_6S0G1_6t1_6sS0H5a6S0I5a6g02SUS0J'xRsP!s$~!s$~!s$B&0<9Rt,ys:00ssD0!s$W&0A9S0K%^:%^CS0L7A8%^BS0M%^0S0N7A;7A7&0`6S0O&0_6R9P9%~@#WRs20?63Ru5B9Rv&0Z=R=%WARA%W@R@5B9S0PP=P9P9PvP=%~?Rw#~#WS0Q=B9uS0R!sC%A89suRxP=A89sA1c9<S0S5R9!sD+usRyP=1c9OS0TA89As!sD+20>9vRzP=Q0Q9k6s/]A9B9@!tD-WwR{20=6?R?!t`$U!sB-Vw#WRw=B9uRv!s=&!tU&{1c9MS0V!t7+P!tP%TS0WA89{!tP,PzP=Ak6sw/]{9B9?P=P9AB9AuS0X!s2&{uS0YP=P91]?@S0Z20?6H>0X6ES0[589S0\!sP$89u?S0]!s2'@S0^P=P9Q0Z,ju,{9Q0\ESF7F7F;!s$520V9>S0_P4P8g01?CR>g01i4Rs'Q20Q48=<>sdB0P637H0OS0`bHbLbMX16X26X86X96X:6X;6XR6X4rX5rX6rW7%6:S0a15:8[S0b%6BS0c%62Rs[S0d12C3S0e120CS0f/@O[S0g%C0S0h1202S0i,@T[S0jg01@aRz\sS0k1i<M/92S0l,5C[S0m%6<S0n152C[S0o%6O%6T!t-$p12M312TO/@a[S0q%CTRyAwpMW[S0r%6WRxPz[S0s1i[]/9TS0t,5O[S0u19TW/2IS0v%CWS0w%C]S0x19]_S0yQ0y/2I'X[[[\x\x[!s#+^16^26^86^96^:6^;6^R6^4r^5r^6r^7rP4%3WS0z&0:WS0{%3CS0|&0:CS0}P0P[P5PCPWfQS0~fOR|,1ES10P2P<POPMPTP]P_PafBS11PpPlPqPofMR}fNR~OJbGb0W>WFP7P4O2n20010!s#$12!s/&bQbObEbDbCbBbAbPbNb@b?b=b<b3bIbJb0bK+0811E4/5KRKePKP619NO11E<RK/24XS6%NO%3O%4T#3\L[%NK%3K%4Q!s4$Q04Q05Q06Q07%DU%:X=EXY\S%GX%3\S12004\\VQ09#L%4^S13Q13'F\Z%M^Q0<!#8f$`15cb\R%:bR\P6Q11,1ERY#4RKP6%De%:f=Efg\S%Gf1Pii\V%Lh%4jS14Q14!ss%jQ0?!ss%k15ml\R%:lS15P6%4qRiP6P1%3n12nIQ0@Q0@/9}'2PdQ0A#3S0A11E}S16/2IS17Q0CQ0EPtQ0K%^8&0N6Rn7A7S18Q0OP9Q!|q+-0M?DOQ0_Q!|$1%C71978,27!y5&P4fRS19fPRg!xN$:P|O3!x'>0!x'MPGP4EI12NG1dE3RN9<F8S1;PFP6&0LEP;PNP4J0K11ENRN,5JP611E:RG154NXS6P419QWS1<P;J06Q1</5N%N[%3[%4_!x^&X%3XQ13!x^6`AEb\c\S%Gb1PKK\V%LY11EpR\#4S1=Q1=!wd%\11EdRd#:S1>!wl%d11EeRe#4S1?/5e\R%:e!ti$fS1@#4P6%DkQ15=Elm\S%Gl!xf'q%4oS15Q15!t$%o%:}S1A!s{%}%4~S1B/5~\R%:~P6%4|!#?;%~Re#3S1C12eIPzPjQ1:#3Q0~,1E/2I!xa%Q0F#eS0F#e,_6Q0I5a6Q0J'xRXP!s$h1yXt:00XX!#<?4Q0KQ0L?A:nQ0M7A8%^;7A7!z-$!#9o$P91TA?DOS0I!#:++P9Q03#WRX/TuDOS03!#;F'wuS1DP=A89wAS1E1c92!#;e/wS1FP=Q0SA89AwS1G!#;e0S1HP=P9Ak6wX/]AS1I,T?DOS1J!tK/1T{@DOS1K!s;%Q!t@'{S1LQ0T!sy+Q!t:%VA89{wS1M!s?&1]@?S1N=B9u!uA%X!s,%Y!s,%!|t&]P=Q0WH05!#:d'!s+&!}-5!#:0/!#:,&X7rXZrQ0a15:7[S0aQ0c%60[Q0eQ0f/@<[Q0hQ0i,@M[Q0k1i<O>0JB2[Q0n1520[S0n12O312M</@][%CMAwaOT[19<2#6Ph\y\y\s\s!#8a>!#8^,^ZrP4PzQ0zQ0{Q0|Q0}P0!#8S%T,1EfV!#8K/aQ11PjP|PgQ19fSS0hOH!#8EhbUbUWUQ1;$0;RzePz20IFFRz$0ARs&0<zRyAtT::/=[,g4%sT!#3]$FPM1dEWS0iC[%rTRA5>z%zTS0e%qTS0fP:%pTS0c%|TS1O%oTS1PGJ/=[RX'?XVsP>g01?cRNQ1;P>Ps1Z3Q/n4B03AGQS1QAm::M=`zAS1Rn!uO'20000Q0e1h:M'fS1SQ0fP:Q0cQ1OQ!t-&/?XXT>P>P!t$'P4Q1QQ!sl4!sc?s!uW$OB02E;OS1RC[=>zyS1QQ1;A`z4A!sd=VsPsPyQ!vB'B02E:MS1;!si%=`zAQ0e/f4!se<Q02%\4S1P%\7S1OP1%\8?<7411;811;7'5RA[11871184'5%\;?<87[S0c%\:?<;8\AB0G874P4!#9C6W\W[WWQ02Q1PQ1OQ0c]\][]WP4PEQ0iQ1;P61UGQ,vE1dE[S1P,1ERA/54XS6S1OP6Q1<1U4U,vE,5AXS6!s8$/UQRAQ1OP6PW19U[/UU,!sY$%NWS1OQ0z%4]#3\L[S1<%NUS0c%3UQ12!s8$2!#9E0^S0fQ0<Q0;5E`\SS0<%G`S0e1Pcc\VS1S%LbS1T1FKK\ZS1U%MYS1V%:\S1W#6\RS1X%K\S1Y%4dS1Z/5d\RS1[Q1>P6Q1?P6%DjS1\Q0?Q0>5Ek\SS0?%GkS1]1Pmm\VS1^%LlS1_1Fii\ZS1`%MqS1a%:oS1b!t1%c%KoS1d%4}S1e/5}\RR}Q1AP6Q1BP6P1Q16#3RiQ1719eg/UeRe,5gPhQ10#3RdQ1:/2IRK!#?L,Q18Q0OQ1N>016@9B9?!#5241974/U7,54!#?9&Q0h,1ES0hfUS1:O2!#?6hQ0i,1E!z[$<!zd$!wi0Q!wf&eQ1SQ1TQ1UQ1VQ1XQ1YQ!w-/Q!w'%1]Q1^Q1_Q1`Q1aQ1cQ1dP!vK0P!vF$2gI,XgPh!#<u',_6Q0GQ0H5a6!#<t'UP!s$~!s$~!s$B1yUt:00UU!#T9XS0JQ0KQ0N!#>{+Q0L9An;7A7S0L!#F2%I!#>l%!#=A,P9Q1EQ0SESS0S!#=@,P9Q0TQ1GESS1G!sM%J!s,%K!#><+Q0RH05!#T?'!sw+LQ0VESS0V!sw2WQ1MESS1M!s>'H!s>%Q9k6w/]{R{,T@DO!#>G51NQ0[589!#>T2P91ju?,{9Q0[989?!#RF%!s$+!#>^AR!#>a/Q0aQ0dQ0gQ0jQ0kQ0l,5B[Q0nQ0pQ0qQ0rQ0sQ0t,5M[19WT/2I%C[Rw12]I,X]\w!#O~U!#>A1!#Op%Q0hQ1:!#Og2Q11PpP~P|PgQ0~Q19!#Oc$X>KXFd!#>F`-08WEI1vEA%3ARw&09ES0a,uHS0n,2ARn'@12AIRU,@wPwPnPwPU1Qrw:0FwwP6P6Q00P4XX6RUQ001274$0EXj6XX6PAPA1Q6AQ0nPI!{V&6P6g02TA1u74H0D,Q6X]6XW6PHPH1Q6HQ0aPDPUPUQ02&094,Q6WXPEPD1Q6DJ0RN:0SN<0CJ0T!#4T~!#4T6eI,Xe!#4T+!}-%L!#Hs,Q!#]S$!|u&Q!|d%Q!|S%!{Z,1I!{Q+!s]'U!sV%!|[$Q!|J%Q!|921T?{!|-8!#[P$!{y&!|/+Z>016?R{!#[M&[989{!|1-;!s+%!|3Rb!|3-mQ0o!|+-uQ0vQ0wQ0xQ0y/U]R{12{!#Y$Y!|$:1:Q0h!|$~!|$3H0U&0tE9wwAe:0sEAEIPGP;EIQ1;,1EB0rE:MEIO4b31dETR:Q1R5<FPFQ0i%sWRAPFPFPTP4C[%rWRw5>z%zWRd%qWRKPB%pWRg%|WR|%oWR~GJ/=]P!sZ&Q1PC[=>zwPdPKPBPgP|P!sH%'?XTFQ01/QXQ1;P4J06b3%sMRXQ1Q%rMR]5`z%zMR~/fy%qMR|P;%pMRg%|MRB%oMRKGJ/=WPX!t8$OP:!t7$]!va$;PgPBP!sG%R:'?e1h;ORF%NTQ0D%4[!#Ug%Q%3QQ08!#Ue1Q09#DQ0:Q135E^\S%G^Q0;Q0;'P\V%L`1Fcc\Z%Mb%:Y!#T^$YQ1=/5\\RQ1WP6Q1ZP6%DhQ0=Q145Ej\S%GjQ0>Q0>!si%k1Fmm\Z%Ml%:q!si%qQ15/5o\RQ1bP6Q1eP6P1Q0AQ0BQ16Q1@'HPfQ1CQ10!#U>'!#BS,P9A89?@!|o$j?@!#Zl612471H78!#Zj'Q0@Q19,1EPk!#ZdjRk:0q;OR8EIAm;;OP;P;POP4P2P7J0pEI1Z3PR7/nN&0o7EI1ZJPR7A<>7N1HQG[1HPJ1ZGQ=<>N[20mJPPkH0lEIPXP>Ps%}MRs,1ERE,Z31ZJE'nB03]JEAm;;s=`z]!#M:01h;sRs,f!y%3/?:eAtM;;/=WRM/?:e1gy!s-$PFP8EI1gs!s4$&0BWRM#},h;!sU''g/?:RMePMeB0j;;!sr$bebcbfbib`WbW_WdW^WabTbhXg6W]o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model : ltac2:(zQ "30!h9!r4!n5>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h12!h9!n5!s7!jif!jj6!hp0!r4!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke!t2&@2$5@1$1@1$0#k0@1$1@1$0#k0&@4$4@1$1@1$0#k0@1$1@1$0#k0^3^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0\1m$6@2$h0@8$7@1$e@1$2^1@3$3~0~1@1$b@1$2^1@3$3~0~1@1$d@1$2^1@1$f@1$2^1@1$8@1$2^1@1$a@1$2^1@1$c@1$2^1@1$9@1$2^1^1").

(* [comment removed for export] *)
Definition grant_ok_na_pin : ltac2:(zQ "50!jq8!h9!hld!r4!n5>1m$3>1a@1$4@1$1#k0>1n$2$0") := ltac2:(zQ "h40!h9!kp2!s7!n5!hma!kp9!hp0!hld!r4!kpf!kn5!kqb!hh9!hk0!kme!kr9!ks0!ks7!ko1!hm0\1m$8\1a@1$3@1$0#k0\1n$7@2$1@2$1@2$1@2$f@2$h2@2$4@1$0#k0^2$aZ@2$h1Z@2$4@1$0#k0^2@2$h0@2$e@2$4@1$0#k0^2^1@1$9@1$2^3@3$b@3$5@2$6@1$3@1$0#k0@1$3@1$0#k0@1$d@1$2^3@1$c@1$2^3^2@2$h3@1$0#k0^1").
Definition grant_ok_na : ltac2:(zQ "50!h9!n5!jq8!hld!r4>4hint@1$1@1$0#k0>1m$4>1a@1$1@1$0#k0>1n$3$2") := ltac2:(zQ "50!h9!n5!hld!r4!lh6\4hint@1$1@1$0#k0\1m$3\1a@1$1@1$0#k0\1n$2@3$4^3^2^1").

Lemma grant_ok_na_unpack : ltac2:(zQ "h70!h9!n5!jr6!qf!s7!hma!jq8!jqf!hld!kp9!hp0!r4!kpf!kn5!kqb!hh9!hk0!li9!kme!jq2!klb!ko1!hm0>4hint@1$1@1$0#k0>1m$b>1a@1$1@1$0#k0>1n$8>0@3$3$6@4$h1^4^3^2^1$7@2$2@3$3$8@2$h5@2$5@1$0#k0^3$dZ@2$2@2$h4Z@2$5@1$0#k0^3@2$2@2$h3@2$h2@2$5@1$0#k0^3^2@1$c@1$4^4@3$3$6@3$e@3$9@2$a@1$1@1$0#k0@1$1@1$0#k0@1$h0@1$4^4@1$f@1$4^4^3@2$h6@1$0#k0^2$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##8}h01Hh11mh21nh32H0h43Halh54Hposh64Htoph72b1h82b2h93Hrfh:1ah;4hintp;1p;4p;2p;3g005Ej1ATg005jj1PTg006Hj1NTg02Tej4ITg01D3j25Tg00T4R0j22Tg01TKj2MTg00NPj21Tg01C9j24Tg00:9j13Tg01\Ij16Tg01B\j2;Tg00=:j2OTg00F6j1@Tg00G0j1?Tg01]Aj3>Tg00O:j2=Tg01^;j3<Tg01Gej29Tg01HAj2:!s/$]j2FTg00;jj3BTg02V1j2L!tU$Vj2E!s8$Qj2JTg02W1j2KTg01Z<j4GTg02KWj2HTg01?CR1f0R2g01i43Bp=0g01loR3,H2g01@CR4'Fp=71E42p=81H23p=Dg00N2R3?B24p=Cg008^#A!s$-PR5#NR6g009Cf3R7f2R8f1R9P2CI#0P01592#0%08R:%09R;'2[R<%02,2;1589#0R;[%07/2:\;1M92P9n20010!s#$12!s-%0X81X71R;P<^81^71R1P21157R<#7%8<'514<8f4R<#3R:#6';'5R=1O66R>%@:%?:3>1=587<7R:P9O3%0=%0:'2P0115<R:#7%8:'514:7f5R:#3R=!sl%#0%@=%?=5>>1=577<<#0115:R=#D#C194=14=<f6R=#3R?#6':%@?%??!sV%<7<:#0'2'2'2!u#$=R?#7%8?'514?:f7R?#3!t7'f8!tG$@#@%?@!sf%=7<?#0P;P1P2f9R?,15R=#7%8='5R@14=:f:R=!si%R:P8O3%0@!uO,=!uO+#014:?f;R:!sS%!u;&?!u;&?14?=f<R?!tN$!u;$!tS0!u;1?!tR+#0f=,15/4?f>!t#'!t|&!tz$1#7R;%81R1!tj%;%01'2P0f@R1,15R;#7#0%8;#0fAR;,15!t`01fB!t`$=!t`%!wM,17<;!t`1#7#0fC,15#8!z3$F92#0AB389[R;AB3921F!z'$1[AB378\11L!z&<13X23P;^13^23P2fE,15#DR;P4!u<$C;P01E92#019!t-$19921E!t,&19!t+$J!t+KP4fG!v%$P7O3194;P01;!t'$:89[R01:921;!|7&1:78\;1K!t'B0!u1+IR0,15fH'4R;fJR7#3#6R1P:O31:;1!|P$1!w8&1R41410fK#3R1#6':R;%@1%?1!w:%07<7#0R7'2R0'2P<P4P0P8P;P7P2P?CGCGCGb6b0b5b0b4b0W5W4P9P2O2!tw0!s/&b0b3W6W0!sHB9!sHD0X23X:6W1W;o"). Qed.

Lemma grant_na_pin_not_errno : ltac2:(zQ "c0!qf!h9!n5!jq8!jqf!lj8!hld!lje!r4!lk7!lh6!jq2>1m$8>1a@1$2@1$1#k0>1n$6>0@2$bZ^1>0@3$0$3@3$a^4^3^2$4@1$5@3$0@1$2@1$1#k0^4@1$9$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##Lzh02Hgh11Hh21Eh37__arithh44__ffh58__varmaph65__with71mh81nh92Hah:4Htoph;4__p1h<4__p2h=4__p3h>4__x1h?4__x2h@4__x3hA4__x4hB4__x5hC4__x6hD4__x7hE2b1hF2b2hG2H0hH2H1hI2H2hJ2H3hK2H4hL2H5hM2HnhN2_HhO6__sat1hP!s/%2hQ!s/%3hR1ahS1qhT1rhU1zp&0p;1p;3p;2p;6p;4p;7p;5p;8g005Ej1;Tg005jj1yTg006Hj1oTg02WQk30@Tg01D3j26Tg00T4R0j2=Tg01TKj2sTg00NPj21j1qTg01C9j27Tg00:9j18Tg01\Ij1<Tg01B\j2?Tg00=:k20!sK$F6j1TTg00G0j1ZTg01]Aj3YTg00O:j2XTg01^;j3WTg02Xaj1vTg00;jj3>Tg01=cj1OTg01HAj23!u$$1j2rTg02BEj6p!sw$^j2`Tg00Wkj1l!tM$Zj1kTg01a[j1jTg01J9j1i!s/$Wj1hTg00[?j1DTg01KBj2I!uo$Oj1JTg01MWk20FTg008Dk20ETg01N9k20!sV$Nek30CTg01ODk40BTg02YYk30!up$3Ek60>Tg02Zgk10!ve$Gej24Tg02L7k20;Tg02<5k20:Tg02:Rk206!s:$]k305!sN$hk20!sX$MIj2[Tg02@dj2b!s8$fk200Tg02NMj2~Tg02O4j2}!s/$Zj2|Tg02[dj1{Tg02\Bj2zTg02=Aj1F!s/$`j2L!sA$cj3aTg02>Ij3QTg02?2j2xTg01I[j2PTg01b9j4]Tg00iHj1u!v:$3j6t!sS$^k301Tg02QHj3U!tr$Ak302Tg02CGk303!v|$ej2dTg02Pdj7fTg02]Lk508Tg02^0k609Tg02KWj2n!xU$]j2m!y|$Vk20!yk$LHj4\Tg01d@j7gTg00dPj3^!s8$dj8_!t'$@k60ATf0R1#;!s$%p=Ng01@CR2/31p=9g01?CR3g01i4R47>1p=0g01loR5,n1p=51m12p=C20<21p=Bg00N2R6f1R7;>1p=:P6P7g01mgP1C\p=S!s4$g5R8g01gTR9P9g01h4R:P1g01hTR;Fgp=2%J1#Jp=RA>612p=Kg01jER<?^71p=wf2R=A^<715^<p=A1d61p=G!t9&kX!t9%@f3R>P8P9P9P:P=P7P1G_p=H!sM'1!sM%EP7!sK+1J0Ap=VP=!s8+7P1Ffp=e!sK'g02^TR?P1P!tv$cf6R;!sS'f5R@f4RAP!tD4G_p=Mg009Cg008^RB#;RC#;RD#NRE#yRF#oRG%91B0@>=7#0P01671#0%0=RH%07RI'=[RJ%01,=I16=7#0RI[%0>/=H\I1s71P7n20010!s#$12!s-%0XF3XE3RIPJ^F3^E3RJP111FARH#5#C%BH'617H>%8@RH#<'?'6RK207GGRL%TH%ZH3Y1XF>7WARHP7O3%0K%0H'=P011F@!sl1A%8;!sl'#0!se%5YL1XFA7W@#0g02_4RH#vRK9>G;#OP1f7RM,1FRN!sn%N'617N;f8RN#8!so'f9RO#8RP#T%ZP!sv%M7WN#0PIPJP1f:RJ,1FRI!si%I'6RL17IOf;RI!sk%RPP=O3%0L%0P!u0&IRP!sU%P'6#017PJf<RP!sU%#0A>GPK!tm$=RL,1FRQ!sS%Q!t]$>,1F/7Lf?RQ!sW'P01?71#013=7[R013711?!wj$R[13>=\R1r!wh<76X86P0^76^86P1f@R0!t0$QRQfARR#8#<RSP7O313QSA>GRKRRPGP6%qFfBRGPKP1Ep11FG11FKRK':P6PKfDRK,1F/:1XU6P1g02_iRG/`HRS%l<RQ%k<R<%j6RT%i6RU%h6RV%DBRW,I6%JBRX#;RY#;#DRZ,I6R['S'220FV:R\P1P=20E3420D1=#0dB0C627H0BR4b4b5b613WZP1b313WHePQP<PTPU%JXRT#J#R!s$&D!t:$,S[,2VP\P!sa+ZW!sa%HWe60?HJ0>fCRH!uB$SfE#8RS$0=%<Sg02`bRS'7/4Gg02a_%;E#N!s$&DRG9>6SfF,1FRW00;5%9W1325fH,1F#5#9[[%DCRW%DERE+0:142W%9E206WER3,42[[%9WR]g01A>R^B05WE7UW9%93\^^9]fI,1F0045A>652R]#Of!zD$^1[^5,b5%5^'7':[200^51425fK!sE$#5RE#914E5'=[1~^51452fL!sB+,4513E2'=[1}^5f!|'$^/[5#K\]1|^5fN!sQ&/:^\]1[^5P6fOR^!uL$P6p-0R]%{B,z6REg02S6R_#F#F#FR`#FRa#FRb#F,L65a61L6b1L6a9a6E1L6`1L6_5Q6!s%+g02SU'xR_1w_Q9A__!s&77A_P<P6P61P6AP=1P6;C]P7!s6$@P>1P6MC]C]PUPVPV%GYRY1I62RU'@,2VR<%u9R_%GCRQ%GXRX!s<$CHP_PVPVP<P_%GTRT/@U!s=-1EYU,2VP_1EYQ,2V1VVO5e!sE-UY!sE%VVJ1EQY,2V!sE-PV!#7@'<EtP_B016YT=U6Q,@X!t4+%JC#GRC1I6G!ta$!s:$GDRD=U6C1I6W>026FRW'E!sC&B036W[!si%P_PV1d6BRB9U6X/SD!s:&!tI+!s-'?1@QU,cV1EUX,cVFf!s@,I08J09!sp$SUB!uF'ICHFM!s$'!|B,X>6X?6X@6XA6XB6XC6XD6X;]X<]W=%K@1:=>[%K;%KN[14M214NA/=J[142N14@O,=P[%KOg01@aR4[1bJI/7;,:M[1:OG17OJ/431`3Z,:O17JN/3I%CJ%BI'6#0%9JPK[!s#,^>6^?6^@6^A6^B6^C6^D6^;]^<]^=]P1P4%971372P=P5PSfR#8#<fQ,1FP7fPP>PAP@P;PMPIPPPLP0PHP^OEb3bTbSbLbKbJbIbHbObPbQP4ebGb1b2b2W2%OReb:b1W:W0P7P1O2!#6l/!s/&b0b1WN!sHD0WMX86WRW7o"). Qed.

(* [comment removed for export] *)

Lemma grant_na_not_errno : ltac2:(zQ "c0!h9!n5!qf!jq8!jqf!lj8!hld!lje!r4!lk7!li9!jq2>4hint@1$1@1$0#k0>5model$8>1a@1$1@1$0#k0>1n$6>0@2$bZ^1>0@3$2$3@4$a^5^4^3^2$4@1$5@3$2@1$1@1$0#k0^4@1$9$7").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanRefNodes ()) ["WithSegs"] "h02Hgh12Hnh21ah34hinth45modelh51np;1p;2p;4p;3p;5g005Ej10Tg005jj16Tg006Hj12Tg01HAj21Tg02Tej45Tg00;jj34Tg02b`j53Tg008^#0#0#0#0#0#0#6#2R0g009Cg00N2g01@Cf0R1'1g01?Cf4R2f3R3f2R4f1R5C5g01i434P2P3P4P5P1D3W0W1W5X20W4W3o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model : ltac2:(zQ "30!h9!r4!n5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h10!s7!h9!hma!n5!r4!ll3!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke!t2!kme\4addr@1$3@1$1#k0\1n@1$3@1$1#k0\1m$4@2$f@8$6@1$d@1$0^1@1$a@1$0^1@3$5@1$c@1$0^1@2$2@1$1#k0^3@2$h0@2$2@1$1#k0^3@2$2@1$1#k0^2@1$e@1$0^1@1$7@1$0^1@1$9@1$0^1@1$b@1$0^1@1$8@1$0^1^1").

Lemma mprotect_model_next_eq : ltac2:(zQ "60!h9!r4!n5!qf!lpb!lr3>1m$1>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$1@3$4^3^2^1@3$5^2^1^3").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanRefNodes ()) ["WithSegs"] "h04addrh11mh21np;1p;3p;2g005Ej10Tg005jj14Tg006Hj12Tg02d7j31Tg008Dj23Tg009CR0g008^#0#0#0#0#0#0#4#2R1f1f0f231,30X21W0W1o"). Qed.

(* [comment removed for export] *)
Lemma mprotect_outcome_si : ltac2:(zQ "i92!h9!n5!qf!hoa!hp0!hm0!jq8!jqf!hld!ls5!lsf!hma!mgd!s7!mh8!mi7!klb!jif!hp7!hpe!jj6!jr6!jrc!js2!mj9!htf!mjf!mna!ik1!r4!moa!ikb!kn5!mp2!hh9!hj2!mpf!lr3!mv0!kme!ko1&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>2ms$h9>2x8@1$1@1$0#k0>5model$hd>4addr@1$1@1$0#k0>3len$8>0@3$2$8@2$b@1$0#k0^4+u2>0@3$2@1$1@1$0#k0@2$9^6N0^3>0@3$2$8@2$i8@2$b@1$0#k0^4$i0Z>0@3$2@1$1@1$0#k0@2$9^8N1@2$5@1$0#k0^4>0@2$h0Z^5>0@2$h0@2$i7@2$b@1$0#k0^7@1$f^6$i1>0@3$2@1$1@1$0#k0@2$9^bN2@2$5@1$0#k0+3=1n@1$1@1$0#k0@2$5@1$0#k0@1$f^8>0@3$2$6@3$e@1$i3@1$d^b^a^1$7>0@3$2$6@3$e@1$i2@1$d^c^b^2$7>1o@1$c$a@2$h6@3$hb@3$ha?4segs^h0^f^e^1@2$h7@2$i6^e^1@2$h5@3$2$6@3$i4^e^d^4$7@3$2@1$c$a^1@4$h8$a@6$hf@2$5@1$0#k0Z@1$3@2$4@1$1@1$0#k0@1$h2@1$1@1$0#8@3$h1~0@4$h4@1$1@1$0#k0@1$1@1$0#k0^d^4~1~1@1$3$hc@1$3@2$4@1$1@1$0#k0$h3@3$i5^d^4^e@1$3$he").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["WithSegs"] "##^'h04__x1h11bh22H3h36__sat9h41zh51Hh62H4h72H5h82H6h97__arithh:4__ffh;4__p1h<8__varmaph=5__with>1qh?1rh@1EhA2HahB4__p2hC7!t1$10hD!s0&1hE4__x2hF4__x3hG4__x4hH4__x5hI4__x6hJ4__x7hK5lemmahL2H0hM2H1hN2H2hO2H7hP2H8hQ2H9hR3HalhS4HlenhT5Hlen'hU3HmahV3HnahW3HnohX3HnwhY3Hu1hZ4addrh[3lenh\1mh]5modelh^2msh_1nh`1oha2x8p%0p&0p;1p;2p;3p;4p;6p;=p;7p;8p;9g005Ej1<Tg005jk100Tg006Hj1tTg00NPj21k10DTg00TOj1cTg00[?j1ZTg02eFj28Tg00;jj35Tg02=Aj1@Tg00O:j2GTg01[Kj1MTg01C9j2?Tg01Gej2!t5$:9j1jTg00Gfj1zTg02fDj3b!s8$0j1uTg02g?k10CTg02L7j2^Tg01HAj29!s8$hj2eTg01=cj1qTg02@dj2TTg02Mfj2\!u'$4R0j23Tg02NMj2_Tg02O4j2a!s/$Zj2`Tg00Wkj1PTg00=Zj1yTg01I[j2YTg01J9k102!s0$Wk101Tg01KBj2l!s/$ej2~Tg00iHk10!sV$MWk20XTg008Dj2}Tg01N9k20W!s0$ek30VTg01ODk40UTg02h7k20RTg01]^j2{Tg02:ok10Q!s0$Rk20NTg02<5k20M!s0$]k30LTg02[dk10GTg02\Bk20F!s0$cj3w!wQ$`j2vTg01a[k10BTg01b9j4X!ts$3k60ATg02?^k30@Tg02QHj3gTg02CGk30?!vm$Ak30>Tg02AAk20=Tg00S8j6:Tg02iJj3rTg02j@j3mTg02k;j2!tz$l0j6!t?$SFS00j2!t8$m6j2pTg02nBj3W!w3$:j2fTg00d0j4U!s/$Pj3ETg00XKj6VTg02d7j3oTg01Rlj2K!sz$_j2nTg02oMk10<Tg030Dk30;Tg031Kk40:Tg032Wj3[Tg033ck10!yF$BEk60!zn$3Ej6xTg01><k407Tg01P6k106Tg0355k10HTg036@m=0ITg037Sk405Tg038Ak30JTg039Xk30KTg03:^k304Tg03;dk30!z+$KWk20O!zJ$Ik20PTg01LHj4iTg01d@j7|!s/$dj8kTg02>Ik30S!wX$2k20!{'$P@k60]!s0$dk70\Tg03<jk40[Tg01eHm90Z!}\$2R1f1R2f0R335p=4g01loR4-0O3p=7g01@CR59513p==1053p=Rg01?CR6g01i4R7753p=;1953p=220P34p=Df2R8g01g5R9g01gTR:P:g01h4R;P1P2g01k1P3Cig01hTR<F|p=C!s?&mgP3Cip=dP2P9P:P:P;P3P!sI$>f3R<!s;+8P2P3Gkp=J1v13p=FB0S123p=6g02SU-0T3p=Qg01jER=?E23p>0EAE=239E=8p=H1~13p=I!t_'X!tF%S!tF/J0]p=hP8!s8+2P3K0\p=]f6R>!s<'f5R?f4R@P!tk4Gkp=Og03=bRA!s:%H0[p=Lp-0RBQ00g01iTP?P@P<!sE%N90Zp=sg00_jg008^RC#<RD#<S01#<RE#<#<#<RF$00RG#tRHg009CRI11G<RJ%cCRK#cRL!sM%#c#<#ZS02'4g02S6RM,8?=5H8%7J#=f7RJ%@MRN'81GG<55H%R@11G>%M?'?g02_iRO'0f:RP%@NRQ'8%ZK,GGRR55H%MJ,GGPH%jP#zf9RS;b3#;f;RT#j#u?bP2#;&0CARAf<RU,1GRV/^4%2V1954RVf>RW,1GRX#7RY#2[[f=RZ,1GR[/e4A5145R\#qR]%DX,T4/?Y,4X[1\X41054RXf?RY,1GR^#7R_#210_4'3[1_^41045R_f@R`,1GRa#7Rb,0419b5'3[1aa4fARb,1GRc#DS03#=\\1`c4fBRd,1GRe#7Rf/4e\\%DeRgP1fCS04,1GRh#7RiP1%P=Rj%y=R=1Y12S05&021Rk&011Rl1l15Rm1~1CRn5ClS06&0Y:Ro1dmn,>lS07CJ20Xl;RpP3P81}67S0820W38#;dB0V152H0UR7b:b<b=X01%R3%22[^01P3fDRqPYO2b9b?b>b8b7b6b2b5b3-0RT%MTRr,9T1?T4%ZCRs'{,9r'3&0QZ%2[%ZDRr%ZFRF+0NRt,0['320MrFS09%Rr%2F%Rt[[S0:%2rR[g01A>RuB0LrF2UWAS0;%2t\u^A[S0<1^a4%2a%2fR[\V[1ec41T4g/?f,4e\]1\e4%2iS0=10i4'3\X1_h411GqRg#7Ru!wW$u5'3\_1ag4fE,1GRF#DS0>!wV%F4fF,1GRv#7S0?/4v\\%DvS0@P1fGRw,1GRx#7S0AP1P0fHR0,1GRy#210yt100OPPfJS0B,1G#2fK,1G/0tPTP2O1%2?\V%@QR0#@Rz#@R{#@R|#@#@#@R}#FR~&0GC-0F1RC%F|5w1R|'6#Q%FzRz%F0'6R0,6~#Q%@}#FR}/60#Q16}|#Q%FQR|%FN9w1C1v1MRC'6'6,6z,6}#QR}%F{16|C,6z'6#QRz20Ezj5H}9H}!s&+7H}3H3HP=P1P1P11Y1JP<&0B1S0CCXP81Y1?CXP2!sA$@PJ1Y1>CXCXPkPlPl%ILRL/Sm,>lR}PoQ01#IRz%cD#IRC'S,>lCJPoPlPlP}Po%IER|!sT%!s='AClLmPoAClLz1hlS5]!sA/mLPo1hlPAClzL!sA-Pl!#5L'}J0APoB0@1L|=g1z,SC!t,+1dmC,>lPoPl%<K#IR|,dn,>lAg1nL1l1s60?1,d|,>l5]!sM$Ag1C|%IDRD5C!s7$1Szm!si$AClnDCJFO!s$%PpP!|A,XE1XF1XG1XH1XI1XJ1X;BXBB%=?14<@[%=>f8RD#=[10J510D?/3P[%RD10>S,3U[%=Sg01@aS01[1TPT/?J,4D[%2D19>P1?>T/{s,9P'31?PT/0D%=P10SP[!s#'^01^E1^F1^G1^H1^I1^J1^;B^BBP3%2>19>5PJP4fMRs#MfN,1GP>POPsPDPSPPPTPUP<PbPwQ0BOBb9b3WQW2P2P3O2n20010!s#$12!s/&!~m$PbO!~q&3bCbDb2b510TOPH1GGU11G3Rs/4ZX1HQ09Q0:Q0;Q0<1^^4%2^%7cRz#2!~%$a4Q03,T4/?z,4c\]1\c410f4,3[\X1_e4104i19i!}u&h4%Dg!}l%g4%7FR[/4F\\Q0>P1Q0?P1PjP=Q05PkPl1l1r>0>1G9ClnRnPoPlQ06PoQ07=]ln!x62103t%R2Rn%28108t'3!vx$P3PwPTPdO3!#5^4bCbD-0=U18`NRwPDE:11Gw/4Up,4segsRw?rb`RD?mY81NDMS071NDNRt1NDQRrPDPYP8EB'AArwdbRf?m`<1NfM1NfNRz1NfQRaPfP`P<EBP31p`<R|AW`Y>#;RC1GG5RL&00E#t#y,fH#PRE1fHHR}PHPHPYP>CU%P}R;3EP;g00a1#PR:g00ai!sT%9EVR{AoY>`g03>`#PR03L95A<'3'KR~P~1nB~EsWK!tw%PHP`Q02,4sX1HPU&0<DB0;wb`E:H0:PH18bMRUP3PzP!u++/A~X1H!sB$NRz18dMRMP3!sF8QRaPM18dN!sH$!sF2PWP3!sD$Q!s@4RPYP!sX5IA[YW?R~!sC$R!sC'RfAL{3095A<,3C,K|'AX\IPWPzPR!wT'1pY8RI11GzRd#M,GGRQ9WYW#;PLPE!vx$WPQCU=E};P;P:P9EVA[YWQ;L095A8'3'K'APf11GMRf!sg+`Y!sg-Y!sg5`Y!sg&<'3,K|P3A[`Y>=L{!t{-RCPC1nBC!wY$!u&-g01?cRD,}6&09R=56DdPPPGPzPLA5HzLRPPHP1&0DGPMPLP3J0811GLRM,4fP1Q04/8N,1G143MX41P3!u~$x14YM1^c4%2cQ0=!}b$e4%Dh!}b$i,4h\]1\h4%2u10u!#<d%g4104[19[!}d&F4Q0@!}d%v4Q0A/4x\\%DxP1%7y!}b%P1Q0CP2Q05!#9M$%IKRK!#8u$Po!#8V$KPo1hl<!}f2X;B%=3P<\n[^01^;BP3Q01fIPSPqO4!}c6@b@W@%qPeH07&06z=56DeP1PZ%M3RD,?^/0OX41PJPdP3E:Q08&0HR#;d!sJ$j`RR#z1GGDRD7bY#;X41P@!sQ%!sG$uR?bYD!s>%<!s>%N=0IP1PZAW`YD!xn0D!xn5D!xn//ACX41P!#I%%l?AWYW?!zA0?!sh1?L~!z=&,KIH05!tO%O2AoW?YB0JYW?ExPaP>E:PUPTE:PrB0K!}s$PtB04!s0$Q07B03!s1$O2bYbTW`WUWVb_WNWXWSWMWRWLWWX[1XZHW]WaW^o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tid_I : ltac2:(zQ "00T") := ltac2:(zQ "70!h9!klb!n5!hma!jr6!nha!nl9@2$5@1$2@1$0#k0\1t@1$2@1$0#k0@2$4@2$1Z@2$3@1$0#k0^1@2$1@2$3@1$0#k0^1$6").

Lemma one_tid_ok : ltac2:(zQ "61!h9!klb!hm0!hma!jr6!nl9&@2$3@1$0#k0@2$2@1$0#k0+1@2$4@2$1Z~0@2$1~0$5").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanRefNodes ()) ["WithSegs"] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__with71zp;1p;2p;3p;4p;6p;7g00[?j16Tg005Ej10Tg00TOj1:Tg02:Rj2@Tg01Gej23Tg00T4j24Tg02<5j2<Tg02<]j3;Tg00Wkj1DTg00=Zj1BTg01a[j1ATg01J9j1RTg01JWj1QTg01KBj28Tg005jj1>Tg02@Aj3=Tg01MWj2PTg008Dj2KTg01N9j2JTg00;jj3ITg01Nej3FTg01ODj4GTg00O:j2HTg00NPj2ETg01LHj4?Tg02AAj2LTg00S8j6CTg01HAj2MTg01d@j7NTg02Pdj7OTg01@CR0f0R1'3p=21M01p=1g00N2R2f1R3g01k1P1C?p=7P3g01g5R4g01gTR5P5g01h4R6P1g01hTFNp=5f2R7P4P5P5P6P3P1FOp=9P2g008^R5#6R4%21%05R5#6R8%:5#:#0R9#6R:'@R;,31'4X721<8:%28R<%1:%2;[[%18R=g01A>R>A;8:3UW0%1;\>^0=g01jER:#DR?%B:R:%A2R@%R2RA%Q2RB1820RC1824RD'7,5B1828RE%>95=2,7D,5B391PB6R6P1P7g01?CR9g01i4RF'K1J17=I9FdAF203CGR0b2b5b6%24134;'4P1b1b3b4%05#0#0#0#0R5#>R;1H;4'ERF%65R5,<8%151@85R9#2[\<A;853V>X0=%19\>^0=P?P:P@PAP2PCg01mgPDC?,5BA=2E;,7D,5B59BP6P0b2b5b6%141349'4P1b1b3b4,L4EC%2Fg03?V,3F'4eo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Lemma region_free_app : ltac2:(zQ "92!h9!n5!hp0!kqb!hp7!kp2!kp9!jq8!qf&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1>2lo@1$1@1$0#k0>1n@1$1@1$0#k0@3$8$7@3$3@3$6~0^4^3^2^1@2$5@3$3^4^2^1@3$3^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["FPX2"] "##-'p'0h02l2h12loh21nh31bi001bh42l1h52IHh61ah71lh81si011pp;1p;2p;3p;4p;6p;5g005Ej12Tg005jj1ATg006Hj1<Tg00=:R0j2:!s1$Zj1@Tg01]Aj34Tg01^;j30Tg01D3j21Tg00;jj33Tg00Wkj1;Tg008Dj25Tg00dPj37Tg03@_j46Tg03AXj19Tg03B6j3?Tg00S8j68!sS$0j4=!sA$Tj5>!sn$^#2!s$-A#<R1/:1R2#@R3P2g01?CR4f3R5f2R6542f1R7f0R830A0578A0678R9'133^21^11^03R:X43%;2?078/19,54X21X11X03P0P1P1f5R0f4R;572R<=426?078A0<!sU$534!sp+\:^73P8P4A0;78R</19R=P6P7f7f6R>C6#9R?/18A0067,1?A0567'1R?534X34P4P7P8P>P0!sP$@/1!sh$AA348?X34154A11@=A?@<9E8A42;!tY$P5P6P7P8O3E8P1P1!sh$==72;R;!t},;!t}'e!uU+X5:X43X81X31!sg$2n200110!s$$21100100X62P8D>W4o"). Qed.

(* [comment removed for export] *)
Lemma region_free_In : ltac2:(zQ "e1!h9!n5!hma!hp0!kme!jq2!jq8!hp7!jj6!jqf!qf!js2!kqb!no1&@2$3@1$1@1$0#k0@1$1@1$0#k0>1l@1$7~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>1b@1$1@1$0#k0>1s@1$1@1$0#k0>0@3$a$6@3$c^5^4^3$9>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^3^2^6@2$b@2$5@2$4@2$2@1$0#k0^6@2$2@1$0#k0^5@2$2@1$0#k0^4@2$5@2$4@2$2@1$0#k0^4@2$2@1$0#k0^3@2$2@1$0#k0^6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanRefNodes ()) ["FPX2"] "##5np'0h02Hdh11Hh23Hrfh31bi001bh41lh52loh61nh71sh83Hinh92b'h:1eh;2s'h<1Eh=2IHh>1ai011pp;1p;2p;3p;4p;6p;7p;5g005Ej1:Tg005jj1GTg006Hj1BTg00=:R0j2@!s1$Zj1FTg01^;j38Tg00d0j43Tg03C6j39Tg00NPj20Tg01C9j21Tg00Wkj1E!sS$Pj3;!sS$Mj6DTg01HAj25Tg00T4R1j2CTg00;jj34Tg02BEj6<Tg00S8j7=Tg03BTj5ATg01RlR2j2?Tg01?Cf0R3g01i434p=7f2R4f1R5'1/53p=61545/?3p=21553,?4p=>g008^#:!s$-GR6#BR7/@7R8#FR9P8f4R:f3R;;84#7P7P7P4P5C3R<f5R=598106=R>106:R?'1R@106;RA1064=6A>32RB[[^77^37^67^57RCX49%E8RD?8;4#7A98<Dg01@af6RD,06RE/1>RFA6?AE72?P3n010!s#%W8W2X77X37X67X57P0P7P7A;8D=!ss%f7R?=;8D998<P!tG2\C^49P3!u9$?PDC3=;8!s]&P7P7f8R;P?C3RB!sg'f9R<P;P?P=P:P5ED106<!uP$;RG,1ARH/5>52@A8?=:#7'CP1f:R1,06R:A6:AE52FA8;D=#7106?R?/1E15@?72>P311G?f<R?,06R>f;R@!uo$=6>G32A8@<;#7P2!te$>R2f=R>C3=48BA98B?11E:15HE72AP=!sJ$?R=P2C!uQ%<P;C3R;548P8P!v@&P7P3P3n20011!vk$120100100X:8!sh$@RAP=!sh&1P<C3P3E<A47=<!sl25!sl?AR0PA!sl&@P1C3P5!sl$0@fBRE=47?P7P>106A!vf$=R='1RH1063R:fCRB,06RG=6:A32fDRF=472106ERE1060R0;6ARI?>HE[]0X971062,1=!sg$>R6A66E=32A47B>P7P211A:=>IE11GE110ARA/5G720]0X;715H092A=P3W0PFP3P5F=W1W0PBP3PDF=W1P3O1b!s+&W<P3O1A98;>P>P?P@P1P<P4P3O6W8P3O1!v3$!zb%21!v9$!zm$2W0P5P3O2!sF-12!s/&b2!{53X=CX49X;7X97!s^-10!s$$!t#$100X>8P3DAW4o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma live_bytes_app : ltac2:(zQ "92!h9!n5!hp0!no7!hp7!kp9!qf!hld!kme&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanRefNodes ()) ["FPX2"] "p'0h02l2h12l1h24__x1h34__x2h44__x3h52IHh67__arithh74__ffh88__varmaph95__with:1ah;2a0h<1lh=1nh>1zi001bi011pp;1p;2p;3p;4p;7p;6p;5g005Ej13Tg005jj1LTg006Hj1ATg00=:R0j2=Tg00=Zj19Tg01]Aj34Tg03DYj11Tg01C9j20Tg00;jj32Tg00Wkj1:Tg008Dj27Tg00dPj38Tg00NPj2<Tg01I[j2;Tg01b9j4KTg01J9j1JTg01JWj1ITg01Kej26Tg00TOj1HTg02QHj35Tg01LHj4CTg01d@j7BTg01MWj2@Tg01N9j2DTg01Nej3ETg01ODj4?Tg00S8j6FTg00d0j4GTg03BTj5>Tg008^R1#3R2#3#3#3#3#3#LR3#AR4/=4R5#9R6P5g00N2R7f1R8f0R9545#1%18R:%19R;'032^06R<X16%:5#1/0;,77X06P0P4P4f3R0f2R=585R>=459#1%1>/0;527^06\<^<6P9P7%1=/0;f4R>,<3R3/09%10R?,03/0:527X>7g01jER@#:%9@P71;7=P81;70CK%J7%I7R@g01g5g01gTRAPAg01h4RAP71671RB1672R2%H1,67R1557557g01kXA57B2=571CCg01hTFB1@@AP9P=g01?CRAg01i4R@'71D9==2A@dg01@C=E78C?b7b8b9X27X37X47108=,091098/0=527^27^37^47P9P:P?P3O3b6A45=9#1P8P9O1EFP4P4P>P0CG=85=R==459#1%1=/0;527eX06X5<X16X=4X:4P8P9O2n2001101010121100100X;5P9D>W1o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX2.
(* [comment removed for export] *)
