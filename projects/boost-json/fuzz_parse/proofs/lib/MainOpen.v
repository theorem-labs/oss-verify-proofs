(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout StepTac
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux
  Spec RefNodes RefStartup RefStartupFacts RefMainEntry RefMainEntryN LibTail LibDiagKn RefPrintfFirst
  MainDefs MainWalk_defs MainSegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MainOpen () := KReplay.lz_vm "#%J-C4ELinuxProcessSemantics?!s<22Fs4pathI47Corelib5Lists7!s+#Def6Forall00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux7sregionC13~~~C!t1+4Init5Logic6eq_indC46Stdlib9micromega5Tauto5eKindI!sE;8GFormula00K!t,72eq01I!s@19Datatypes4list00!sF=prod00C!sF;3fstC8!v6N8SymExec23SX25s_log!v:&!v|V;log_covered!sl%I!uy;!uY>bool!v[4!sF31c!tnO8MainOpen4regA!ti&!vE\9sym_state00!src8sidecond!sqe7scripts!sp'!x0P=!v@#Walk_defs2r!vC&K!t\\4expr02!sm&!x;+7Numbers7BinNums8positive01!sKG2!y,<3nat!sE/!sj31Z02!uDc1!v3i3!smc6kentry05!sok6!sok7!soc5sadd!w0f!t_'8!sok4!{03!#7`71!z?@3!tUe1!tUH2I!t7d0!t7B!|~$!}jH3K!#>895Riscv5Instr5aluop!v^B!#8CY2cA!#5hc3kn!#9-&!#:q63and!#>/9!sA$1!#='\4s_pc!u6&!wS<sndI!vX?0!y#^s!y#0!#9L_C!sj%!#=R\F!tSfF!#7lh4!smc!#>9+!~3D!#A%#2!|VG;branch_!s~$5!|>[!w,'!#Fc&!#HP$4!s+#2In!#C[8or00!t>Y3s!t?,!#JBH5State6EACCES!s[SMFILE!s[SN!s[#!uo85False00C6!sxI3Sys2Fs4!up#=openat_errnos!tbTOMEM!s[Q<ENAMETOOLONG!t>UENTK!#Lg47EnvRing3Pol01!sG6=!sD#M!#M>'Psatz!{5#!sOI4!sOK6!sO6:Z!sL+;ZArith!zU$!tL86VarMap1t02I!sD?0I!t_C7!#Oj,!vM<5PE!#GI#K!#PYD!#Fu<6option!vlF!tb+1!t?F5!sJF8!#S%;8B!sJ&C!wW@=Z!sT$CheckerC!w9<4f!#T>8!sq-C!sq0_soundC5!sX&6!xg%6BinInt1Z2le!w]E!vDG4!sJF6!w_D3Op2!#Ui>unit!y_8!t9%4kind!#Ao-!sf81I!v^@!|&00!|VN1!uUI3!#C^=N02!wq<3oppC45stdpp9bitvector;defini!{_#s7bv_wrap!si=pow!sC=sub!sC<6modulo!sF<>pow_pos_nonneg!z->t!sB<:!sj#!sfB7compar!zsF7!sIE!zrG3!smE6!sIE5!sIE3!w_=mul!sC=ad!~<=:mod_unique!#DUO8PropExec=!yh&64_mod!#HH7!#>8$8!#a`$_r!z`BZ_to_bv!sLA;bv_unsigned!sPA@!sv&!sU-!#=^N9!#?S#_ret!#@]74True!#`,=:!zK%ison!#3/7!~[65!#If\U!#IfeU!#K;^2cU!#PJfU!#PJ&!xG?2bv00!x;K3Run:valid_argv!#P%;6length!#5;<of_nat!tEO?total!tE#_bytes!#FxQ5Namei>path_has_slash!#m4M8!s`$eqb!#Ke7tl!}b89!#Ht#!#lG$!sE67f_equal!#TUO3Lib2Nd:and_elimF5!#33=3not!vGX;dotdot_!ul#K!}h=1!u1a4!#X'7!#E>4!#q+P7CatExec<cat!ze$_ptr!vC3!#r=03nth!v_23Nat!#8A#!tk;3app!#GHC1!{IO@!#XB#_stack_fits!#o/9x!v/R3Amb5a_uid!#3\U!sc#7a_hwcap!se&!~424Znat5Nat2Z9i!#?~'!u12Peano2lt!#7c5!#LR+1!#H>5;ZifyClasses;rew_iff_rev!u;P:MuslStrlen=!y$'_room!#UXP;S!wa#LayoutAbuild!ws&!#4@$!#>7WM!sn4_within_span!tnQ!y[4!si$!teX8wrap_me!v@R6BvBase;nat_to_wor!#?>A6bv_!|t#!~?PStepTac<!t,#!sd#!#9B#!{AU!uc+9u64_range!{HD7inj!zA#!#7w8!zZ#sym!{,B5mkrel!sKB7!{R&!#6`O=!#`y&Sound4SX2S7u_small!#E%>!|a%f!taC3inj!},QRefStartupDmain_!zZ%rdn_abov!w4&K!#5<:!#9Ta2!#9T7!#48&e!#6CQ!#3I,B!#3I#!z;$readabl!yN'!t~V9ex!t}%1!{$V<RefMainE!vv#8!w%$s!#;2'!{qX3rdn!w]'!#7P=3!{IEapp!sKB6!sK$2!tw/!tp96images5Plain1M?loaded_segments!#?+A!#s;#0!~2>6!~2#!#S54!sH4e!txT5phdrs!#6AP!#db%sp_window_lo!sa\hi!wI68!wI#Inst7Inj_Z_Z!t,;!#lQ$7Prelude5bvmap!ylP6SymRun7vals_ev!u~%!#kuYENV!|sV!#5g6regs_ok!stjknow!st,!uRO5Frame9f!s+#!#UK+!v=Y6!sl$A!~X_7seg_r!#AI'!sjX4mkst!#3E&!#@BL6config01I!tDPShapeAlg8realize!$3KX!#6B/<!#6B#!y81!ss\2E!t^j!yz]!ss05!}>#!tad2p!sif!#;3c5auxvp!slc3rn!#M&V8SymDrive9junk_!vu#!slV>!#AT,efs8canary_w!sqV9!t_'X@!t`+_!#Yz%!st%!#W\5:!sG%_app!$#6\!$?=,!xB'!$$&]ym_exec!#3H&!#=g9!$D~$!$-\]5carry!t}V!#8O58sc_denot!u'3!$Iw8!u+^6s!#4G#!u,i9mem!u-/!u}dlog_fla!suj4!sqZ!vO1a_base!smc5a_off!}LV!$K#%<!$N|$s!v=/!smVA!$Kn,_!#>,#!sr]6r!xi/!#3pX:!uE#_intro!#3j&!#Du>3Sem5alu64!x?^e!u,/!#`Z:map!#GWJ>!ti$!sE+@!#O:#to_le!#ZqV!v9'5krea!#9N`!sh$_!#NJ'!{j_!xX[>RefPrintfFirst9rz_run_l!{p&!$=2\!$GT%!$PIc!$:p$!#?s&!#N{<8inj_succ!uuP!#p\05FUELM!vdV!sm16STOPS!sne4scr!#IcV!#A3/7sr_main!sndkn!sn[!#I9'4TSet!v5d3s!v4'!#M\YregA!#B_W4Scfg=hunspell_scfg!tW`cA_!$I2'!#zgYcov!$X^&!#xOC1!w|Q!#OU'ge!#\\'!#x9:5ld!#cLR!#A+1r_ge!#;~ZRun7reg_va!#d/'!v&?5bv_eqC5!#v0L4Uapi8AT_FDCWD!$B,VBopen_igno!#=o#lags!$M+=N!#c=Q!#Vc$7outsid!#>pV7StoreOk!#D_#grows!zT_!#|5$len!sk_:!sk$nonul!uGV!v0%6in_rng!|/'!#^c3!$3d27!t2P!#A\+9!#ic#gre!#mq25!|5$8!#h\#Na!#ye+!#n9Aadd!vS_fact!#bnW8m_halt!$1nSm_vm_lazy!}/A4BvWf!#AbX;!#ZL#set_a!#>J&!#?9\ridx!skc6sr_up!#D-W!#6W&6reg!siY!#?V1!#RG#!#?VV!{$,>!#HC$!#vf#li!#NSV!#qP33!v:W!t_'6!#E_$!v:d3s!$Zx&!sk^5noscr!smd4srC!#G6&!|nP5Model!$WjZ8rC!~p0!skO!#D1/6blob!#b9W!xE+8!si$!#m<'!#>$V:sr_vars_l!#R8`<env_app!#Ye,!#^_\3env01!uK^kn!uKqkno!#bA`=!#r,%!vA%!sq&!#:u=7add_0_r!t=gl!#4,U!#^<6!$mF$!#jr'!|MY?!$Ek'!$+k/!xSV<k!sg$!#YD-!#b#B2!uzdscs!#a8/!#Z]Dlow32!#[,H!sNC!#yL&4sext!syE<!$gH%taken!$-C75proj2!sA=1!#7E_crF!#83fF!$nNd4kn!sl'!#RC\F!#RC&!#9-ZF!#9--!#QW\!vse3s!w`'!#|#^!$ME&!$--@9and_morph!sOCnot!sO&!uPP!#<A-N=!#z%-N!vGW!su02E!sje=!#z+-!sue8evN_argc!#7{U!#<R/2!#>tW7ArgvEnv5!tQ#!uDe!#|L#!v3jjun!#:8_4ENV!{:+!#7,F6!#XG#b!$Ks;4neg!$bR<3!$R6-4Bool!s'$=!s[#_true!$?o#!$a`;eqb_neq!x'X7u_!x,\!#3O2!$Y'd4sc!slY!xq1!#eo%!ycf!#eq%N!#5y_regU!#9#&!$}eS2!#d0ZU_!$\p'!#9W\!#8#2!$%5,=!#B#$_f!s,$!sH76nth_In!wF^9!$B1&!wG&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~he7sregion37Corelib7Numbers7BinNumsm11Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ne5saddr04prod04cons03nil04pairne4EVarne2SA03fstne8sidecondne9sym_state04bool04true37Corelib4Init5Logichh02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainOpen4FPX1~~~~~~hia4regA69OSSVerify6Proofsaboost_jsonafuzz_parse3libdMainWalk_defs~~~~~~hn22rAheblog_coveredne5s_logne7scriptsne6kentryhia2cAhn23knAhn22rChh03andne6sentry03sndne4s_pcne4ELithia4regFhn22rF05false3h5LinuxProcessSemantics5Riscv5Instriic7ALU_ADDiic6BC_LTUhia2cFne5EAluwne4SCBrm14Npos3h5LinuxProcessSemantics5Riscv3Semio15low3235stdpp9bitvectorbdefinitionsiqc7Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSem5Stateit49errno_ret3h5LinuxProcessSemantics5Riscv7Preludejgf4sextio15alu32io1cbranch_taken5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openjl6dopenat_errnoshia3scF36Stdlib5Lists4Listjq22Init4cENAMETOOLONGit46ENOENT46Stdlib6ZArith6BinInt1Zjt52lejt53powjt53subiqcbbv_unsignedhia4regUhn22rUhia2cUhn23knUiqc2bvhh03not3h5LinuxProcessSemanticsfLinuxProcessSem3Runkj8avalid_argv06lengthjt56of_natne3env69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMainEntry~~~~~~koa6blobs069OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~kt38blobs_evne3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~li07vals_ev06option04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsln2h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lre3rdn69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~mg0floaded_segments03nathh02ex37Corelib4Init5Peanoml42ltjt53addjt53muljgf5bvmaphh01Ilre4getriqc2BViqc4BvWfkj85mkCfglre4mkstlre7seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~mrcdhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ng48realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~nkbccat_argv_ptr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~np59frame_mod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainOpen5Usage~~~~~~nta6frameUnta6regU_wng44TSet37Corelib5Lists7ListDefoj73nth03app37Corelib4Init3Natola3addkj8h0entry_stack_fits3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutoo89EntryDrawkj8avalid_envpkj88valid_spjt52lt69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~ou9amain_entryit45Model04Noneit48m_haltedit49m_vm_lazy" s.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition regA : ltac2:(zQ "20!h8!l7@1$0$1") := ltac2:(zQ "80!na!rd!s5!sb!t1!t6!tc!u3@3$3@2$2$1$0@4$5$1$0@2$7@1$6N0-u0+r0@1$4@2$2$1$0").
Lemma covA : ltac2:(zQ "d0!u8!h8!ud!v8!hg4!s5!hga!hi4!hma!hr2!hr8!hs6!hse@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##%Np;2p;1p;3p10000p4p70!s1$`p4p710p8p1001A!s?+2C!s?/2_!s4$1p1003>p4p73101p8g003bj26Tg004<j15!s/$\j21Tg005<j30!s/$Yj14Tg006_j22Tg007ej33Tg008?R0g008_R1'6g009?g00:@R2g00;L#5R31123g00<Wg00=a3030#4'2=301do"). Qed.
Definition cA := Eval vm_compute in carryM rA kn_main.
Lemma cA_knA : ltac2:(zQ "90!h8!ht8!u8!ud!hg4!s5!hi4!hu1!hu7@3$6@1$0$1@3$2@1$0$1@1$0$3@3$2@2$5@1$0$1@1$0$3@1$0$4$7$8").
Proof.
vm_compute. reflexivity. Qed.
Lemma rC_facts : ltac2:(zQ "f1!h8!ud!v8!u8!s5!hi4!hue!hse!t1!hv4!hvb!ig4!na!hs6!ig9&@3$3$2@1$0$1@3$3@2$4$2@1$0$1$7$6@2$9@3$5$c@1$e~0+tsnlc@2$9@3$5@1$0$1@3$b$2@1$0$1@3$3@2$4$2@1$0$1$7$6@1$8$1@3$5@1$0$a@1$d~0@1$8$a").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##&\p;1p;3p;2p;4g00?lj10Tg00@Qj11Tg00AUj1<Tg007ej32Tg004<j18Tg00K6j17Tg00S8j24Tg003bj23!s8$Sj46!sS$\j2;Tg005<j35!sA$nj19Tg00U3j3:!sA$Yj1=!s8$PR0g00OE#0#1#0!s$$1!s$$!s2'!s>1<R1;21g00;LR2#8R3%72R2;22R4g00UnR5#8R6%75R5;25R7'41301P4P713321365C6C6g00:@R71;73g00<Wg00W735R4753R8#9=201A:734=232%=8=265'4'4do"). Qed.
(* [comment removed for export] *)
Definition regF : ltac2:(zQ "20!h8!l7@1$0$1") := ltac2:(zQ "90!na!rd!s5!sb!t6!u3!t1!ih0!tc@3$3@2$2$1$0@4$4$1$0@2$5@1$8N0-v0+h0@3$3@2$2$1$0@4$4$1$0@2$5@1$7Z+hgrmh4+4@1$6@2$2$1$0").
Lemma covF : ltac2:(zQ "d0!u8!h8!ud!v8!hg4!s5!hga!hi4!ih7!ihf!hr8!hs6!hse@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1p;3g003bj26Tg004<j15Tg004\j21Tg005<j30Tg005Yj14Tg006_j22Tg007ej33Tg008?R0g008_R1'6g00X;g00:@R2g00;L#5R31123g00<Wg00Y<3030#4'2=301do"). Qed.
Definition cF := Eval vm_compute in carryM rF knF0.
(* [comment removed for export] *)
Lemma rF_facts : ltac2:(zQ "h80!h8!ud!u8!v8!s5!hi4!t1!ig4!hv4!ihf!ih0!ht8!hse!hg4!sb!ii5!na!il0!ilb!im5!imb!tc!in3!ig9@2$8@3$5$h0@1$h7@3$2$3@1$0$1@3$2@2$4$3@1$0$1$c$9+knmm0@2$8@3$5@1$0$1@3$7$3@1$0$1@3$2@2$4$3@1$0$1$c$9@3$e$1@4$h6$f$h2@3$h4$h1@1$h5Ni8@1$aZ@1$a+vvvvvvvvvvvvvgg1@1$6$1@3$5@1$0$1@3$7@1$0$b@1$0$1@3$2@2$4@1$0$b@1$0$1@1$0$d$h3@1$6$1").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##+dp;1p;3p;4p;2g00@Qj15Tg00?lj10Tg00AUj1@Tg007ej33Tg004<j19Tg00>ej1CTg00B3j1=Tg00Z@j3BTg00[Gj4ATg00K6j1FTg00M=j3ETg00S8j2;Tg003bj2:!s8$Sj4?!t$$\j2<Tg005<j38!sA$nj1DTg00U3j3>!t^$6j12Tf0R0#5#5p=1%00#0p=7%20#2!s$/p=6!sB$!s$/p=4g00UPR0g00OER1#5#1#0#7#5#7#1!s-$1#1#@R2;32g00;LR3#9R4g00\Rg00]2g00Ojg00Nf#6!s$+Cg00PV#=3B%01#7#4!s$-!sx%!s$%0#@#=CA%F3R15E3R3;33R5A3411R6';1:02P5P61:431:41C?C?g00:@R61<64g00<Wg00Y<38R5784#D=302A>645=343g00M]#9R31<34g008?#9g00]d387>4=341';';do"). Qed.

(* [comment removed for export] *)
Definition scF : ltac2:(zQ "10!na>1e$0P") := ltac2:(zQ "d0!ina!iq3!is9!hg4!ii5!hi4!na!jg2!il0!ilb!jj5!jjd!jk6\1e$6@3$5$3@3$c$9@3$a@1$0#i0@1$0#k0@3$b$8@1$1@1$7^1@1$1@2$2@1$0#k0Z@2$2@1$0#k0+vvvvvvvvvvvvvgg1$4").
Lemma scF_openat : ltac2:(zQ "40!na!joa!jpb!jr5>1e$0>0@3$3$0^1$1@1$2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##,=h01Hh11eh22Hep;3p;2p;1p;6g00^cj39Tg007ej35Tg00_:R0j22!s1$Tj10Tg003bj28Tg002Cj66Tg00UPR1g00`TR2f0R335p=7g00aIR4=513p=3g00b>R5!s4%1g00c3R6,23p=4g00cP9913P0g00dRR7f1R8551%78%38%18#4'2'2f2R8#0P3A5178P1P7%03X11R9g008?g00\R'8R:%07df3R7P3E6W0P3O!sn3P0%77%37%17#4'2f4R7#0P3%77P1P2P9P:%02df5R2!si-!sU+P0%32%12#4f6R2!s_$32P1P4!s_%4df7R4!s_-12#4P0%14P6f8R4!sW$14P1P5!sW%5df9!sU,P6f:#0P3n010!s#%X06P3O1n20!s9'2!s-$!s'$!s[%!sBr2X11o"). Qed.
Lemma scF_ENAMETOOLONG : ltac2:(zQ "20!jrb!jpb@1$1$0").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1g003bj21Tg00_Tj10Tg008?g00\R'1g00eG#0do"). Qed.
Lemma scF_ENOENT : ltac2:(zQ "20!jsb!jpb@1$1$0").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1g003bj21Tg00_Tj10Tg008?g00\R'1g00fB#0do"). Qed.
Lemma openat_errnos_range : ltac2:(zQ "50!na!jud!hv4!joa!jr5>1e$0>0@3$4$0^1$3@2$2@2$1+1^2@2$1^2+vvf").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##0yh04__x1h12Heh27__arithh34__ffh48__varmaph55__with61ep;3p;1p;2p;5p;4p;7p;8g00^cj3WTg00KVj1VTg00g7j2GTg00A6j1A!s8$Xj2=Tg00hAj3P!s/$jj3LTg00iSj2F!se$6j1CTg00M=j37Tg004<j1@Tg00j?j2?!s/$]j1>Tg00k;j1UTg00?lj15Tg00@Qj16!tC$Uj12!sJ$fj2OTg00lIj5E!s/$mj1DTg00mOj4;Tg00n:j7H!s/$^j8ITg00oBj2BTg003bj2J!s8$dj2KTg007ej34Tg010Pj3M!s/$oj4NTg00_:j2:Tg011aj2<Tg00S8j2QTg012=j2R!s/$`j7STg013Dj7TTg00UPR0f0R1'Rp=3P0f1R2g013hP1C;p=9P2g002_R3g014OR4P4g014oR5P1g015OFSp=0%51#5p=1f2R6P3P4P4P5P2P1FTp=8g00cP9W0!sV$oR7g00OER8#V,G0g00NfR9#A,=05P01=095L0g016['FR9%C79779!s&'37%@71?02%>0%U0R7!t:'%58R9#6R:#6R;#2R<#31O08R='9,07%5:#2R:#3/9=,07%6;#2R;!s5,8#5#1#2R>!s9'P!t#+DE587!s%+%D4!sA,P0%28R8#3g017GR4P=C;,07P0P=P4%19#1!s$&2R9#3!sB$FHGI1B75P1P6g008?!v'$8_R5'J1K16=475dg00PV=M02CNb3b4b5X00A40<1A40:1A40;1A40>1g00c3':!s$%1<821<29'Q[^00P1P6P2O2b2W1X60o"). Qed.
Lemma errno_ret_range : ltac2:(zQ "80!jud!hv4!ina!na!jg2!jv3!jva!kg1>1e$3>0@2$1@2$0+1^1@2$0^1+vvf@2$0@2$6@2$5+2+k0+vvf@2$7@1$2#k0@1$4^2").
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##70h06__sat1h14__x1h24__p1h37__arithh44__ffh5!sN%0h68__varmaph75__with82Hah91Hh:2Heh;1eh<1zp;1p;2p;3p;4p;6p;7p;8g00AUj19Tg011aj20Tg00?lj1;Tg00S8j27Tg00@Qj11Tg017nj1UTg018Lj1=!s/$ij2LTg019Oj2K!s/$lj25Tg01:Ij2@Tg00KVj1E!s8$ij2hTg01;Qj28!s/$mj3]Tg01<Qj2YTg003bj2D!s\$6j1VTg004<j1TTg00j?j2Q!s/$]j1OTg00k;j1NTg012=j23!s8$fj2MTg00lmj1JTg01=2j3I!s/$Uj3?Tg00mOj4:Tg01>8j6HTg013Dj7GTg00oBj2F!s/$dj2PTg007ej3>Tg010Pj3R!s/$oj4STg00_:j2g!sn$\j2fTg01??j3e!s/$bj3`Tg01@Ej2_!s/$bj2^Tg01A?j6\Tg002Cj6Z!s8$cj1[Tg01Bmj6CTg01CKj2XTg01D1j2B!s/$[j2WTg01EJj1a!ui$`j7bTg00n:j7c!s/$^j8dTf0R0#;#;p=4g00UPR1f1R2g017GP0C:p=6P2g002_R3g014OR4P4g014oR5P0g015OFbp=2f2R6P3P4P4P5P2P0Fcp=<f3R7!s;+6P2P0Gdp=Ag00OER8#9R9/00%;8#4!s$+9R:,00R;'7R<P1%18R=#1!s$'R>#UR?%=2R@'LRA%9=R=%9>R>'KRB/5:RC/00X<1RDP11@@BREPDP@PB%E8RF15B2RG1h=>RHg00PVRI/8=RJ10I>18IB[RK[RL10I=RMg01FBRNA]=>2UW8R>10IB\N^8MRMP2g01F^1YI='DPJeO1RJPKp-0RNg015oRO#VRP%TORO1Q12RQ%O1RR%N1RS13191M18R8'6,2S131:R:,68,2SRT5<S%J4RUPS!vQ'131I131==I1?R==?18RV!s_$P1PVg01GDP=C:,2S5<S!s\,P7EHR7FGCA1FS5R5P0P6g008?R4g008_R3'D1P06=>43dAR1I2CSR3b4b6b7X11W210IG18GB'7/g6\<^11^2NP0f5R<,5BR4,8B104I'7P<f4O3b3b0b5b0PHPLP>PMPJPKPPPOPQPRP11f18g013h131F9e1==`1V!u'$P5P!tD,%=01_BF15B0'^5>1^11P0P<O1!t+'E\A>1GEP115B6PD!t;8SA<S7TPUA?1=:/6V,2SCA!t50X2N172;10CG[!uN+6RN,09PNP<!uC,%=6/@BP0EZb9PA%[@EC1X?@,B?1W?@EC%a2,B?,0CeW:X;1o"). Qed.
(* [comment removed for export] *)
Definition regU : ltac2:(zQ "20!h8!l7@1$0$1") := ltac2:(zQ "80!na!rd!s5!sb!t1!t6!tc!u3@3$3@2$2$1$0@4$5$1$0@2$7@1$6N0-o0+l0@1$4@2$2$1$0").
Lemma covU : ltac2:(zQ "d0!u8!h8!ud!v8!hg4!s5!hga!hi4!kh0!kh8!hr8!hs6!hse@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1p;3g003bj26Tg004<j15Tg004\j21Tg005<j30Tg005Yj14Tg006_j22Tg007ej33Tg008?R0g008_R1'6g01Gkg00:@R2g00;L#5R31123g00<Wg01Hl3030#4'2=301do"). Qed.
Definition cU := Eval vm_compute in carryM rU kn_mainN.
Lemma cU_knU : ltac2:(zQ "90!h8!ht8!u8!ud!hg4!s5!hi4!khe!ki4@3$6@1$0$1@3$2@1$0$1@1$0$3@3$2@2$5@1$0$1@1$0$3@1$0$4$7$8").
Proof.
vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma path_nonul : ltac2:(zQ "90!ina!kib!h8!sb!t1!kj1!km4!jr5!is9>3a0s@1$2@1$1@1$0#8>4path@1$2@1$1@1$0#8>0@1$6@3$3@1$2@1$1@1$0#8^2@3$3@1$2@1$1@1$0#8^1@1$4@1$2@1$1@1$0#8@1$5@3$7@1$1@1$0#8@2$8@1$0#8Z^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##:Sp'0h01Hh12H0h21li001lh32H1h42Hlh52Hxh61ah71eh82H2h92_Hh:1xi011xh;2Hnh<3Hvah=3_H0h>3_H1h?3a0sh@4pathp;1p;2p;3p;6p;8g00@Qj18Tg017nj1JTg01L4j1GTg004<R0j1ETg00K6j1O!sC$Wj1ITg00AUj1;Tg01MNj2C!s/$nj1ATg011aj27Tg00S8j2<Tg01NNj1DTg000`R1j34Tg01CKj2NTg01OJj1MTg007ej30Tg01PNj2LTg01QBj2@Tg002Cj6?!s8$Yj2>Tg00M=j31Tg01R8j69Tg01Bmj6:Tg003bj2=!sA$Uj8HTg00?lj1BTg00^cj3KTg01SZj1FTf0R2#8#8p=5f4R3f3R4f2R5f1R6;1231p=3%B2#Bp=6AK562#Fp=2g00OER7#8#5R8#JR9#GR:#ER;P;P6P;P2%O;R<D3#I%;7P;P5!s>$<D3R=,C;#AR>'7%88#5#5!sh$;,7>'<R>%D=!s=+!s$$;R8'71C:2#A%67#6!s$0;'7X6;R7=4;=g00PV,N9R9=2:2X6;R?!s=&00R@g008?RA%M2g00\RRB30g01T3,L2=0AB'<X6@RB1@;=34A2:96R=P;P4!u0$<D3#D/78P;P3!s;$<D394;7P;f5R7!s<$!s8%?P;f6R8P;P7P<D3,@;94@BP1P;P?%E;RBP;f9R@P;f8RA!v'$C706A2:9@RD[P6P;f7REP;P8!sC$F90B<P;PAP;PE!s8$G!s8$BP<P0P;p-0P2g01FBg00c3RHn1011000002!s%$!s#$X7BRIg01U4RJPCP2E?PH1>D2b1W0P2O1W0A4;?6RDA1;45RCP;f?RKP;f>P<D350BA1;34RLP;f@RMP;PK!s>&PBPBP0P;PBP2P7P2!tL21001!tL%KA1;73RNfAROA1;M<RM51;P2E9A0B3MPBP;!sn$;P2PEP6!sn<0A1;87R7P;fB!tX$OP<D3P6E9A0;8MfC90;EP2fDRM90;AP;fE!t?$O<90B@ROf;94;?RPfHRQ92:9RR]4^5=[X2;!te$90BAP2POPBfF=1;<fIRO92:9^4D^5RX2BfGRR92:9A1;R<!x]$!xH$fJR1=1;<RR90B6fK!t&$M[P2A1;Q<RQ90B<!tU$RO!x,+IPJPR!wS'M!wS-fP=1;<90BCfQ!s0&L!w0$KPNfR=1;<!vW'<!vW&7fSR7!s?$!v$&7fT!v$&U!u~&VA0B@<REfZ!uF$1P^0!um%0BA<!w<$BP<fY92:9f[!sI%D]0X2BfX!uf$4;?<P6W8W3f:R?P2E:b8W1P@!s0$!u1&b!s+&W3P2P5P6O3W3X1DX0=X2BX:;P4P5P6P2O4n2002!xP%!xS%41!xa+000A0B2OA2:91[X2BPQO1P21=BO!t'$4W5P!tO%3!tO41!s+%W0!tO+0W4X5!tND1!tN5GA2:9A!tN$F!tN&G!tN$9W;W>W=X9>P2GHW<X@;W?o"). Qed.
Lemma path_len : ltac2:(zQ "90!ina!kib!h8!sb!kn2!t1!km4!jud!kna>3a0s@1$2@1$1@1$0#8>4path@1$2@1$1@1$0#8>0@1$6@3$3@1$2@1$1@1$0#8^2@3$3@1$2@1$1@1$0#8^1@1$5@1$2@1$1@1$0#8@2$7@1$8@2$4@1$1@1$0#8^2+hvvvf").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##:Op'0h01Hh12H0h21li001lh32H1h43Hl'h52Hxh61ah71eh82H2h92_Hh:1xi011xh;2Hlh<3Hvah=3_H0h>3a0sh?4pathp;1p;2p;3p;6p;7g00@Qj17Tg017nj1ITg01L4j1FTg004<R0j1ETg00K6j1P!sC$Wj1HTg00AUj1:Tg011aj28Tg00S8j29Tg01NNj1=Tg000`R1j34Tg01CKj2OTg00^cj3NTg01SZj1MTg01OJj1LTg007ej30Tg01PNj2KTg01QBj2ATg002Cj6@!s8$Yj2>Tg00M=j31Tg01R8j6;Tg01Bmj6<Tg003bj2BTg01UPj7JTg01MNj2C!s/$nj1?Tg00?lj1DTf0R2#7#7p=5f4R3f3R4f2R5f1R6;1231p=31C62#?p=G%D2#Dp=61C56#?/82p=2g00OER7#7#5R8#IR9#FR:#ER;P;P6P;P2%P;R<D3#H%:7P;P5!s>$<D3R=,G;R>'8%78#5#5!sf$:,8>'9R>%==!s=+!s$$:R8'8%67#6!s$0:R792:2X6;R?=4;=g00PV,O9=N:2#MX6;R9!s=&00R@g008?RA%L2g00\RRB30g01T3,K2=0AB'9X6@RB1A;=34'9A2:67R=P;P4!u-$<D3#=/88P;P3!s;$<D394;?P;f5R!s<%<D3RA94;91A;A94@B'9P1P;P?%E;RBP;f8R@P;f7RA!sQ$9706A2:@7RC[P6P;f6RDP;P8!sC$E90B<P;PAP;PD!s8$F!s8$BP<P0P;p-0P2g01FBg00c3RGn1011000002!s%$!s#$X7BRHg01U4RIP9P2E@PG1>C2b1W0P2O1W0A4;?6RCA1;45R9P;f>RJP;f=P<D350BA1;34RKP;f?RLP;PJ!s>&PBPBP0P;PBP2P8P2!tL21001!tL%JA1;83RMf@RNA1;L<RL51;P2E;A0B3LPBP;!sn$;P2PAP6!sn<0A1;D8R8P;fA!tX$NP<D3P6E;A0;DLfB90;AP2fCRL90;@P;fDRNf9ROA1;N<50BRNf;94;?RPfGRQ=2:7RR]4^5=[X2;!th$90B@P2PNPBfE=1;<fHRN=2:7^4C^5RX2BfFRR=2:7A1;R<!xi$!xK$fIR1=1;<RR90B6fJ!t&$L[P2A1;Q<RQ90B<!tT$RN!x0+HPIPR!wV'L!wV-fO=1;<90B9fP!s0&K!w3$JPMfQ=1;<!vZ'<!vZ&8fRR8!s?$!v'&8fS!v'&T!v%&UA0BO<R8fY!uF$1P^0!um%0B@<!x/$BP<fX=2:7fZ!sI%C]0X2BfW!uf$4;?<P6W8W3f:R?P2E<b8W1PO!s0$!u1&b!s+&W3P2P5P6O3W3X1CX0=X2BX:;P4P5P6P2O4n2002!xS%!xV%41!xd+000A0B2NA2:17[X2BPQO1P21BBN!t'$4W5P!tO%3!tO41!s+%W0!tO+0W4X5!tND1!tN5FA2:A!tN%E!tN&F!tN$9W;W=X9>P2FJW<X?;W>o"). Qed.
End FPX1.

Section Open.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!h8!ina!kib@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!orc$0").
  Variable tid : word.
  Variable regs0 : ltac2:(zQ "30!ina!mnc!kib@2$1@1$0#5@1$2@1$0#k0").
  Variable mem0 : ltac2:(zQ "30!ina!kib!lm4>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
  Hypothesis Hva : ltac2:(zQ "60!h8!ina!kib!sb!t1!km4@1$5@3$3@1$0@1$2@1$1#8?3a0s@3$3@1$0@1$2@1$1#8?4path@1$4@1$0@1$2@1$1#8").
  Hypothesis Hve : ltac2:(zQ "10!os9@1$0?4envv").
  Hypothesis Hvsp : ltac2:(zQ "10!ot7@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!ina!ou3!kg1!hv4!jv3@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  (* LPS #38: [main_entry] is over the ProcInput, and the encoded form above held the
     pre-revision argument list.  Measured, not guessed -- a farm round
     printed the callee's whole expected type and the eight terms it was given:
       @main_entry : Amb -> ProcInput -> word -> word -> word -> EntryDraw -> word
                     -> bvmap 5 word -> (word -> option byte) -> Prop
       given        AMB sp0 [a0s; path] envv rdraw tid regs0 mem0
       "The 2nd term has type word which should be a subtype of ProcInput"
     so the argv/envp pair moved INTO the ProcInput and [mbase] and the binary entry
     joined ahead of [sp0].  A KReplay/CDef blob is never re-encoded, so the statement is
     written out (rule 11), with the SAME ProcInput this section already builds one line
     below at [model0].
     DONOR, in this unit and already landed: MainDefs.v:258
       NEW  @main_entry (amb_of inp) inp mbase (Z_to_bv 64 291460) sp0 rnd tid regs mem
     291460 = 0x47284, the PLAIN binary's entry (U/MainDefs.v carries 290456 = 0x46e98 for the
     ubsan twin, which is why this constant is not shared). *)
  Hypothesis ME : @main_entry AMB (mkProcInputC [a0s; path] envv fs0 stdin0) mbase
                    (Z_to_bv 64 291460) sp0 rdraw tid regs0 mem0.
  (* LPS 727298f3 port: the launch facts the argv-string bound needs ([path_facts]'s fourth
     conjunct, read off [RefMainEntryN.str_fits_N]); both are the run's own launch clauses,
     as RefMainEntry's [KnowProofs] section takes them. *)
  Hypothesis Hvl : valid_launch (mkProcInputC [a0s; path] envv fs0 stdin0).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) (mkProcInputC [a0s; path] envv fs0 stdin0).

  Let model0 : Model := MainDefs.model0 tid brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0).
  Definition ENV : ltac2:(zQ "40!h8!ina!ko4!kib>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!ina!ks9!lge!lha!ll9!kib\4vals@1$0@1$6@1$1#k0@2$4@1$5^1@1$3@2$2?3a0s?4path").
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  (* LPS #38: [p1] is over the ProcInput and the drawn entry (RefMainEntry.v:118-119); the
     input is the one [ME] and [model0] name.  Shape donor, statement only: the 75d69e00
     port of boost-beast/http_request (its lib/MainOpen.v, the same [Let pp]). *)
  Let pp : word := p1 (mkProcInputC [a0s; path] envv fs0 stdin0) a0s path envv rdraw.


  Definition regA_w : ltac2:(zQ "50!h8!s5!ina!na!kib@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ina!na!kib!s5!sb!t1!t6!jva!is9!kg1@3$4@2$3@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$8@1$0#k0@2$7@2$9@1$0#k0?3sp0+u0+r0@1$5@2$3@1$2@1$0#k0$1").

  (* [comment removed for export] *)
  Definition frameA : ltac2:(zQ "30!ina!kib!lm4>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "h30!ina!kib!h8!lm4!is9!lmc!hi4!lq9!lv9!mj6!jva!kg1!mk9!hv4!mke!mm8!mme!mn5!kna\1M>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$d@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$4@1$0#k0+tqgsc>1i$c>0@2$f^1N8@2$e@1$1@1$0#k0\1w@1$1@1$0#k0@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$h0@2$a@2$b@1$0#k0?3sp0+n8@2$h1+8@1$h2^3N8@2$5@1$2@1$1@1$0#8@2$7N8^1").

  (* [comment removed for export] *)
  (* LPS 727298f3 port: written out (rule 11g).  The replay used
     [PropExec.build_stack_bytes_within_span], which the revision deletes as false of the
     kernel's block.  The first, second, third and fifth conjuncts are
     [RefMainEntryN.main_strN] at argv [a0s; path], k = 1; the fourth is
     [RefMainEntryN.str_fits_N], whose margin is 8: the old [+ 17] is false at the revision
     (str_fits_N's note: at the top of the window the last argv NUL can sit 9 bytes below
     2^47), and every consumer of this conjunct needs only [+ 8]. *)
  Lemma path_facts :
    rdn RSEGS mem0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned pp)%Z
    /\ (bv_unsigned pp <= bv_unsigned sp0 + 2107576)%Z
    /\ (entry_stack_fits sp0 [a0s; path] envv -> (bv_unsigned pp + Z.of_nat (length path) + 8 <= 0x800000000000)%Z)
    /\ exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned pp + Z.of_nat (length path))) 8 = Some t8.
Proof using All.
    pose proof (main_strN (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 291460) sp0
                  [a0s; path] envv rdraw tid regs0 mem0) as MS.
    repeat lazymatch type of MS with
           | forall _ : word, _ => specialize (MS brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hvl | exact Hlau | reflexivity ];
               specialize (MS h); clear h
           end.
    pose proof (str_fits_N (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 291460) sp0
                  [a0s; path] envv rdraw) as SF.
    repeat lazymatch type of SF with
           | forall _ : word, _ => specialize (SF brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hvl | exact Hlau | reflexivity ];
               specialize (SF h); clear h
           end.
    destruct (MS 1%nat ltac:(cbn; lia)) as (Sr & Slo & Shi & _ & St8).
    specialize (SF 1%nat ltac:(cbn; lia)).
    cbn [nth] in Sr, Slo, Shi, St8, SF.
    unfold p1 in pp. subst pp.
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|].
    split; [intros _; exact SF | exact St8].
  Qed.

  (* [comment removed for export] *)
(* LPS 727298f3 port: written out (rule 11g).  The replay applied [main_regs_ok] and
   [main_know_ok] with their pre-revision argument lists; RefMainEntry's sections now take the
   ProcInput, the binary entry and the launch facts.  Text of boost-beast/http_request's
   lib/MainOpen.v [seg_A], with this image's addresses and the two lemmas applied over
   their current sections. *)
  Lemma seg_A : forall T,
    (forall vals R M,
       length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp -> vals_ev vals 5 = tid ->
       regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
       frame_mod mem0 M regA_w -> frameA M ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xebe88) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x473d0) mem0 (seg_rom RSEGS)) model0) T.
Proof using All.
    intros T HA. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 291460) sp0
                  a0s path envv rdraw tid regs0 mem0) as HR.
    repeat lazymatch type of HR with
           | forall _ : word, _ => specialize (HR brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hvl | exact Hlau | reflexivity ];
               specialize (HR h); clear h
           end.
    pose proof (main_know_ok (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 291460) sp0
                  a0s path envv rdraw tid regs0 mem0) as HK.
    repeat lazymatch type of HK with
           | forall _ : word, _ => specialize (HK brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hvl | exact Hlau | reflexivity ];
               specialize (HK h); clear h
           end.
    change (E0 (mkProcInputC [a0s; path] envv fs0 stdin0) sp0 a0s path envv rdraw tid regs0)
      with (ENV (vals0 (mkProcInputC [a0s; path] envv fs0 stdin0) sp0 a0s path envv rdraw tid regs0)) in HR, HK.
    set (vals := vals0 (mkProcInputC [a0s; path] envv fs0 stdin0) sp0 a0s path envv rdraw tid regs0) in *.
    assert (HL : length vals = 40%nat) by (subst vals; unfold vals0; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P2 : vals_ev vals 2 = pp) by reflexivity.
    assert (P5 : vals_ev vals 5 = tid) by reflexivity.
    clearbody vals.
    eapply (rz_run_lf RSEGS FUELM STOPSM scrA 0x473d0%Z sr_main kn_main 40%nat (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA) | exact HR | exact HK
      | apply Forall_nil | apply Forall_nil | reflexivity | reflexivity | ].
    intros R M HR' HK' EQM LF. rewrite cA_knA in HK'.
    change (s_pc (fst (fst rA))) with 0xebe88%Z. change (s_regs (fst (fst rA))) with srA in HR'.
    assert (RF : regions_flat (ENV vals) regA).
    { intros r Hr. unfold regA in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]. rewrite P0. lia. }
    pose proof (log_covered_frame (ENV vals) mem0 regA _ covA RF LF) as FR. rewrite <- EQM in FR.
    unfold regA, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENV] in FR. rewrite P0 in FR.
    replace (bv_unsigned sp0 + -224)%Z with (bv_unsigned sp0 - 224)%Z in FR by lia.
    apply (HA vals R M HL P0 P2 P5 HR' HK' FR).
    split.
    - krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|].
      unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot ev ENV] in Hrd. rewrite P0 in Hrd.
      replace (bv_unsigned sp0 + -56)%Z with (bv_unsigned sp0 - 56)%Z in Hrd by lia. exact Hrd.
    - intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ .. | lia];
      lazymatch goal with |- exists w, rdn _ _ (Z_to_bv 64 (?b + 8 * Z.of_nat ?k)) 8 = _ =>
        let off := eval vm_compute in (-120 + 8 * Z.of_nat k)%Z in
        krdv HK' 0%nat off 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia|];
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENV] in Hrd; rewrite P0 in Hrd;
        eexists; replace (b + 8 * Z.of_nat k)%Z with (bv_unsigned sp0 + off)%Z by (cbn; lia); exact Hrd
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_regs' : forall vals R,
    vals_ev vals 2 = pp -> regs_ok (ENV vals) srA R ->
    getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = pp
    /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Proof using All.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["Open"] "##2Th01bh12b1h22b2h31nh41Hh52HRh62P2h71Rh84valsp;1p;2p;3p;5p;6p;4g00@Qj16Tg017nj1ETg01L4j18Tg004<j1OTg00?lj10Tg02<Uj2NTg00A6j1GTg02=Aj2MTg007ej31Tg02>Cj1DTg02?Cj3I!sS$Uj15Tg03<5j3?!s/$Xj2=Tg01CKj2CTg01D1j23Tg03=Yj2<Tg00S8R0j2HTg03>8j2;Tg02fDj24Tg003bj2ATg00B3j1@Tg03??j5:Tg01Bmj6>Tg03@Aj3LTg00>ej1K!sy$Sj4BTf0R1#6#6p=2g00UPR2g00PVR3711p=9%01#0p=F!s-$#0#0p=J!s2+!s$'p=7g00OER4#6R5#2R6#6#2R7#ER8#8R9#O%05R5#ER:/N9f1R;g00Nf#G#GR<'Mp,2ppR=519f2R>#Dg036cR?;I;%06#5g01U4R65?:R@,=>RA%04R4#0RB#6#2#5RC,C8RD519%65#5=?:6RE,=>RFg03@eRG519RH%0!sB'5,=>RI=19=RJ%24!s<&6,=>R:,38g03A_R4'<#9RK'HRL'HP9f3RM#DRN1;?@'4A191DX091A9D%@C,4N=19DePAPNP?P>P@P1D:E>PHPLP91;?E,4NA191GX09g03BfRL%81RH%8;R@P0%8>?1;113M>13M;512R0[13>;13>1512%8M?1>;[RAf4#8?1M>\0AL>;1P1n20010!s#$12!s-%0W2W1W3PA^2@^1H^3LP1P8%FB#J#7!s$-2#0#F!v^$B,C8PG138G,A2O4b4%@B!uJ%GePF!uJ&E!uJ&JPK!uJ$5!uJ&=X09P;%K<!sX%=ePI!sX&5!sX&91;?6,4N1381/<4#9!vX$23%67#2!s$&5R7,C8,38!sG$d%@7,4N!s5'eP:!sy&6!sy%CBCBCBW5W6W7W8o"). Qed.

  (* [comment removed for export] *)
  Lemma path_at_A : forall M,
    frame_mod mem0 M regA_w -> (length path <= 4095)%nat ->
    (length path <= 4095)%nat /\ ~ In (Z_to_bv 8 0) path /\ rdn RSEGS M pp (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
(* LPS 727298f3 port: written out (rule 11g); the replay opened [path_facts] with its old
   fourth conjunct.  Text of boost-beast/http_request's lib/MainOpen.v [path_at_A]. *)
  Proof using All.
    intros M [FM _] Hlen. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct path_facts as (Sr & Slo & Shi & _).
    pose proof (path_len a0s path Hva) as HPl.
    split; [exact Hlen|]. split; [apply (path_nonul a0s path Hva)|].
    pose proof (u64_range pp).
    rewrite <- Sr. apply rdn_agree. intros j Hj. apply FM. cbn [outside]. split; [|exact I].
    unfold in_rng. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma seg_C : forall vals R M (mo : Model) T,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall R', getr R' 1 = Z_to_bv 64 0x47424 -> getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
                getr R' 4 = Z_to_bv 64 0x10b6b8 -> getr R' 8 = Z_to_bv 64 2 -> getr R' 10 = Z_to_bv 64 0x10000 ->
                getr R' 18 = pp -> getr R' 20 = Z_to_bv 64 3 -> getr R' 21 = Z_to_bv 64 0x10000 ->
                realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xdc75c) M (seg_rom RSEGS)) mo) T) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (Z_to_bv 64 3)) (Z_to_bv 64 0xebe8c) M (seg_rom RSEGS)) mo) T.
Proof using All.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["Open"] "##Fwh01bh12M'h22R'h32EMh43EQMh54Elogh63Epch72HCh82HKh93HK'h:2HLh;2HRh<3HR'h=3HR3h>2Hhh?3Hhih@5HlazyhA3HlohB1MhC2P0hD2P2hE1RhF1ThG2_HhH1lhI2mohJ4valshK1zp%0p&0p;1p;2p;3p;4p;5p;7p;6p;Og00@Qj11Tg017nj1STg01L4j1XTg004<j1FTg00?lj14Tg02<Uj2nTg01VUj1[Tg03LKj1fTg00lmj1cTg007ej30!se$\j2HTg03MBj1`Tg00K6j1PTg01MNk201Tg02=Aj2RTg02>Cj1;Tg02?Cj3TTg02@Qj4\Tg00AUj16Tg03N:j2?Tg03<5j39Tg01CKj25Tg01D1j2QTg019lj2bTg02Cej1aTg02Dij5JTg02Ejj2LTg011aj2VTg00B3j1GTg02fDj27Tg003bj28!t:$]k700Tg03Oej1~Tg03Pjj3}Tg03R1j3^Tg005<j3NTg00U3j3OTg03S4j2yTg02TWj5xTg02Ucj7wTg02Vlj4K!s\$Yj1vTg02WLj3rTg02XRj3qTg02Yaj2pTg02ZBj1mTg02[Ij3UTg00Snj1lTg01Bmj6ETg00>ej1Z!vv$Vj1kTg00G\j2oTg02k7j2jTg01@bj2YTg02_3j1iTg02`:j1hTg00C:j3sTg03T<j3tTg03UHj6g!w8$6j13!w/$Xj2]Tg02F_j4eTg03??j5{Tg03>8j2dTg03VMlO|Tf0R0#1#1p=A%30#3p=_!s-$#3#3p=z!s2+!s$'p=M%40#4p=2%40#1p=:%1!s6$>%10#6p==f3R1f2R2f1R3'];00p=C%1!t4$!s$,p=Dg026TR4g038kR5P3P0Cep=I!sQ+p=Wg01U4R69930p=@P1g03WPR7P2P3P0D{p=<f7R8f6R9f5R:,d7'7f4R7P11]23P0EEp=BP0P4P5g030=S00g031DS01g03XUR5P3g03Y\R;g00R3R<P2P1P7P:P9P8f8R=f9R>f:R?f;R@f<RAf=RBf>RCf?RDf@REfARFfBRGfCRHfDRIfERJfFRKfGRLMO|p=ug00OERM#1RN#1RO#1RP#1RQ#ARR#SRS#XRT#F%4NRU#SRV/nTRW%SP#X#[\TRXg03Zbg035b%[T%f3%cT301HTTRY#F%`2%PY30g027[201T9g00NfRY#_RZ#_#z#M!s$%R[301R8Yp,3sp0R\50T1R=Zp,2ppR]50T%;>g036cR^;T=P4%;?P=P<C\PTP0%6MR_P61?V_d59V%2P#:#:#A#>#A#:#=R`,5SRaCCPTP3%6NRN!sS$Nd59V1QS\Rb%1RRR#6'b,5SRc!sO$2%6ORd!sO$d!s|$4Q#>#:#2#>#>#2#A#=RQ,5SRe!sU$1%6PRP!sU$P!s~$5SNRf!sA$7%1URU#6Rg!sE$gd59VRh%1R#DRi#6Rj,5SRk!sQ$:%4O#=RO!sO$Od59VP]!s?$9%=UR:!s=$:!t\%MRM#6Rl,5SRm!sI$8%4U#6RU!sK$U!sb$kCCp,2fxR6P=%1M#2!v4$2!v<$2!v8$n,5SRoPG%a4RpDJ/LF/IE[!s#&^2Wp,4SPlo!t=%4#2!s$-A#W#D!s$$=/Vb!sO$hi%Ai!s=,,Vb%;CRbP^PBPm%GlRlP717bl,8TK00%~h=}^lA^Bhm5TbP6%>M!vy$2!x#$>!to$MP[g00:@Rbg00;LRh#FR^1Hb^Rig00<WRqg00W7Rr3NRs3NRtAOb^sRsAOiqrRug00M]#FRv1Hv^Rwg008?Rx#FRy1yr<Rz3NR{7N^R|AOv^{R{AOwyzR}%;DR~PBPp1@VgRg=^CmPAP@1HiqR@/8rP4Q00g008_Q01P5PMP;g00UnR;#PRMP<P[Dx%PhR[FwPiPqPbP^PtPsCKPuCK50@d1HwyR@/8z%vtRz%Px7r<PwPyPvP^P|P{CKP}!sP%P0P7Aq4B~,phRhPhP?P>%;F%mt;T3P4%;GP3P|C\%;H?UFz90X2g00UPRH%ltRt;0nR|A0^s[R[%F;R;?0zMRsP6P715StP1P!xe+PHPnP6P=15S0P8!s>%J/IIXKHPX%;L?UJzA0X0KX1XP;PMfHRM#;RL?UK0=0XKXH;18XJPzP0EEP9P1EEA0X9JPXPKP6P>PoP0!s|%K/IJX1XPAP=PTPL1@V_R_A0T0aX0T18Ta%G`,7L=0TaeP=P_PL!s+$9C<GB!sW&N!sW%cX0TRaPT%ZYR`%kRRR'oRA,jLRJPaPTP\1QS0/YR,5S=0Tc!t,%c1RMYPEEE%iA,7L,QS%hA'Y!sJ&eA0TJceg00Oj%GR7s`,7LAtL`REE!t[:dRdA0T0e!t,%e%GQ!u4%eeP=Pd!sW$d!sW0PRPA0T0f!sW%f%GN!sW%feP=PP!sW$P!sW,PgA0T0kX0TRP18Tk%Gj!sU%keRkP=Pg!sW$g!t00OROA0T0]X0TPD%ZZ!sW%]eP=PO!sU$O!sU0:R:A0T0m!t_%m17Ll=0TmeP=P:!sU$:!sU0URUPPPkP=PU!sD$U!sD%O9P8P0EEb3PtP2EEX5sXG[X6|g03[XEgW4W9W<X1XX2WMHub=b?bAW7W8W;WDWCW:W@W>WFWIWBWEWJo"). Qed.
  (* [comment removed for export] *)
  Definition regF_w : ltac2:(zQ "50!h8!s5!ina!na!kib@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ina!na!kib!s5!sb!t6!is9!t1!jva!kg1@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0@2$8@2$9@1$0#k0?3sp0+v0+h0@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+hgrmh4+4@1$7@2$3@1$2@1$0#k0$1").

  Lemma seg_F : forall (e : Z) vals R M (mo : Model) T,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    (1 <= e <= 4095)%Z -> scF e ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall R' M', getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R' 4 = Z_to_bv 64 0x10b6b8 -> getr R' 18 = pp ->
                  frame_mod M M' regF_w ->
                  realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x47660) M' (seg_rom RSEGS)) mo) T) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (Z_to_bv 64 0xebe8c) M (seg_rom RSEGS)) mo) T.
Proof using All.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["Open"] "##qxh01bh17__arithh24__ffh38__varmaph45__with51Hh64__x1h72FRh81nh92Hah:1zh;3HL0h<7__sat41h=!s0&2h>4cstrh?1rh@2M'hA2R'hB4__p1hC6!sL$0hD!s/%1hE!s^&3hF!s0&4hG3EQMhH2H0hI2HChJ2HKhK3HK'hL3HK1hM3HK2hN2HLhO2HRhP3HR'hQ3HR1hR3HR2hS3HSChT2HehU2HhhV3HhihW5HlazyhX3HlohY2HrhZ2LFh[1Mh\2P0h]2P2h^2Q0h_2Q2h`3Q40ha1Rhb2RFhc1Thd1ehe1lhf2mohg1ohh4valshi5vals1hj1xhk1yp%0p&0p&1p;1p;2p;3p;4p;5p;6p;7p;8p;<p;Ng00@Qj11Tg017nj1qTg01L4k10@Tg004<j1ZTg00?lj13Tg02<Uk20wTg01VUk10BTg03LKk10hTg00lmk10>Tg007ej30k106!sm$\j2]Tg03MBk10TTg00K6j1KTg00AUj1@Tg011aj24Tg00_Tk10rTg01MNj2?Tg02=Aj2Fk109Tg02>Cj17Tg02?Cj3kTg02@Qj4gTg03N:j2jTg03<5j3I!s/$Xj2WTg01D1j2DTg019lj2bTg01CKj2!sw$A_j3BTg02Cek11>Tg02Dik50MTg02Ejk20KTg02F_k40ITg01EJj1CTg00M=j36Tg03\]k20zTg03]dk10vTg03^ik20DTg003bj2=Tg01Bmj62Tg03_nk70sTg01Y2j3XTg03a8k20LTg03b>k20CTg03cCk80nTg03JAk20mTg01X[k20lTg03dMk30kTg03eXk10jTg002Cj6[Tg01]iR0j2oTg01;QR1j2<Tg01^Ak10fTg00j]k10eTg00k;k10dTg012=k20?Tg00oBk20c!s0$dk20!vN$0Pk30a!s0$ok40`!sv$_k40<Tg03f<k40:Tg00>ej1vTg02fDj2:!w]$]k70^Tg03Oek10!xy$Pjk30\Tg03R1k308Tg03gGk30!u4$9Ok207Tg00EJk30ZTg03hWk20YTg01g`k10X!y8$nR2j1RTg01hfk20VTg01iIk30UTg01jKj4!w+$]Dj1|Tg01:ik205!v4$mk30!z/$j?k20STg01>8k60R!v3$fk20QTg01=2k30P!s0$Uj3rTg00S8j2STg03ick70OTg03jjk603!{7$6j18Tg005<j3!w1$U3j3cTg02TWk50NTg02Uck70WTg02Vlj4M!sU$Yk11=Tg02WLk31<Tg00B3j1iTg00Z@k31;Tg00[Gk41!vt$kKk41!{#$XRk318k4!}Y$3l[k10;Tg03mCk315!s0$kk314Tg03nVk30HTg02Yak212!uF$nk1!~b$3oEk30G!s0$`k30!t]$ZBk10}Tg02[Ik300Tg02\Yk20|Tg00^ck30{!~1$Vk10FTg00G\j2~!~%$:S00k20ETg02]hj3!vf$@bj2!wI$?bj3pTg02_3j1!t0$`:j1uTg01k2k20uTg02a@k20xTg02bGk70yTg02cSj1!tB$mOj4!},$>8j2wTg02k7k20tTg00C:k30~Tg03T<k310Tg03??j5x!y:$fm<02!{[$`k70JTg00n:k70p!s0$^k816Tg02gKk4!#3t$l>mN0oTf0R3#3#3p=\%3!s0$!s$,p=ef2R4f1R5/43'Sp=m%83#8p>0A!s/$#8!s3$i!s3+!s$'p=ng00NfR6,F3p=J%33#1p=a%1!s}$L%1!s6$T%13#@p=E!s6$#1#1p=l!tU+p>01!s?+!s$'p=Hg008?R7g008_S01703p=dg027[R8g00UPR9P0P2P1g028:R:P6g00PVR;f3R<P4P5P3N<02p>0g20?93p=>P9P5g01GDP3Czp=YP5g002_R=g014OR>P>g014oR?P3g015OR@K0Jp=QP8P!t:&P:f5R:f4R1P!t21_14;5/S3p=UA0953p=O!s\$3P2P5P4P<!sb$6R2f7R0f8RA!s^$=t14;3p=;P4P=P>P>P?P5P3K0pp=G!s:-!u-%7GP3CzP!tc%AP<!sE+!tW$L16p=hg001AR@?053p=`g02mJRB?f93p=VAcB93p=^1S53,S4p=_P@P5P3g00X;RCH17p=yP4P9P5P3CMp=NP3g026TRDg030=S02g031DS03g040;S04P5g041AS05g042GRE!ua'P2P0PAf9RFf:RGf;RHf<RIf=S06f>S07f?RJf@RKfARLfBRMfCRNfDROfERPfFRQfGRRNN0op>0qg00OERS#1RT#1RU#1RV#1RW#1S08#1RX#qRY$0@RZ#ZR[%3TR\#qR]00wZS09%qV$0@$0B\ZR^g03Zbg035b&0BZ&0h5&0>Z301]ZZR_#Z&0T4%K_30%@SR_/40%\SS0:#3S0;#eR`#@Ra7m0&0rA1?ZA&0A6Rb$0A$0i#n!s$%Rc508%JFp,3sp0Rd50Z1FGbp,2ppRe50Z%7HS0<g036cRf;kGPD%7IRgPGg00R3RhCgQ09%@TRTg01U4Ri1j]Td5I],W51DYdRj%1XS0=#@'b,9YRk50Z%@URlPi1j]l!sP%4%aW#\#L#aS0>#3#L#\#T#ES0?,9YRm50Z%3U#ES0@PiQ0@,j]!s^%<=0Zeg043M9BK<PDg038kS0Ap,2fxS0BP:%\V#a!st$\#l#ES0C,9YP1&1>DS0DI0M00KKPJH0I[[[[^@^]Ap,4SPloS0E&01`S0F#T#l#H!s$$ER`/4j!sH$hiS0GQ0=#1!sF-H#ERV,4jPK%CL%KZRU56ZRnp,3a0sp,4path+0z$0vRoPfPJP8Pc20D3f#dX88Q01,=7Rp20Dcf#dd1?ZKP0E2P1K0sAXZKn$0900Lo?kfJPDPL%CM=6ZURnPoPJPh!st%C3h!st$Pp20Cch!sn%LPAE2P1L0nPDAXZL!sp'PJPhCgP81?ZMRo%CORn!sx$q9XZNRr/F3=0ZnX88RsP820mo6PsPZ%CNRs!sN$t#JA0Z3nX0Z1=ZsAXZMtRn20lo6'FB0kMt6E2Po&0joE[PcPFE[1Fnc=0ZsPZ%JNA0Z3dX0ZPF%JrRrPNPqP6P8Pc1o63X881o6c%1\Rq#1#ERs,<;Rn1=9;PcPs1=9sS0HH0gg015oRo#KRt%ZoRo&0f9S0I&0e9Ru&0d9Rv20?9;Rw%>sRx'Y'Q20cv?RyP3P4Pp20b34#ddB0a9;5H0`Rpb2b3b4PnP3b1H0<1?ZNPGE2H0:E2A0ZrdPZ1FObA0Z3eX0ZS0JPF%CP!v3$r9XZO/FbRnPOPrPb!uF%b!uF%bc1<TsRrPbPT1=9TPcPsQ0HJ0_PtPoQ0IPu%>TRz/Yx,QvPyP!tY'r!tY,OPH!tY,ne%CQ=6ZU9XZPP[%73R[PfPP%CRRU%vcRnP:P<1:[n=0ZUeK0^%@qRq!}6$qd5I]Rr$0]>0\fnB08PrU5k[g00M]R[%75Rr>0[DP%@XRX-07TRU/baRf1bU_Rx60ZnPhPDPrPPPnPfPxPZfHRh#CR{1DY3R|,4f?m|xX0Z20YhK1DY{,4ffIS0K#CR{$0X1DY{Rh1<hU'UQ0K,?ZRh=08c%RhR}/OsR~&068S0L&069S0M%R5%R3'OA085320V5340UXk8Xj8S0NPhP}1=9}!vt&M9tPKCsP~fJS0O,?ZR~#|%R~#;205TXS0P1<;TR~%;X1<;US0Q[[S0R%;TR}g01FBRhB04TX5UW9S0S%;U\h^9}S0T%3\#ER\-05TS0U%;\207T\RX,<;[\~S0VB04T\5VhX9}S0W%;X!s`&Xp-0R}PtPo20S95S0YPuPvPv!#;e'<J0R20Q9SRSB0P9zYRz'Y,Qv5Gv&0>>S0ZPv%>a9r9z=AvSRaQ0Z%>_9r9z9AvS9GvaChCh!yP,X69WB1<3U,S514f514f4?m4x[[^69^B}P3fQS0[#C,DYR}#;P}P0PAO4b1b<b=bEbFb>b;bHb51F5cP1E21:rn!sS$!xM$}xeK0OP:J03!xy&ECgRrePrQ0BQ0:#L#L$01#L#T#L#a#ES0:%8cS0\g00:@Rrg00;LR}#ZRx1]rxRfg00<WRag00Y<R_3fR>3fR?Acrx>R>Acfa_S0]%Z[R[1][xR=%Z7Rhg00]dRX3fR\7fxS0^Ac[x\R\Ac=hXS0_%74R~PQQ0DAI]qi>08R{PPPO1]faRO/=_PDQ02Q01Q03Q04Q0:Q05g00Un#KPEQ0\I0N%K}R_K0WPfPaPrPxP?P>CMQ0]CM50Od1]=hRO/=X&1=?RX%K781<EP=PhP[PxQ0^P\CMQ0_!sT%P5P3Pxg00\RROg00]2R[g00OjRh%i;R=81;nRnQ0F$01#e!s$&T#H#L#@RE#iRrH1:Ra=6}_RfPDPR%7<P3H19XexRPP}B18DQ~RqPaP_PZP{Q08#q&0;319Y;R{$0;615h814Y19YE60H[=07OX0ZPK1F4cP:E21:~n1:~r!sC'ePDPQP~PaH13e212}qRqJ03P>A0x>fRfA0x\_R>&11?R}Q0C'ORa1Sf>R~g044PRQ40GRO40=E2PxP_PPPqP\B0Gf>OE2PNPMQ09%71&0}?;k5PD%7:P5Q0^Cg%72Q0O<00X90^4%7000|XP9Q0CPDQ0AQ0BP219Y3RDP:Q0DI0MfL+0KfKH0IX:9B0{@3CQ00PBP9%v6R6Q0;#lR?$0FRM'~%@WRWCMRN/`5PBP9Q0>#1#T#a#a#ERB,~=PlCMR=/`5g00c3RO+0EQ0<%V4%^43PP31`N4P@PNQ06#7R>%V3Rf%^3R\3PX?@PZPd15|MRq1<qU%;WRP15qW/4U3_'UX0ZfRR_,?ZRx!#5R$xR7/OsR[Q0LQ0MQ0NPxP71=97!#5/+Q0KCsP[fSR[,?ZR7#|%R7Rx#;Q0PQ0RQ0SQ0TQ0UQ0VQ0WQ0X!#9V$YPuPv%>V9AvSQ!#3R$`=!s2%%>M9p9SRr9Avw1Yrz,Qv%>WRn9AvwAp9rn=Avz5Gv!s%%!#3l3143V14`5154MR`1<`U15`W/4U7_P'U[[^69P3PjQ0GQ0EO3!#3f0%JIQ07E2%VNRP#},:g,DY%uP'5!sq%%^NRN#;15`N!vT&eAPgPNeP<P3E[W5P3O11`=400EOQ001`=<PO%V1%^15P>P31`=1P@P=%7JR1?Pf\X?@P9P;153BR\1<\U%;lRf15\l!w]':9!vj/!#=6,B9p9wR>!vF%>!vF%lR4!vF&>4!vF0!vB,15;BR41<4U154l!v7$f'UP3b1bCbD1DY{R{!t@8AAvww1Ywz!#8V$!sx-4;;Q0Q'S!sk'-0u;RzE2Q07#7Rw%V=Rf#}':!vk$f'5R>1<>U%^=R=#;15>=!vk,wf=eP:!vk,PO%V2%^25P1P3n010!s#%X5OP3O1n20!s9'2110!s3&!s`%!sB51000WYX?@%7A00xCR@eP@%7FR@fMROPCPXg045UP3P5K0yB00@OX1]Z9RC%{@'y5BOP^%7GROfNR@<00XfORXQ0<#{,yC7B3Xg^P3P2P<E2%{O,yC9B@2PZ%JHfPR@19Yq=NZW15{B,9Y=NZl%KCRB56CRq56C7BAX0ZP3PdQ06E[15jMR2!sO%WRO=6Cq9BX0P9P{Q0[19Y\=NZl=6CB96CO7BFX:9P3P;PzE[19Y4!sD'R!sF$9B@AA087c1OxsR8!~0,7Px1=9x!~0/OCsP8fT,?ZR8#|%R8#;!}x99%@?R?#>9r9Sg013hPrCz!#D^/X691b3?153M'O!}0&O1!}&&>b;1bj?R?/O2P9P2ANZDW!uG$B[HX:9P5P?P3E219Y?=NZ!sA&_GPRPIPHPZg046VRHAI]TiRT'w,:1A0Z3kX0ZRRPZQ0=$0FR_,~6RB-0t1RCPR!#5Y%_,9Y=0Zk!#JP$k%JJPLE2%}B,:1!zc$B'5!sI&eA0ZCke%i_:0~h6,:1B1016_E21WITP1PHPIPTPGDxE2PZAI]liRl,wH!t\&m!t1%mQ0?#i,:1=0Zme1WIl!s`&l!s`'Q0@=I]iRi!sb%Q0JPK%vb!sY%ee1WIi!sY&i!sY&3O6b7b5b7!s$&bP}B0=a~QE2WZWGWKWPX@^WANH0qbMbRbib_b^b`bLbQbVbXWIWJWOW]W\WNWSWTWWWUWcWfW[WaWhXd9o"). Qed.
End Open.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Usage.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable model0 : Model.
  (* LPS 727298f3 port: [main_entry] is over the run's whole input, and the argv-string facts
     read the launch, so the input and the launch facts are parameters here, tied to [av] /
     [envv] by [Hargv] / [Henvp] as RefMainEntryN's section does.  Section shape of
     boost-beast/http_request's lib/MainOpen.v [Section Usage]. *)
  Variable inp : ProcInput.
  Variables (mbase brk entryw : word).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Henvp : in_envp inp = envv.
  Hypothesis Hhw : in_hwcap inp = a_hwcap.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
  Hypothesis Hargc : length av <> 2%nat.
  Hypothesis Hh0 : m_halted model0 = None.
  Hypothesis Hlazy0 : m_vm_lazy model0 = [].


  Definition ENVU : ltac2:(zQ "40!h8!ina!ko4!kib>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!ina!kib!t1!lge!lha!ll9\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Definition regU_w : ltac2:(zQ "50!h8!s5!ina!na!kib@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ina!na!kib!s5!sb!t1!t6!jva!is9!kg1@3$4@2$3@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$8@1$0#k0@2$7@2$9@1$0#k0?3sp0+o0+l0@1$5@2$3@1$2@1$0#k0$1").

  (* [comment removed for export] *)
  Definition frameU : ltac2:(zQ "40!ina!kib!lm4!mnc>1R@2$3@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "h30!ina!kib!h8!lm4!is9!lmc!hi4!lq9!lv9!mj6!jva!kg1!hv4!mo5!moa!mp2!mp8!mke!mnc\1R@2$h2@1$0#5@1$1@1$0#k0\1M>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$4@1$0#k0+tqgsc@2$c@2$h1@1$1@1$0#k0\1w@1$1@1$0#k0@3$6@1$3@1$2@1$1@1$0#8@4$8$9^2@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+k0N8@2$5@1$2@1$1@1$0#8@2$7N8^1@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+k8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+9Kv$d@2$h0@1$0#5+9@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+l0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h2Kv$d@2$h0@1$0#5+h2@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+l8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h3Kv$d@2$h0@1$0#5+h3@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+m0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h4Kv$d@2$h0@1$0#5+h4@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+m8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h5Kv$d@2$h0@1$0#5+h5@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+n0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h6Kv$d@2$h0@1$0#5+h6@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+n8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h7Kv$d@2$h0@1$0#5+h7").

  (* LPS 727298f3 port: written out (rule 11g), restated over the revision's
     [cat_argv_ptr] (the drawn stack top and the exec file name).  Text of
     boost-beast/http_request's lib/MainOpen.v [seg_U], applying RefMainEntryN's lemmas over
     their current sections. *)
  Lemma seg_U : forall T,
    (forall R M,
       getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 1095352 -> getr R 8 = Z_to_bv 64 2 ->
       getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
       frame_mod mem0 M regU_w -> frameU R M ->
       rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0)) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 292200) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 291792) mem0 (seg_rom RSEGS)) model0) T.
  Proof using All.
    intros T HU. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_okN inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as HR.
    repeat lazymatch type of HR with
           | forall _ : word, _ => specialize (HR brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (HR h); clear h
           end.
    pose proof (main_know_okN inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as HK.
    repeat lazymatch type of HK with
           | forall _ : word, _ => specialize (HK brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (HK h); clear h
           end.
    pose proof (evN_argc inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as Hac.
    repeat lazymatch type of Hac with
           | forall _ : word, _ => specialize (Hac brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (Hac h); clear h
           end.
    assert (Uac : bv_unsigned (argcN inp) = Z.of_nat (length av)).
    { rewrite <- Hargv. eapply u_argcN. rewrite Hargv. exact Hva. }
    change (EN inp sp0 av envv rdraw tid regs0) with (ENVU (valsN inp sp0 av envv rdraw tid regs0)) in HR, HK, Hac.
    set (vals := valsN inp sp0 av envv rdraw tid regs0) in *.
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) by reflexivity.
    cbn [ev ENVU] in Hac.
    clearbody vals.
    eapply (rz_run_lf RSEGS FUELM STOPSM scrU 291792%Z sr_mainN kn_mainN 40%nat (fst (fst rU)) (snd (fst rU)) (snd rU)
              (fst (fst cU)) (snd (fst cU)) (snd cU) (ENVU vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rU) | vm_cast_no_check (@eq_refl _ cU) | exact HR | exact HK
      | | apply Forall_nil | exact Hh0 | exact Hlazy0 | ].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. unfold sc_denot. cbn [branch_taken edenot ev ENVU]. rewrite Hac.
      unfold bv_eqb. rewrite Uac. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R M HR' HK' EQM LF. rewrite cU_knU in HK'.
    change (s_pc (fst (fst rU))) with 292200%Z. change (s_regs (fst (fst rU))) with srU in HR'.
    assert (RF : regions_flat (ENVU vals) regU).
    { intros r Hr. unfold regU in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
      unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENVU]. rewrite P0. lia. }
    pose proof (log_covered_frame (ENVU vals) mem0 regU _ covU RF LF) as FR. rewrite <- EQM in FR.
    unfold regU, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev ENVU] in FR. rewrite P0 in FR.
    replace (bv_unsigned sp0 + -128)%Z with (bv_unsigned sp0 - 128)%Z in FR by lia.
    apply (HU R M).
    - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - regv HR' (4:reg). reflexivity.
    - regv HR' (8:reg). reflexivity.
    - regv HR' (11:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVU]. rewrite P0. f_equal; try lia.
    - exact FR.
    - unfold frameU.
      repeat split.
      + krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 56)%Z with (bv_unsigned sp0 + -56)%Z by lia. exact Hrd.
      + eexists. krdv HK' 0%nat (-64)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        replace (bv_unsigned sp0 - 64)%Z with (bv_unsigned sp0 + -64)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-72)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (9:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 72)%Z with (bv_unsigned sp0 + -72)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-80)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (18:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 80)%Z with (bv_unsigned sp0 + -80)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-88)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (19:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 88)%Z with (bv_unsigned sp0 + -88)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-96)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (20:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 96)%Z with (bv_unsigned sp0 + -96)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-104)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (21:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 104)%Z with (bv_unsigned sp0 + -104)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-112)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (22:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 112)%Z with (bv_unsigned sp0 + -112)%Z by lia. exact Hrd.
      + krdv HK' 0%nat (-120)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
        unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0 in Hrd.
        regv HR' (23:reg); cbn [edenot ev ENVU];
        replace (bv_unsigned sp0 - 120)%Z with (bv_unsigned sp0 + -120)%Z by lia. exact Hrd.
    - krdv HK' 0%nat 8%Z 8%nat Hrd; [apply flat_intro; cbn [edenot ev ENVU]; rewrite ?P0; lia|].
      unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev ENVU] in Hrd; rewrite P0, P1 in Hrd. exact Hrd.
  Qed.

  (* LPS 727298f3 port: written out (rule 11g), restated over the revision's [cat_argv_ptr];
     the sixth conjunct's margin is 8, the one RefMainEntryN.str_fits_N proves (the old [+ 17]
     is false at the revision).  The facts are RefMainEntryN's [main_strN] and [str_fits_N]
     at k = 0, and [valid_argv]'s no-NUL clause. *)
  Lemma arg0_facts :
    rdn RSEGS mem0 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) (length (nth 0 av []) + 1) = Some (nth 0 av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth 0 av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])))) 8 = Some t8)
    /\ (entry_stack_fits sp0 av envv -> (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0) + Z.of_nat (length (nth 0 av [])) + 8 <= 0x800000000000)%Z)
    /\ ~ In (Z_to_bv 8 0) (nth 0 av []).
  Proof using All.
    clear Hargc Hh0 Hlazy0. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
    pose proof (main_strN inp mbase entryw sp0 av envv rdraw tid regs0 mem0) as MS.
    repeat lazymatch type of MS with
           | forall _ : word, _ => specialize (MS brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (MS h); clear h
           end.
    pose proof (str_fits_N inp mbase entryw sp0 av envv rdraw) as SF.
    repeat lazymatch type of SF with
           | forall _ : word, _ => specialize (SF brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hargv | exact Henvp | exact Hhw | exact Hvl | exact Hlau ];
               specialize (SF h); clear h
           end.
    destruct (MS 0%nat ltac:(lia)) as (Sr & Slo & Shi & Slen & St8).
    split; [exact Sr|]. split; [exact Slo|]. split; [exact Shi|]. split; [exact Slen|]. split; [exact St8|]. split.
    - intros _. exact (SF 0%nat ltac:(lia)).
    - destruct Hva as (_ & _ & _ & Hn & _). apply (proj1 (Forall_forall _ _) Hn). apply nth_In. lia.
  Qed.
End Usage.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
