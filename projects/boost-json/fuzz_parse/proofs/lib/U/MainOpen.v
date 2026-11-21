(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib ArgvEnv MuslStrlen RefLayout StepTac SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux Spec RefNodes LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefStartup RefStartupFacts RefMainEntry RefMainEntryN LibDiagKn RefPrintfFirst MainDefs MainWalk_defs MainSegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MainOpen () := KReplay.lz_vm "#%K`C4ELinuxProcessSemantics?!s<22Fs4pathI47Corelib5Lists7!s+#Def6Forall00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux7sregionC13~~~C!t1+4Init5Logic6eq_indC46Stdlib9micromega5Tauto5eKindI!sE;8GFormula00K!t,72eq01I!s@19Datatypes4list00!sF=prod00C!sF;3fstC8!v6N8SymExec23SX25s_log!v:&!v|V;log_covered!sl%I!uy;!uY>bool!v[4!sF31c!u\O1U8MainOpen4regA!tk&!vG\9sym_state00!src8sidecond!sqe7scripts!sp'C!vBQ=!vB#Walk_defs2r!vE&K!t^\4expr02!sm&!x?+7Numbers7BinNums8positive01!sKG2!y1<3nat!sE/!sj31Z02!uDc1!v3i3!smc6kentry05!sok6!sok7!soc5sadd!w0f!t_'8!sok4!{03!#7d71!z?@3!tUe1!tUH2I!t7d0!t7B!|~$!}jH3K!#><95Riscv5Instr5aluop!v^B!#8G[2cA!#5le3kn!#94&!#:y63and!#>79!sA$1!#=3\4s_pc!u8&!wW<sndI!v\?0!y'^s!y'0!#9RaC!sl%!#=\^F!tWhF!#7vh4!smc!#>E+!~=D!#A7#2!|`G;branch_!s~$5!|H]!w1'!#Fs&!#H`$4!s+#2In!#Ck8or00!t@[3s!tA,!#JTH5State6EACCES!s[SMFILE!s[SN!s[#!uq85False00C6!sxI3Sys2Fs4!up#=openat_errnos!tbTOMEM!s[Q<ENAMETOOLONG!t>UENTK!#Ly47EnvRing3Pol01!sG6=!sD#M!#MP'Psatz!{9#!sOI4!sOK6!sO6:Z!sL+;ZArith!zW$!tL86VarMap1t02I!sD?0I!t_C7!#O|,!vM<5PE!#GW#K!#PkD!#G'<6option!vlF!tb+1!t?F5!sJF8!#S;;8B!sJ&C!wW@=Z!sT$CheckerC!w9<4f!#TP8!sq-C!sq0_soundC5!sX&6!xg%6BinInt1Z2le!w]E!vDG4!sJF6!w_D3Op2!#U{>unit!y_8!t9%4kind!#A}-!sf81I!v^@!|&00!|VN1!uUI3!#Cl=N02!wq<3oppC45stdpp9bitvector;defini!{_#s7bv_wrap!si=pow!sC=sub!sC<6modulo!sF<>pow_pos_nonneg!z->t!sB<:!sj#!sfB7compar!zsF7!sIE!zrG3!smE6!sIE5!sIE3!w_=mul!sC=ad!~<=:mod_unique!#]lO8PropExec=!yh&64_mod!#HR7!#>8$8!#ar$_r!z`BZ_to_bv!sLA;bv_unsigned!sPA@!sv&!sU-!#=^N9!#?S#_ret!#@]74True!#`?=:!zK%ison!#3/7!~[65!#In^U!#IngU!#KG`2cU!#P\hU!#P\&!xO?2bv00!xCK3Run:valid_argv!#P;;6length!#5C<of_nat!tEO?total!tE#_bytes!#G$Q5Namei>path_has_slash!#mNM8!s`$eqb!#Ko7tl!}j89!#H|#!#la$!sE67f_equal!xVP3Lib2Nd:and_elimF5!#3;=3not!vGX;dotdot_!ul#K!}p=1!u1a4!#X=7!#EF4!#qFP7CatExec<cat!ze$_ptr!vC3!#rW03nth!v_23Nat!#8I#!tk;3app!#GPC1!{IO@!#XT#_stack_fits!#oI9x!v/R3Amb5a_ui!#9V&!scS7a_hwcap!se&!~424Znat5Nat2Z9i!#@-'!u12Peano2lt!#7k5!#LZ+1!#HF5;ZifyClasses;rew_iff_rev!u;P:MuslStrlen=!y$'_room!#U`P;S!wa#LayoutAbuild!ws&!#4@$!#>?WM!sn4_within_span!tnQ!y[4!si$!teX8wrap_me!v@R6BvBase;nat_to_wor!#?FA6bv_!|t#!~?PStepTac<!t,#!sd#!#9B#!{AU!uc+9u64_range!{HD7inj!zA#!#7w8!zZ#sym!{,B5mkrel!sKB7!{R&!#6`O=!#a,&Sound4SX2S7u_small!#E1>!|a%f!taC3inj!#?zQ:RefStartupDmain_!z\%rdn_abov!w6&K!#5>:!#9Va2!#9V7!#4:&e!#6EQ!#3K,B!#3K#!z=$readable!#C9U!t~&9ex!t}%1!#C}W<RefMainE!vx#8!w'$s!#;6'!{uX3rdn!w_'!#7T=3!{MEapp!sKB6!sK$2!tw/!tp96images5Ubsan1M?loaded_segments!#?0A!#sU#0!~6>6!~6#!#SA4!sH4e!txT5phdrs!#6EP!#dn%sp_window_lo!sa\hi!wI68!wI#Inst7Inj_Z_Z!t,;!#la$7Prelude5bvmap!$16SRun7vals_ev!u~%!#l'[ENV!|3V!#5m6regs_ok!stjknow!st,!v>O5Frame9f!s+#!#UY+!v?[6!sn$A!~\_7seg_r!#AQ'!sjX4mkst!#3I&!#@JL6config01I!tDPShapeAlg8realize!$3kZ!#6H/<!#6H#!y<]!su22E!tbl!z&1!su^5!}J#!tef2p!skh!#;Ee5auxvp!sne3rn!#MBV8SymDrive9junk_!v}#!tZX>!#Al,efs8canary_w!taV9!ta'X@!tb+_!#Z<%!st%!#Wv5:!sG%_app!$#\\!$?o,!xHW!$$P1ym_exec!#3Z&!#=}9!$EZ$!$/0]5carry!t}V!#8c58sc_denot!u'3!$JS8!u+^6s!#4W#!u,i9mem!u-/!u}dlog_fla!suj4!sqZ!vO1a_base!smc5a_off!}LV!$K[%<!$OX$s!v=/!smVA!$LJ,_!#>?#!sr]6r!xi/!#3pX:!uE#_intro!#3j&!#E3>3Sem5alu64!x?^e!u,/!#`t:map!#GmJ>!ti$!sE+@!#OR#to_le!#[3V!v9'5krea!#9P`!sh$_!#N`'!{j_!~C[!#:?$PrintfFirst9rz_run_l!{r&!$=`\!$H-%!$P}c!$;@$!#?}&!#O;<8inj_succ!uwR!#pz05FUELM!vhX!so16STOPS!spg4scr!$E'X!#A?/7sr_main!spfkn!sp/!#IWW4TSet!v;f3s!v:'!#M~[regA!#BoW4Scfg=hunspell_scfg!tYbcA_!$Ip'!#{C[cov!$YJ&!#x}C1!#O{Yge!#]-'!#xg:5ld!#czR!#A@1r_ge!#<:ZRun7reg_va!#d]'!v&?5bv_eqC5!#v^L4Uapi8AT_FDCWD!$BcVBopen_igno!#>'#lags!$Ml=N!#ciQ!#W3$7outsid!#?+V7StoreOk!#Ds#grows!zVa!#|e$len!sma:!sm$nonul!uKV!v4%6in_rng!|3'!#_93!$4F27!#AtY9!#j;#gre!#nK25!|9$8!#i4#Na!#z?+!#nkAadd!vUafact!#cFW8m_halt!$2RSm_vm_lazy!}5A4BvWf!#A|X;!#Zv#set_a!#WaV!#?Q0ridx!skc6sr_up!#DHW!#6]&6reg!si,!#?l_!#Rc#M!t[V!{+,>!#H_$!#wD#li!#=KV!#r+33!v<W!t_'6!#Ey$!v<f3s!$[h&!#Db`noscr!sof4srC!#GV&!|vP5Model!$XX\8rC!~z0!smQ!#DK/6blob!#bi'!xOX8!si$!#mx'!#>:V:sr_vars_l!#R^`<env_app!#Z3,!#_,\3env!#_#'!uKWkn!uKqkno!#bg`=!#ri%!vA%!sq&!#;'=7add_0_r!t=gl!zjV!#^b6!$nD$!#kL'!|Q[?!$F]'!$,U/!xUV<k!sg$!#Yl-!#bOB2!u|dscs!#a`/!#[,Dlow32!#[UH!sNC!#z2&4sext!syE<!$h>%taken!$/,75proj2!sA=1!#T?cF!#8=hF!$oNf4kn!sn'!#Rc^F!#Rc&!#9<\F!#9<-!#Qw^!v}g3s!wl'!#|q`!$NA&!$-|@9and_morph!sOCnot!sO&!uTR!#<U-N=!#zs-N!vMY!sw02E!slg=!#zv-!swg8evN_argc!srV!#<l/2!#?6W7ArgvEnv5!tQ#!uFg!#}@#!v7ljun!#:Va4ENV!{H+!#7KF6!#Xy#b!$L{;4neg!$cb<3!$S>-4Bool!s'$=!s[#_true!$@w#!$bp;eqb_neq!x1X7u_!x3^!#3a2!$Z7f4sc!sn[!xy1!#fY%!ymh!#f[%N!#69aregU!#9G&!%#'S2!#dp\U_!$^+'!#9w^!#8C2!$&1,=!#BS$_f!s,$!sH76nth_In!wN`9!$CE&!wO&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~he7sregion37Corelib7Numbers7BinNumsm11Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ne5saddr04prod04cons03nil04pairne4EVarne2SA03fstne8sidecondne9sym_state04bool04true37Corelib4Init5Logichh02eqheblog_coveredne5s_logne7scripts89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainOpen4FPX1~~~~~~hka4regA79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UdMainWalk_defs~~~~~~hp42rAne6kentryhka2cAhp43knAhp42rChh03andne6sentry03sndne4s_pcne4ELithka4regFhp42rF05false3h5LinuxProcessSemantics5Riscv5Instrij07ALU_ADDij06BC_LTUne5EAluwne4SCBrhka2cFm14Npos3h5LinuxProcessSemantics5Riscv3Semio55low3235stdpp9bitvectorbdefinitionsir07Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSem5Stateit89errno_ret3h5LinuxProcessSemantics5Riscv7Preludejh34sextio55alu32io5cbranch_taken5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openjladopenat_errnoshka3scF36Stdlib5Lists4Listjq62Init8cENAMETOOLONGit86ENOENT46Stdlib6ZArith6BinInt1Zjt92lejt93powjt93subir0bbv_unsignedhka4regUhp42rUhka2cUhp43knUir02bvhh03not3h5LinuxProcessSemanticsfLinuxProcessSem3Runkjcavalid_argv06lengthjt96of_natne3env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~koe8blobs_evne3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~ktb7vals_ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcRefMainEntry~~~~~~lhf6blobs006option04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsln8h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ls43rdn69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~mg6floaded_segments03nathh02ex37Corelib4Init5Peanomla2ltjt93addjt93muljh35bvmaphh01Ils44getrir02BVir04BvWfkjc5mkCfgls44mkstls47seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ms2dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~nga8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~nl1ccat_argv_ptr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~npb9frame_modnga4TSet89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainOpen5Usage~~~~~~nu86frameUnu86regU_w37Corelib5Lists7ListDefojf3nth03app37Corelib4Init3Natom23addkjch0entry_stack_fits3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutop09EntryDrawkjcavalid_envpkjc8valid_spjt92lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStartup~~~~~~ov1amain_entryit85Model04Noneit88m_haltedit89m_vm_lazy" s.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition regA : ltac2:(zQ "20!h8!l7@1$0$1") := ltac2:(zQ "80!na!rd!s5!sb!t1!t6!tc!u3@3$3@2$2$1$0@4$5$1$0@2$7@1$6N0-u0+r0@1$4@2$2$1$0").
Lemma covA : ltac2:(zQ "d0!u8!h8!ud!v8!hg4!s5!hga!hi4!hia!hj8!hk0!hoc!ht6@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##%Np;2p;1p;3p10000p4p70!s1$`p4p710p8p1001A!s?+2C!s?/2_!s4$1p1003>p4p73101p8g003bj26Tg004<j15!s/$\j21Tg005<j30!s/$Yj14Tg006_j22Tg007ej33Tg008?R0g008_R1'6g009?g00:BR2g00;N#5R31123g00<Yg00=c3030#4'2=301do"). Qed.
Definition cA := Eval vm_compute in carryM rA kn_main.
Lemma cA_knA : ltac2:(zQ "90!h8!htc!u8!ud!hg4!s5!hi4!hu5!hub@3$6@1$0$1@3$2@1$0$1@1$0$3@3$2@2$5@1$0$1@1$0$3@1$0$4$7$8").
Proof.
vm_compute. reflexivity. Qed.
Lemma rC_facts : ltac2:(zQ "f1!h8!ud!v8!u8!s5!hi4!hk0!hv2!t1!hv8!hvf!ig8!na!hj8!igd&@3$3$2@1$0$1@3$3@2$4$2@1$0$1$6$7@2$9@3$5$c@1$e~0+tvsg4@2$9@3$5@1$0$1@3$b$2@1$0$1@3$3@2$4$2@1$0$1$6$7@1$8$1@3$5@1$0$a@1$d~0@1$8$a").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##&\p;1p;3p;2p;4g00@0j11Tg00@Uj10Tg00AYj1<Tg007ej32Tg004<j18Tg00K:j17Tg00S@j24Tg003bj23!s8$[j46!sS$\j2;Tg005<j35Tg00T6j19Tg00U;j3:!sA$Yj1=!s8$XR0g00OI#1#0#1!s$00!s$0!s6%<R1;21g00;NR2#8R3%72R2;22R4g00V6R5#8R6%75R5;25R7'41301P4P713321365C6C6g00:BR71;73g00<Yg00W?35R4753R8#9=201A:734=232%=8=265'4'4do"). Qed.
(* [comment removed for export] *)
Definition regF : ltac2:(zQ "20!h8!l7@1$0$1") := ltac2:(zQ "90!na!rd!s5!sb!t6!u3!t1!ih4!tc@3$3@2$2$1$0@4$4$1$0@2$5@1$8N0-v0+h0@3$3@2$2$1$0@4$4$1$0@2$5@1$7Z+hgurl4+4@1$6@2$2$1$0").
Lemma covF : ltac2:(zQ "d0!u8!h8!ud!v8!hg4!s5!hga!hi4!hia!hj8!hk0!ihb!ii3@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1p;3g003bj26Tg004<j15Tg004\j21Tg005<j30Tg005Yj14Tg006_j22Tg007ej33Tg008?R0g008_R1'6g00XEg00:BR2g00;N#5R31123g00<Yg00YH3030#4'2=301do"). Qed.
Definition cF := Eval vm_compute in carryM rF knF0.
(* [comment removed for export] *)
Lemma rF_facts : ltac2:(zQ "h80!h8!ud!u8!v8!s5!hi4!t1!ig8!hv8!ih4!htc!hk0!ii3!hg4!sb!ii9!na!il4!ilf!im9!tc!in1!igd!in8@2$8@3$5$h0@1$h6@3$2$3@1$0$1@3$2@2$4$3@1$0$1$b$c+knin4@2$8@3$5@1$0$1@3$7$3@1$0$1@3$2@2$4$3@1$0$1$b$c@3$e$1@4$h5$f$h2@3$h3$h1@1$h4Ni8@1$9Z@1$9+vvvvvvvvvvvvvgg1@1$6$1@3$5@1$0$1@3$7@1$0$a@1$0$1@3$2@2$4@1$0$a@1$0$1@1$0$d$h7@1$6$1").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##+fp;1p;3p;4p;2g00@Uj16Tg00@0j10Tg00AYj1@Tg007ej33Tg004<j18Tg00>ij1CTg00B7j1=Tg00ZNj3BTg00[Uj4ATg00K:j1FTg00MAj3ETg00S@j2;Tg003bj2:!s8$[j4?!t$$\j2<Tg005<j39Tg00T6j1DTg00U;j3>!t^$:j12Tf0R0#6#6p=1%00#0p=7%20#2!s$/p=5!sB$!s$/p=4g00UXR0g00OIR1#6#1#0#7!s+$!s0%6!s0$@R2;32g00;NR3#8R4g00\`g00]@g00Ong00Nj#5!s$+Cg00PZ#=3B%01#7#4!s$-6#1!s$+0#@#=CA%F3R15E3R3;33R5A3411R6';1:02P5P61:431:41C?C?g00:BR61<64g00<Yg00YH39R5794#D=302A>645=343g00Ma#8R31<34g008?#8g00^2397>4=341';';do"). Qed.

(* [comment removed for export] *)
Definition scF : ltac2:(zQ "10!na>1e$0P") := ltac2:(zQ "d0!ine!iq7!isd!hg4!ii9!hi4!na!jg6!il4!ilf!jj9!jk1!jka\1e$6@3$5$3@3$c$9@3$a@1$0#i0@1$0#k0@3$b$8@1$1@1$7^1@1$1@2$2@1$0#k0Z@2$2@1$0#k0+vvvvvvvvvvvvvgg1$4").
Lemma scF_openat : ltac2:(zQ "40!na!joe!jpf!jr9>1e$0>0@3$3$0^1$1@1$2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##,=h01Hh11eh22Hep;3p;2p;1p;6g00_3j39Tg007ej35Tg00_JR0j22!s1$dj10Tg003bj28Tg002Cj66Tg00UXR1g00`fR2f0R335p=7g00a[R4=513p=3g00bPR5!s4%1g00cER6,23p=4g00cb9913P0g00ddR7f1R8551%78%38%18#4'2'2f2R8#0P3A5178P1P7%03X11R9g008?g00\`'8R:%07df3R7P3E6W0P3O!sn3P0%77%37%17#4'2f4R7#0P3%77P1P2P9P:%02df5R2!si-!sU+P0%32%12#4f6R2!s_$32P1P4!s_%4df7R4!s_-12#4P0%14P6f8R4!sW$14P1P5!sW%5df9!sU,P6f:#0P3n010!s#%X06P3O1n20!s9'2!s-$!s'$!s[%!sBr2X11o"). Qed.
Lemma scF_ENAMETOOLONG : ltac2:(zQ "20!jrf!jpf@1$1$0").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1g003bj21Tg00_dj10Tg008?g00\`'1g00eY#0do"). Qed.
Lemma scF_ENOENT : ltac2:(zQ "20!jsf!jpf@1$1$0").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1g003bj21Tg00_dj10Tg008?g00\`'1g00fT#0do"). Qed.
Lemma openat_errnos_range : ltac2:(zQ "50!na!jv1!hv8!joe!jr9>1e$0>0@3$4$0^1$3@2$2@2$1+1^2@2$1^2+vvf").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##0yh04__x1h12Heh27__arithh34__ffh48__varmaph55__with61ep;3p;1p;2p;5p;4p;7p;8g00_3j3WTg00KZj1VTg00gIj2GTg00A:j1A!s8$jj2=Tg00hSj3PTg00i<j3L!s/$ej2F!se$:j1CTg00MAj37Tg004<j1@Tg00jQj2?!s/$oj1>Tg00kMj1UTg00@0j15!s/$Uj16!tC$Yj12Tg00l8j2O!s/$[j5ETg00m?j1D!s/$aj4;Tg00nLj7HTg00o0j8I!s/$Tj2BTg003bj2JTg0106j2KTg007ej34!s8$bj3MTg011Aj4NTg00_Jj2:Tg0123j2<Tg00S@j2Q!s8$Oj2RTg0132j7S!s/$Vj7TTg00UXR0f0R1'Rp=3P0f1R2g014:P1C;p=9P2g002_R3g014aR4P4g015AR5P1g015aFSp=0%51#5p=1f2R6P3P4P4P5P2P1FTp=8g00cb9W01g016AR7g00OIR8#V,G0g00NjR9#A,=05P01=095L0g016m'FR9%C79779!s&'37%@71?02%>0%U0R7!t:'%58R9#6R:#6R;#2R<#31O08R='9,07%5:#2R:#3/9=,07%6;#2R;!s5,8#5#1#2R>!s9'P!t#+DE587!s%+%D4!sA,P0%28R8#3g017YR4P=C;,07P0P=P4%19#1!s$&2R9#3!sB$FHGI1B75P1P6g008?!v'$8_R5'J1K16=475dg00PZ=M02CNb3b4b5X00A40<1A40:1A40;1A40>1g00cE':!s$%1<821<29'Q[^00P1P6P2O2b2W1X60o"). Qed.
Lemma errno_ret_range : ltac2:(zQ "80!jv1!hv8!ine!na!jg6!jv7!jve!kg5>1e$3>0@2$1@2$0+1^1@2$0^1+vvf@2$0@2$6@2$5+2+k0+vvf@2$7@1$2#k0@1$4^2").
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##70h06__sat1h14__x1h24__p1h37__arithh44__ffh5!sN%0h68__varmaph75__with82Hah91Hh:2Heh;1eh<1zp;1p;2p;3p;4p;6p;7p;8g00AYj19Tg0123j20Tg00@0j1;Tg00S@j27!s8$Uj11Tg018@j1U!s/$^j1=Tg019;j2L!s/$aj2KTg01:>j25!s/$[j2@Tg00KZj1ETg01;;j2h!s/$cj28Tg01<?j3]!s/$cj2YTg003bj2D!s\$:j1VTg004<j1TTg00jQj2Q!s/$oj1OTg00kMj1N!u3$Oj23Tg00l8j2MTg00m?j1JTg01=Dj3I!s/$gj3?!sA$aj4:Tg01>Jj6HTg013Vj7GTg00oTj2FTg0106j2PTg007ej3>!s8$bj3RTg011Aj4STg00_Jj2g!sn$nj2fTg01?Qj3eTg01@4j3`!s/$Wj2_Tg01A4j2^!s/$Qj6\Tg002Cj6ZTg01B5j1[Tg01C?j6C!s/$]j2XTg01DCj2B!s/$mj2WTg01E\j1a!u&$2j7bTg00nLj7c!u3$0j8dTf0R0#;#;p=4g00UXR1f1R2g017YP0C:p=6P2g002_R3g014aR4P4g015AR5P0g015aFbp=2f2R6P3P4P4P5P2P0Fcp=<f3R7!s;+6P2P0Gdp=Ag00OIR8#9R9/00%;8#4!s$+9R:,00R;'7R<P1%18R=#1!s$'R>#UR?%=2R@'LRA%9=R=%9>R>'KRB/5:RC/00X<1RDP11@@BREPDP@PB%E8RF15B2RG1h=>RHg00PZRI/8=RJ10I>18IB[RK[RL10I=RMg01FTRNA]=>2UW8R>10IB\N^8MRMP2g01G01YI='DPJeO1RJPKp-0RNg016ARO#VRP%TORO1Q12RQ%O1RR%N1RS13191M18R8'6,2S131:R:,68,2SRT5<S%J4RUPS!vQ'131I131==I1?R==?18RV!s_$P1PVg01GVP=C:,2S5<S!s\,P7EHR7FGCA1FS5R5P0P6g008?R4g008_R3'D1P06=>43dAR1I2CSR3b4b6b7X11W210IG18GB'7/g6\<^11^2NP0f5R<,5BR4,8B104I'7P<f4O3b3b0b5b0PHPLP>PMPJPKPPPOPQPRP11f18g014:131F9e1==`1V!u'$P5P!tD,%=01_BF15B0'^5>1^11P0P<O1!t+'E\A>1GEP115B6PD!t;8SA<S7TPUA?1=:/6V,2SCA!t50X2N172;10CG[!uN+6RN,09PNP<!uC,%=6/@BP0EZb9PA%[@EC1X?@,B?1W?@EC%a2,B?,0CeW:X;1o"). Qed.
(* [comment removed for export] *)
Definition regU : ltac2:(zQ "20!h8!l7@1$0$1") := ltac2:(zQ "80!na!rd!s5!sb!t1!t6!tc!u3@3$3@2$2$1$0@4$5$1$0@2$7@1$6N0-o0+l0@1$4@2$2$1$0").
Lemma covU : ltac2:(zQ "d0!u8!h8!ud!v8!hg4!s5!hga!hi4!hia!hj8!hk0!kh4!khc@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1 (kr_t_MainOpen ()) ["FPX1"] "p;2p;1p;3g003bj26Tg004<j15Tg004\j21Tg005<j30Tg005Yj14Tg006_j22Tg007ej33Tg008?R0g008_R1'6g01H=g00:BR2g00;N#5R31123g00<Yg01I@3030#4'2=301do"). Qed.
Definition cU := Eval vm_compute in carryM rU kn_mainN.
Lemma cU_knU : ltac2:(zQ "90!h8!htc!u8!ud!hg4!s5!hi4!ki2!ki8@3$6@1$0$1@3$2@1$0$1@1$0$3@3$2@2$5@1$0$1@1$0$3@1$0$4$7$8").
Proof.
vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma path_nonul : ltac2:(zQ "90!ine!kif!h8!sb!t1!kj5!km8!jr9!isd>3a0s@1$2@1$1@1$0#8>4path@1$2@1$1@1$0#8>0@1$6@3$3@1$2@1$1@1$0#8^2@3$3@1$2@1$1@1$0#8^1@1$4@1$2@1$1@1$0#8@1$5@3$7@1$1@1$0#8@2$8@1$0#8Z^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##:Sp'0h01Hh12H0h21li001lh32H1h42Hlh52Hxh61ah71eh82H2h92_Hh:1xi011xh;2Hnh<3Hvah=3_H0h>3_H1h?3a0sh@4pathp;1p;2p;3p;6p;8g00@Uj18Tg018@j1JTg01LNj1GTg004<R0j1ETg00K:j1OTg01M1j1ITg00AYj1;!s8$hj2CTg01NHj1ATg0123j27Tg00S@j2<!sA$hj1DTg000`R1j34Tg01C]j2NTg01Odj1MTg007ej30Tg01Phj2LTg01Q\j2@Tg002Cj6?Tg01R3j2>Tg00MAj31!s8$Rj69!sw$?j6:Tg003bj2=!sA$oj8HTg00@0j1BTg00_3j3KTg01T4j1FTf0R2#8#8p=5f4R3f3R4f2R5f1R6;1231p=3%B2#Bp=6AK562#Fp=2g00OIR7#8#5R8#JR9#GR:#ER;P;P6P;P2%O;R<D3#I%;7P;P5!s>$<D3R=,C;#AR>'7%88#5#5!sh$;,7>'<R>%D=!s=+!s$$;R8'71C:2#A%67#6!s$0;'7X6;R7=4;=g00PZ,N9R9=2:2X6;R?!s=&00R@g008?RA%M2g00\`RB30g01TM,L2=0AB'<X6@RB1@;=34A2:96R=P;P4!u0$<D3#D/78P;P3!s;$<D394;7P;f5R7!s<$!s8%?P;f6R8P;P7P<D3,@;94@BP1P;P?%E;RBP;f9R@P;f8RA!v'$C706A2:9@RD[P6P;f7REP;P8!sC$F90B<P;PAP;PE!s8$G!s8$BP<P0P;p-0P2g01FTg00cERHn1011000002!s%$!s#$X7BRIg01UNRJPCP2E?PH1>D2b1W0P2O1W0A4;?6RDA1;45RCP;f?RKP;f>P<D350BA1;34RLP;f@RMP;PK!s>&PBPBP0P;PBP2P7P2!tL21001!tL%KA1;73RNfAROA1;M<RM51;P2E9A0B3MPBP;!sn$;P2PEP6!sn<0A1;87R7P;fB!tX$OP<D3P6E9A0;8MfC90;EP2fDRM90;AP;fE!t?$O<90B@ROf;94;?RPfHRQ92:9RR]4^5=[X2;!te$90BAP2POPBfF=1;<fIRO92:9^4D^5RX2BfGRR92:9A1;R<!x]$!xH$fJR1=1;<RR90B6fK!t&$M[P2A1;Q<RQ90B<!tU$RO!x,+IPJPR!wS'M!wS-fP=1;<90BCfQ!s0&L!w0$KPNfR=1;<!vW'<!vW&7fSR7!s?$!v$&7fT!v$&U!u~&VA0B@<REfZ!uF$1P^0!um%0BA<!w<$BP<fY92:9f[!sI%D]0X2BfX!uf$4;?<P6W8W3f:R?P2E:b8W1P@!s0$!u1&b!s+&W3P2P5P6O3W3X1DX0=X2BX:;P4P5P6P2O4n2002!xP%!xS%41!xa+000A0B2OA2:91[X2BPQO1P21=BO!t'$4W5P!tO%3!tO41!s+%W0!tO+0W4X5!tND1!tN5GA2:9A!tN$F!tN&G!tN$9W;W>W=X9>P2GHW<X@;W?o"). Qed.
Lemma path_len : ltac2:(zQ "90!ine!kif!h8!sb!kn6!t1!km8!jv1!kne>3a0s@1$2@1$1@1$0#8>4path@1$2@1$1@1$0#8>0@1$6@3$3@1$2@1$1@1$0#8^2@3$3@1$2@1$1@1$0#8^1@1$5@1$2@1$1@1$0#8@2$7@1$8@2$4@1$1@1$0#8^2+hvvvf").
Proof.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["FPX1"] "##:Op'0h01Hh12H0h21li001lh32H1h43Hl'h52Hxh61ah71eh82H2h92_Hh:1xi011xh;2Hlh<3Hvah=3_H0h>3a0sh?4pathp;1p;2p;3p;6p;7g00@Uj17Tg018@j1ITg01LNj1FTg004<R0j1ETg00K:j1PTg01M1j1HTg00AYj1:Tg0123j28Tg00S@j29Tg01Nhj1=Tg000`R1j34Tg01C]j2OTg00_3j3NTg01T4j1MTg01Odj1LTg007ej30Tg01Phj2KTg01Q\j2ATg002Cj6@Tg01R3j2>Tg00MAj31!s8$Rj6;!t1$?j6<Tg003bj2BTg01Ujj7J!u+$hj2C!ti$Hj1?Tg00@0j1DTf0R2#7#7p=5f4R3f3R4f2R5f1R6;1231p=31C62#?p=G%D2#Dp=61C56#?/82p=2g00OIR7#7#5R8#IR9#FR:#ER;P;P6P;P2%P;R<D3#H%:7P;P5!s>$<D3R=,G;R>'8%78#5#5!sf$:,8>'9R>%==!s=+!s$$:R8'8%67#6!s$0:R792:2X6;R?=4;=g00PZ,O9=N:2#MX6;R9!s=&00R@g008?RA%L2g00\`RB30g01TM,K2=0AB'9X6@RB1A;=34'9A2:67R=P;P4!u-$<D3#=/88P;P3!s;$<D394;?P;f5R!s<%<D3RA94;91A;A94@B'9P1P;P?%E;RBP;f8R@P;f7RA!sQ$9706A2:@7RC[P6P;f6RDP;P8!sC$E90B<P;PAP;PD!s8$F!s8$BP<P0P;p-0P2g0!ze%cERGn1011000002!s%$!s#$X7BRHg01UNRIP9P2E@PG1>C2b1W0P2O1W0A4;?6RCA1;45R9P;f>RJP;f=P<D350BA1;34RKP;f?RLP;PJ!s>&PBPBP0P;PBP2P8P2!tL21001!tL%JA1;83RMf@RNA1;L<RL51;P2E;A0B3LPBP;!sn$;P2PAP6!sn<0A1;D8R8P;fA!tX$NP<D3P6E;A0;DLfB90;AP2fCRL90;@P;fDRNf9ROA1;N<50BRNf;94;?RPfGRQ=2:7RR]4^5=[X2;!th$90B@P2PNPBfE=1;<fHRN=2:7^4C^5RX2BfFRR=2:7A1;R<!xi$!xK$fIR1=1;<RR90B6fJ!t&$L[P2A1;Q<RQ90B<!tT$RN!x0+HPIPR!wV'L!wV-fO=1;<90B9fP!s0&K!w3$JPMfQ=1;<!vZ'<!vZ&8fRR8!s?$!v'&8fS!v'&T!v%&UA0BO<R8fY!uF$1P^0!um%0B@<!x/$BP<fX=2:7fZ!sI%C]0X2BfW!uf$4;?<P6W8W3f:R?P2E<b8W1PO!s0$!u1&b!s+&W3P2P5P6O3W3X1CX0=X2BX:;P4P5P6P2O4n2002!xS%!xV%41!xd+000A0B2NA2:17[X2BPQO1P21BBN!t'$4W5P!tO%3!tO41!s+%W0!tO+0W4X5!tND1!tN5FA2:A!tN%E!tN&F!tN$9W;W=X9>P2FJW<X?;W>o"). Qed.
End FPX1.

Section Open.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!h8!ine!kif@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!os4$0").
  Variable tid : word.
  Variable regs0 : ltac2:(zQ "30!ine!mo2!kif@2$1@1$0#5@1$2@1$0#k0").
  Variable mem0 : ltac2:(zQ "30!ine!kif!lma>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
  Hypothesis Hva : ltac2:(zQ "60!h8!ine!kif!sb!t1!km8@1$5@3$3@1$0@1$2@1$1#8?3a0s@3$3@1$0@1$2@1$1#8?4path@1$4@1$0@1$2@1$1#8").
  Hypothesis Hve : ltac2:(zQ "10!ot1@1$0?4envv").
  Hypothesis Hvsp : ltac2:(zQ "10!otf@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!ine!oub!kg5!hv8!jv7@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  (* LPS #38: [main_entry] is over the ProcInput; the encoded form above held the
     pre-revision argument list.  Measured from a farm round, which
     printed the callee's whole expected type and the eight terms it was given at
     U/MainOpen.v:112 -- "The 2nd term has type word which should be a subtype of
     ProcInput".  A KReplay/CDef blob is never re-encoded, so the statement is written
     out (rule 11), over the SAME ProcInput this section builds below at [model0].
     DONOR: U/MainDefs.v:260, this twin's own, already landed
       NEW  @main_entry (amb_of inp) inp mbase (Z_to_bv 64 290456) sp0 rnd tid regs mem
     290456 = 0x46e98 is the UBSAN binary's entry; the plain twin's 291460 is a different image and
     must not be shared. *)
  Hypothesis ME : @main_entry AMB (mkProcInputC [a0s; path] envv fs0 stdin0) mbase
                    (Z_to_bv 64 290456) sp0 rdraw tid regs0 mem0.
  (* LPS 727298f3 port: the launch facts the argv-string bound needs ([path_facts]'s fourth
     conjunct, read off [RefMainEntryN.str_fits_N]); both are the run's own launch clauses,
     as RefMainEntry's [KnowProofs] section takes them. *)
  Hypothesis Hvl : valid_launch (mkProcInputC [a0s; path] envv fs0 stdin0).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) (mkProcInputC [a0s; path] envv fs0 stdin0).

  Let model0 : Model := MainDefs.model0 tid brk mbase sp0 lim (mkProcInputC [a0s; path] envv fs0 stdin0).
  Definition ENV : ltac2:(zQ "40!h8!ine!ko8!kif>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!ine!ks9!kt5!lh4!lm0!kif\4vals@1$0@1$6@1$1#k0@2$3@1$4^1@1$2@2$5?3a0s?4path").
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  (* LPS #38: [p1] is over the ProcInput and the drawn entry (U/RefMainEntry.v:124-125); the
     input is the one [ME] and [model0] name.  Shape donor, statement only: the 75d69e00
     port of boost-beast/http_request (its lib/Ub/MainOpen.v, the same [Let pp]). *)
  Let pp : word := p1 (mkProcInputC [a0s; path] envv fs0 stdin0) a0s path envv rdraw.


  Definition regA_w : ltac2:(zQ "50!h8!s5!ine!na!kif@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ine!na!kif!s5!sb!t1!t6!jve!isd!kg5@3$4@2$3@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$8@1$0#k0@2$7@2$9@1$0#k0?3sp0+u0+r0@1$5@2$3@1$2@1$0#k0$1").

  (* [comment removed for export] *)
  Definition frameA : ltac2:(zQ "30!ine!kif!lma>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "h30!ine!kif!h8!lma!isd!ln2!hi4!lqf!lvf!mjc!jve!kg5!mkf!hv8!ml4!mme!mn4!mnb!kne\1M>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$d@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$4@1$0#k0+ttln4>1i$c>0@2$f^1N8@2$e@1$1@1$0#k0\1w@1$1@1$0#k0@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$h0@2$a@2$b@1$0#k0?3sp0+n8@2$h1+8@1$h2^3N8@2$5@1$2@1$1@1$0#8@2$7N8^1").

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
    pose proof (main_strN (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 290456) sp0
                  [a0s; path] envv rdraw tid regs0 mem0) as MS.
    repeat lazymatch type of MS with
           | forall _ : word, _ => specialize (MS brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hvl | exact Hlau | reflexivity ];
               specialize (MS h); clear h
           end.
    pose proof (str_fits_N (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 290456) sp0
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
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xef330) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x46fe4) mem0 (seg_rom RSEGS)) model0) T.
Proof using All.
    intros T HA. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_regs_ok (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 290456) sp0
                  a0s path envv rdraw tid regs0 mem0) as HR.
    repeat lazymatch type of HR with
           | forall _ : word, _ => specialize (HR brk)
           | ?P -> _ => let h := fresh "Hd" in
               assert (h : P) by first [ exact Hva | exact Hve | exact Hvsp | exact Htid | exact ME
                                       | exact Hvl | exact Hlau | reflexivity ];
               specialize (HR h); clear h
           end.
    pose proof (main_know_ok (mkProcInputC [a0s; path] envv fs0 stdin0) mbase (Z_to_bv 64 290456) sp0
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
    eapply (rz_run_lf RSEGS FUELM STOPSM scrA 0x46fe4%Z sr_main kn_main 40%nat (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA) | exact HR | exact HK
      | apply Forall_nil | apply Forall_nil | reflexivity | reflexivity | ].
    intros R M HR' HK' EQM LF. rewrite cA_knA in HK'.
    change (s_pc (fst (fst rA))) with 0xef330%Z. change (s_regs (fst (fst rA))) with srA in HR'.
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
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["Open"] "##2Th01bh12b1h22b2h31nh41Hh52HRh62P2h71Rh84valsp;1p;2p;3p;5p;6p;4g00@Uj16Tg018@j1ETg01LNj18Tg004<j1OTg00@0j10Tg02=3j2NTg00A:j1G!s8$_j2MTg007ej31Tg02>aj1DTg02?cj3I!sS$Yj15Tg03==j3?!s/$`j2=Tg01C]j2CTg01DCj23Tg03>aj2<Tg00S@R0j2HTg03?@j2;Tg02g8j24Tg003bj2ATg00B7j1@Tg03@Gj5:!sy$?j6>Tg03AIj3LTg00>ij1K!sy$[j4BTf0R1#6#6p=2g00UXR2g00PZR3711p=9%01#0p=F!s-$#0#0p=J!s2+!s$'p=7g00OIR4#6R5#2R6#6#2R7#ER8#8R9#O%05R5#ER:/N9f1R;g00Nj#G#GR<'Mp,2ppR=519f2R>#Dg037cR?;I;%06#5g01UNR65?:R@,=>RA%04R4#0RB#6#2#5RC,C8RD519%65#5=?:6RE,=>RFg03AmRG519RH%0!sB'5,=>RI=19=RJ%24!s<&6,=>R:,38g03BgR4'<#9RK'HRL'HP9f3RM#DRN1;?@'4A191DX091A9D%@C,4N=19DePAPNP?P>P@P1D:E>PHPLP91;?E,4NA191GX09g03CnRL%81RH%8;R@P0%8>?1;113M>13M;512R0[13>;13>1512%8M?1>;[RAf4#8?1M>\0AL>;1P1n20010!s#$12!s-%0W2W1W3PA^2@^1H^3LP1P8%FB#J#7!s$-2#0#F!v^$B,C8PG138G,A2O4b4%@B!uJ%GePF!uJ&E!uJ&JPK!uJ$5!uJ&=X09P;%K<!sX%=ePI!sX&5!sX&91;?6,4N1381/<4#9!vX$23%67#2!s$&5R7,C8,38!sG$d%@7,4N!s5'eP:!sy&6!sy%CBCBCBW5W6W7W8o"). Qed.

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
    (forall R', getr R' 1 = Z_to_bv 64 0x47038 -> getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
                getr R' 4 = Z_to_bv 64 0x10ebf8 -> getr R' 8 = Z_to_bv 64 2 -> getr R' 10 = Z_to_bv 64 0x10000 ->
                getr R' 18 = pp -> getr R' 20 = Z_to_bv 64 3 -> getr R' 21 = Z_to_bv 64 0x10000 ->
                realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xdfc04) M (seg_rom RSEGS)) mo) T) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (Z_to_bv 64 3)) (Z_to_bv 64 0xef334) M (seg_rom RSEGS)) mo) T.
Proof using All.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["Open"] "##Fwh01bh12M'h22R'h32EMh43EQMh54Elogh63Epch72HCh82HKh93HK'h:2HLh;2HRh<3HR'h=3HR3h>2Hhh?3Hhih@5HlazyhA3HlohB1MhC2P0hD2P2hE1RhF1ThG2_HhH1lhI2mohJ4valshK1zp%0p&0p;1p;2p;3p;4p;5p;7p;6p;Og00@Uj11Tg018@j1UTg01LNj1XTg004<j1FTg00@0j12Tg02=3j2pTg01Voj1YTg03MYj1gTg00m?j1dTg007ej30!se$\j2HTg03NPj1aTg00K:j1RTg01Mhk20!sx%_j2TTg02>aj19Tg02?cj3WTg02A1j4[Tg00AYj16Tg03OHj2:Tg03==j38Tg01C]j24Tg01DCj2STg01:>j2cTg02DGj1bTg02EKj5JTg02FLj2MTg0123j2`Tg00B7j1CTg02g8j27Tg003bj25!t:$kk701Tg03Q3k100Tg03R8j3~Tg03S?j3^Tg005<j3QTg00U;j3PTg03TBj2zTg02UKj5yTg02VWj7xTg02W`j4K!s\$Yj1uTg02X@j3tTg02YFj3qTg02ZUj2oTg02[6j1nTg02\=j3VTg00T6j1m!uk$?j6@Tg00>ij1Z!vw$Zj1lTg00G`j2kTg02kkj2jTg01A4j2\Tg02_gj1iTg02`nj1rTg00C>j3sTg03ULj3hTg03VXj6v!w9$:j13!w0$`j2]Tg02GAj4fTg03@Gj5eTg03?@j2|Tg03W]lO}Tf0R0#1#1p=E%30#3p=_!s-$#3#3p={!s2+!s$'p=O%20#2p=G%20#1p=A%1!sh$#1p=L%1!sB$D%10#6p=<f3R1f2R2f1R3'];00p=;!sf$#2#2p=I!sb+!s$'p=Bg0272R4g039oR5P3P0Cfp=Ng01UNR69830p==P1g03X`R7P2P3P0Dep=>f7R8f6R9f5R:,|7'7f4R7P11]23P0E@p=?P0P4P5g0313S00g032<S01g03YgR5P3g03[0R;g00R9R<P2P1P7P:P9P8f8R=f9R>f:R?f;R@f<RAf=RBf>RCf?RDf@REfARFfBRGfCRHfDRIfERJfFRKfGRLMO}p=wg00OIRM#1RN#1RO#1RP#1RQ#ERR#URS#XRT#F%2NRU#URV/pTRW%UP#X#Y\TRXg03\8g036b%YT%g3%dT301HTTRY#F%a2%RY30g0289202T9g00NjRY#_RZ#_#{#O!s$%R[301T8Yp,3sp0R\50T1T=Zp,2ppR]50T%9>g037cR^;W=P4%9?P=P<C[PTP0%6MR_P61:V_d58V%GP#A#L#D#G#E#<R`,4SRaC;PTP3%6NRN!sQ$Nd58V1SS\Rb%1RRR#6'c,4SRc!sO$2%6ORd!sO$d!sz$2Q#G#D!sz$I!s|$Q,4SRe!sS$1%6PRP!sS$P!s|$4SNRf!sA$7%1URU#6Rg!sE$gd58VRh%1R#BRi#6Rj,4SRk!sQ$:%2O#<RO!sO$Od58VP]!s?$9%<UR:!s=$:!tZ%MRM#6Rl,4SRm!sI$8%2U#6RU!sK$U!sb$kC;p,2fxR6P=%1M!u-$A#E#L#A#<Rn,4SRoPG%b4RpDJ/MF/NE[!s#&^2Wp,4SPlo!t9%2#I!s$$E#L#B!s$$</`b!sI$hi%Ei!s=,,`b%9CRbP^PBPm%ClRlP717bl,5TK01&00h=~^lA^Bhm5WbP6%DM#G#A#D!s&&A#<RMP[g00:BRbg00;NRh#FR^1Hb^Rig00<YRqg00W?Rr3QRs3QRtAPb^sRsAPiqrRug00Ma#FRv1Hv^Rwg008?Rx#FRy1zr<Rz3QR{7Q^R|APv^{R{APwyzR}%9DR~PBPp1=VgRg=^CmPAP@1HiqR@/5rP4Q00g008_Q01P5PMP;g00V6R;#RRMP<P[Dy%RhR[FxPiPqPbP^PtPsCKPuCK50@d1HwyR@/5z%utRz%Rx7t<PwPyPvP^P|P{CKP}!sP%P0P7Aq4B~,ohRhPhP?P>%9F%nt;W3P4%9GP3P|C[%9H?VFz90X2g00UXRH%mtRt;0nR|A0^s[R[%F;R;?0zMRsP6P714StP1P!x`+PHPnP6P=14S0P8!s>%J/NIXKHPX%9L?VJzA0X0KX1XP;PMfHRM#9RL?VK0=0XKXH;15XJPzP0E@P9P1E@A0X9JPXPKP6P>PoP0!s|%K/NJX1XPAP=PTPL1=V_R_A0T0aX0T15Ta%C`,7L=0TaeP=P_PL!s+$9C>G?!sW&N!sW%cX0TRaPT%ZYR`%lRRR'kRA,jLRJPaPTP\1SS0/\R,4S=0Tc!t,%c1TMYPEE@%iA,7L,SS%rA'\!sJ&eA0TJceg00On%CR7s`,7LAhL`RE@!t[:dRdA0T0e!t,%e%CQ!u4%eeP=Pd!sW$d!sW0PRPA0T0f!sW%f%CN!sW%feP=PP!sW$P!sW,PgA0T0kX0TRP15Tk%Cj!sU%keRkP=Pg!sW$g!t00OROA0T0]X0TPD%ZZ!sW%]eP=PO!sU$O!sU0:R:A0T0m!t_%m17Ll=0TmeP=P:!sU$:!sU0URUPPPkP=PU!sD$U!sD%O9P8P0E@b3PtP2E@X5sXG[X6|g03\nEvW4W9W<X1XX2WMHwb=b?bAW7W8W;WDWCW:W@W>WFWIWBWEWJo"). Qed.
  (* [comment removed for export] *)
  Definition regF_w : ltac2:(zQ "50!h8!s5!ine!na!kif@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ine!na!kif!s5!sb!t6!isd!t1!jve!kg5@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0@2$8@2$9@1$0#k0?3sp0+v0+h0@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+hgurl4+4@1$7@2$3@1$2@1$0#k0$1").

  Lemma seg_F : forall (e : Z) vals R M (mo : Model) T,
    m_halted mo = None -> m_vm_lazy mo = [] ->
    (1 <= e <= 4095)%Z -> scF e ->
    length vals = 40%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = pp ->
    regs_ok (ENV vals) srA R -> know_ok RSEGS (ENV vals) M knA ->
    (forall R' M', getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R' 4 = Z_to_bv 64 0x10ebf8 -> getr R' 18 = pp ->
                  frame_mod M M' regF_w ->
                  realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x47274) M' (seg_rom RSEGS)) mo) T) ->
    realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (Z_to_bv 64 0xef334) M (seg_rom RSEGS)) mo) T.
Proof using All.
ltac2:(KReplay.run1z (kr_t_MainOpen ()) ["Open"] "##qzh01bh17__arithh24__ffh38__varmaph45__with51Hh64__x1h72FRh81nh92Hah:1zh;3HL0h<7__sat41h=!s0&2h>4cstrh?1rh@2M'hA2R'hB4__p1hC6!sL$0hD!s/%1hE!s^&3hF!s0&4hG3EQMhH2H0hI2HChJ2HKhK3HK'hL3HK1hM3HK2hN2HLhO2HRhP3HR'hQ3HR1hR3HR2hS3HSChT2HehU2HhhV3HhihW5HlazyhX3HlohY2HrhZ2LFh[1Mh\2P0h]2P2h^2Q0h_2Q2h`3Q40ha1Rhb2RFhc1Thd1ehe1lhf2mohg1ohh4valshi5vals1hj1xhk1yp%0p&0p&1p;1p;2p;3p;4p;5p;6p;7p;8p;<p;Ng00@Uj11Tg018@j1pTg01LNk10@Tg004<j1_Tg00@0j12Tg02=3k20wTg01Vok10BTg03MYk10hTg00m?k10>Tg007ej30k106!sm$\j2]Tg03NPk10TTg00K:j1KTg00AYj1BTg0123j24Tg00_dk10rTg01Mhj2@!tD$_j2Fk109Tg02>aj17Tg02?cj3kTg02A1j4gTg03OHj2jTg03==j3J!s/$`j2VTg01DCj2ETg01:>j2`Tg01C]j2!sw$B?j3DTg02DGk11>Tg02EKk50MTg02FLk20KTg02GAk40ITg01E\j1CTg00MAj36Tg03^5k20zTg03_>k10vTg03`Ck20DTg003bj2=!tA$?j63Tg03aHk70sTg01YLj3WTg03bRk20LTg03cXk20CTg03d]k80nTg03KMk20m!sW$5k20lTg03egk30kTg03g2k10jTg002Cj6YTg01^CR0j2nTg01;cR1j2<!s<$[k10fTg00jok10eTg00kMk10d!wI$Ok20?Tg00oTk20cTg0106k20b!s0$bk30aTg011Ak40!vb$_9k40<!tQ$Vk40:Tg00>ij1vTg02g8j2;!w]$kk70^Tg03Q3k10!xy$R8k30\Tg03S?k308Tg03hak30[Tg019ak207Tg00ENk30ZTg03j1k20!uR$h:k10XTg01NHR2j1MTg01i@k20!xY$ick30UTg01jej4!w+$]^j1|!v&$;k205Tg01<?k30!z/$jQk20STg01>Jk60RTg00l8k20QTg01=Dk30P!s0$gj3qTg00S@j2RTg03k?k70OTg03lFk603!{7$:j18Tg005<j3!w#$U;j3aTg02UKk50NTg02VWk70WTg02W`j4N!sU$Yk11=Tg02X@k31<Tg00B7j1iTg00ZNk31;Tg00[Uk41:!tA$gk41!{#$YFk318k41!yr$n7k10!w>$n_k315Tg03oGk314Tg0402k30HTg02ZUk2!~3$0T6k1!~b$40ak30GTg041<k30!t]$[6k10}Tg02\=k300Tg02]Mk20|!}d$3k30{!~1$Zk10FTg00G`j2~!sC$JS00k20ETg02^\j3!vp$A4j2!wI$@4j3oTg02_gj1!t0$`nj1uTg01kLk20uTg02b4k20xTg02c;k70yTg02dGj1!tB$maj4!},$?@j2wTg02kkk20tTg00C>k30~Tg03ULk310Tg03@Gj5x!y0$@m<02Tg0132k70JTg00nLk70p!{e$0k816Tg02h?k4!#3t$m2mN0oTf0R3#2#2p=Z%2!s0$!s$,p=df2R4f1R5/43'Rp=l%83#8p>0A!s/$#8!s3$i!s3+!s$'p=mg00NjR6,F3p=L%23#1p=>!t1+p=r%1!s:$f%13#Bp=G%13#2p=b!s>$#1#1p>01!s3+!s$'p=Ig008?R7g008_S01703p=cg0289R8g00UXR9P0P2P1g028XR:P6g00PZR;f3R<P4P5P3N<02p>0g20?93p=AP9P5g01GVP3Czp=XP5g002_R=g014aR>P>g015AR?P3g015aR@K0Jp=SP8P!t:&P:f5R:f4R1P!t21_14;5/R3p=TA0953p=O!s\$3P2P5P4P<!sb$6R2f7R0f8RA!s^$=t14;3p=:P4P=P>P>P?P5P3K0pp=H!s:-!u-%7YP3CzP!tc%?P<!sE+!tW$L16p=hg001AR@?053p=^g02n@RB?e93p=UAaB93p=[1R53,R4p=\P@P5P3g00XERCH17p=yP4P9P5P3CNp=PP3g0272RDg0313S02g032<S03g041WS04P5g042_S05g043gRE!ua'P2P0PAf9RFf:RGf;RHf<RIf=S06f>S07f?RJf@RKfARLfBRMfCRNfDROfERPfFRQfGRRNN0op>0qg00OIRS#1RT#1RU#1RV#1RW#1S08#1RX#pRY$0@RZ#_R[%2TR\#pR]00wZS09%pV$0@$0B\ZR^g03\8g036b&0BZ&0h5&0>Z301]ZZR_#_&0T4%K_30%BSR_/40%ZSS0:#2S0;#dR`#BRa7l0&0rA1@ZA&0A6Rb$0A$0i#m!s$%Rc508%LFp,3sp0Rd50Z1FGbp,2ppRe50Z%7HS0<g037cRf;kGPD%7IRgPGg00R9RhCgQ09%BTRTg01UNRi1j]Td5J],V51EYdRj%1XS0=#B'`,9YRk50Z%BURlPi1j]l!sP%4%ZW#>#>#ZS0>#2#r#f#GS0?,9YRm50Z%2U#GS0@PiQ0@,j]!s\%<=0Zeg044o9DK<PDg039oS0Ap,2fxS0BP:%ZV#>#b#f#Z!t,$GS0C,9YP1&1>DS0DI0M00KKPJH0I[[[[^@^]Ap,4SPloS0E%r`S0F#f$01#I!s$$GR`/4j!sH$hiS0GQ0=#1!sG/I#GRV,4jPK%CL%KZRU56ZRnp,3a0sp,4path+0z$0vRoPfPJP8Pc20D3f#cX88Q01,=7Rp20Dcf#cd1@ZKP0E3P1K0sAWZKn$0900Lo?kfJPDPL%CM=6ZURnPoPJPh!st%C3h!st$Pp20Cch!sn%LPAE3P1L0nPDAWZL!sp'PJPhCgP81@ZMRo%CORn!sx$q9WZNRr/F3=0ZnX88RsP820mo6PsPZ%CNRs!sN$t#LA0Z3nX0Z1=ZsAWZMtRn20lo6'FB0kMt6E3Po&0joEYPcPFEY1Fnc=0ZsPZ%LNA0Z3dX0ZPF%LrRrPNPqP6P8Pc1n63X881n6c%1\Rq#1#GRs,<;Rn1=9;PcPs1=9sS0HH0gg016ARo#KRt%_oRo&0f9S0I&0e9Ru&0d9Rv20?9;Rw%AsRx'X'S20cv?RyP3P4Pp20b34#cdB0a9;5H0`Rpb2b3b4PnP3b1H0<1@ZNPGE3H0:E3A0ZrdPZ1FObA0Z3eX0ZS0JPF%CP!v3$r9WZO/FbRnPOPrPb!uF%b!uF%bc1<TsRrPbPT1=9TPcPsQ0HJ0_PtPoQ0IPu%ATRz/Xx,SvPyP!tY'r!tY,OPH!tY,ne%CQ=6ZU9WZPP[%73R[PfPP%CRRU%vcRnP:P<1;[n=0ZUeK0^%BqRq!}7$qd5J]Rr$0]>0\fnB08PrU5k[g00MaR[%75Rr>0[DP%BXRX-07TRU/`aRf1`U_Rx60ZnPhPDPrPPPnPfPxPZfHRh#CR{1EY3R|,4f?l|xX0Z20YhK1EY{,4ffIS0K#CR{$0X1EY{Rh1<hU'TQ0K,@ZRh=08c%MhR}/OsR~&068S0L&069S0M%M5%M3'OA085320V5340UXk8Xj8S0NPhP}1=9}!vt&M9tPKCsP~fJS0O,@ZR~#|%M~#:205TXS0P1<;TR~%:X1<;US0Q[[S0R%:TR}g01FTRhB04TX5UW9S0S%:U\h^9}S0T%2\#GR\-05TS0U%:\207T\RX,<;[\~S0VB04T\5VhX9}S0W%:X!s`&Xp-0R}PtPo20S95S0YPuPvPv!#;f'<J0R20Q9SRSB0P9zYRz'X,Sv5Hv&0>>S0ZPv%Aa9q9z=?vSRaQ0Z%A_9q9z9?vS9HvaChCh!yP,X69WB1<3U,R514f514f4?l4x[[^69^B}P3fQS0[#C,EYR}#:P}P0PAO4b1b<b=bEbFb>b;bHb51F5cP1E31;rn!sS$!xM$}xeK0OP:J03!xy&ECgRrePrQ0BQ0:#b#Z#>#b!s&&>#GS0:%8cS0\g00:BRrg00;NR}#_Rx1]rxRfg00<YRag00YHR_3eR>3eR?Aarx>R>Aafa_S0]%_[R[1][xR=%_7Rhg00^2RX3eR\7exS0^Aa[x\R\Aa=hXS0_%74R~PQQ0DAJ]qi>08R{PPPO1]faRO/=_PDQ02Q01Q03Q04Q0:Q05g00V6#KPEQ0\I0N%K}R_K0WPfPaPrPxP?P>CNQ0]CN50Od1]=hRO/=X&1=?RX%K781<EP=PhP[PxQ0^P\CNQ0_!sT%P5P3Pxg00\`ROg00]@R[g00OnRh%i;R=81;nRnQ0F#r#d!s$&f#I#b#BRE#iRrH1:Ra=6}_RfPDPR%7<P3H19XexRPP}B18DQ~RqPaP_PZP{Q08#p&0;319Y;R{$0;615h814Y19YE60H[=07OX0ZPK1F4cP:E31;~n1;~r!sC'ePDPQP~PaH13e212}qRqJ03P>A0x>fRfA0x\_R>&11?R}Q0C'ORa1Rf>R~g0464RQ40GRO40=E3PxP_PPPqP\B0Gf>OE3PNPMQ09%71&0}?;k5PD%7:P5Q0^Cg%72Q0O<00X90^4%7000|XP9Q0CPDQ0AQ0BP219Y3RDP:Q0DI0MfL+0KfKH0IX:9B0{@3CQ00PBP9%v6R6Q0;$01R?$0FRM'~%BWRWCNRN/^5PBP9Q0>#1!zl$>#GRB,~=PlCNR=/^5g00cERO+0EQ0<%U4%[43QP31^N4P@PNQ06#7R>%U3Rf%[3R\3QX?@PZPd15|MRq1<qU%:WRP15qW/4U3\'TX0ZfRR_,@ZRx!#5S$xR7/OsR[Q0LQ0MQ0NPxP71=97!#50+Q0KCsP[fSR[,@ZR7#|%M7Rx#:Q0PQ0RQ0SQ0TQ0UQ0VQ0WQ0X!#9W$YPuPv%AV9?vSQ!#3S$`=!s2%%AM9o9SRr9?vw1Xrz,Sv%AWRn9?vwAo9rn=?vz5Hv!s%%!#3m3143V14`5154MR`1<`U15`W/4U7\P'T[[^69P3PjQ0GQ0EO3!#3g0%LIQ07E3%UNRP#},;g,EY%uP'5!sq%%[NRN#:15`N!vT&eAQgPNeP<P3EYW5P3O11^=400EOQ001^=<PO%U1%[15Q>P31^=1P@P=%7JR1?Qf\X?@P9P;153BR\1<\U%:lRf15\l!w]':9!vj/!#=7,B9o9wR>!vF%>!vF%lR4!vF&>4!vF0!vB,15;BR41<4U154l!v7$f'TP3b1bCbD1EY{R{!t@8A?vww1Xwz!#8W$!sx-4;;Q0Q'R!sk'-0u;RzE3Q07#7Rw%U=Rf#}';!vk$f'5R>1<>U%[=R=#:15>=!vk,wf=eP:!vk,PO%U2%[25Q1P3n010!s#%X5OP3O1n20!s9'2110!s3&!s`%!sB51000WYX?@%7A00xCR@eP@%7FR@fMROPCPXg047;P3P5K0yB00@OX1]Z9RC%{@'y5DOP^%7GROfNR@<00XfORXQ0<#{,yC7D3Xg^P3P2P<E3%{O,yC9D@2PZ%LHfPR@19Yq=PZW15{B,9Y=PZl%KCRB56CRq56C7DAX0ZP3PdQ06EY15jMR2!sO%WRO=6Cq9DX0P9P{Q0[19Y\=PZl=6CB96CO7DFX:9P3P;PzEY19Y4!sD'R!sF$9D@AA087c1OxsR8!~0,7Px1=9x!~0/OCsP8fT,@ZR8#|%M8#:!}x99%B?R?#A9q9Sg014:PrCz!#D_/X691`3?153M'O!}0&O1!}&&>b;1`j?R?/O2P9P2APZDW!uG$D[HX:9P5P?P3E319Y?=PZ!sA&_GPRPIPHPZg048>RHAJ]TiRT'w,;1A0Z3kX0ZRRPZQ0=$0FR_,~6RB-0t1RCPR!#5Y%_,9Y=0Zk!#JQ$k%LJPLE3%}B,;1!zc$B'5!sI&eA0ZCke%i_:0~h6,;1B1016_E31VITP1PHPIPTPGDxE3PZAJ]liRl,wH!t\&m!t1%mQ0?#i,;1=0Zme1VIl!s`&l!s`'Q0@=J]iRi!sb%Q0JPK%vb!sY%ee1VIi!sY&i!sY&3O6b7b5b7!s$&bP}B0=a~QE3WZWGWKWPX@^WANH0qbMbRbib_b^b`bLbQbVbXWIWJWOW]W\WNWSWTWWWUWcWfW[WaWhXd9o"). Qed.
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


  Definition ENVU : ltac2:(zQ "40!h8!ine!ko8!kif>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!ine!kif!t1!ks9!kt5!lh4\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  Definition regU_w : ltac2:(zQ "50!h8!s5!ine!na!kif@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ine!na!kif!s5!sb!t1!t6!jve!isd!kg5@3$4@2$3@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$8@1$0#k0@2$7@2$9@1$0#k0?3sp0+o0+l0@1$5@2$3@1$2@1$0#k0$1").

  (* [comment removed for export] *)
  Definition frameU : ltac2:(zQ "40!ine!kif!lma!mo2>1R@2$3@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "h30!ine!kif!h8!lma!isd!ln2!hi4!lqf!lvf!mjc!jve!kg5!hv8!mob!mp0!mp8!mpe!ml4!mo2\1R@2$h2@1$0#5@1$1@1$0#k0\1M>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$4@1$0#k0+ttln4@2$c@2$h1@1$1@1$0#k0\1w@1$1@1$0#k0@3$6@1$3@1$2@1$1@1$0#8@4$8$9^2@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+k0N8@2$5@1$2@1$1@1$0#8@2$7N8^1@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+k8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+9Kv$d@2$h0@1$0#5+9@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+l0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h2Kv$d@2$h0@1$0#5+h2@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+l8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h3Kv$d@2$h0@1$0#5+h3@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+m0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h4Kv$d@2$h0@1$0#5+h4@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+m8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h5Kv$d@2$h0@1$0#5+h5@2$c@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+n0N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h6Kv$d@2$h0@1$0#5+h6@3$6@1$3@1$2@1$1@1$0#8@4$8$9^1@2$4@1$0#k0@2$a@2$b@1$0#k0?3sp0+n8N8@2$5@1$2@1$1@1$0#8@2$7N8@2$e^2@3$f@1$0#5+h7Kv$d@2$h0@1$0#5+h7").

  (* LPS 727298f3 port: written out (rule 11g), restated over the revision's
     [cat_argv_ptr] (the drawn stack top and the exec file name).  Text of
     boost-beast/http_request's lib/MainOpen.v [seg_U], applying RefMainEntryN's lemmas over
     their current sections. *)
  Lemma seg_U : forall T,
    (forall R M,
       getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 1108984 -> getr R 8 = Z_to_bv 64 2 ->
       getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
       frame_mod mem0 M regU_w -> frameU R M ->
       rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0)) ->
       realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 291196) M (seg_rom RSEGS)) model0) T) ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 290788) mem0 (seg_rom RSEGS)) model0) T.
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
    eapply (rz_run_lf RSEGS FUELM STOPSM scrU 290788%Z sr_mainN kn_mainN 40%nat (fst (fst rU)) (snd (fst rU)) (snd rU)
              (fst (fst cU)) (snd (fst cU)) (snd cU) (ENVU vals) mem0 (seg_rom RSEGS) regs0 model0);
      [ vm_cast_no_check (@eq_refl _ rU) | vm_cast_no_check (@eq_refl _ cU) | exact HR | exact HK
      | | apply Forall_nil | exact Hh0 | exact Hlazy0 | ].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. unfold sc_denot. cbn [branch_taken edenot ev ENVU]. rewrite Hac.
      unfold bv_eqb. rewrite Uac. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
      apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R M HR' HK' EQM LF. rewrite cU_knU in HK'.
    change (s_pc (fst (fst rU))) with 291196%Z. change (s_regs (fst (fst rU))) with srU in HR'.
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
