(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, lemmas added for the revision. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RegsEquivM () := KReplay.lz_vm "#%RyC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_ind!sB88eq_trans!sD87f_equal!sa<ind_r!sD29Datatypes3fstK!sC+7Numbers7BinNums8positive02!sKG1!sK=1N02I45stdpp9bitvector;definitions2bv00c79OSSVerify6Proofs:boost_json:fuzz_parse3lib:RegsEquivM8regs_eqvC13~~~K!t8D1I!vN72eq00!vh83not!xTA3Sem7reg_get!xR<sym!vgG3!vg>Z!w,/!t,-4True!sB:!uN#1!vz[9f!v{1!u};?!s<22Fs4path!sVN2Fs!zh=appI!sqJ>!wX$!sE+=ac!s?#_report!xP#!smI5State7PipeBuf!~CI6bv_eqb!sSI9!~p$_set!vCN9!t0%_eqC8!x@N3Lib6M!uH$@!ze&!tG#_same!xG&!suS8PropExec;!ta&refl!y;'!zE69False!#5?#!u0ZA!u0/other!t=%I!yL;4bool00K!sFA1!sFB2!#3473and00!sA85!u`$!sC:!}`%!#5B[;!uz-!utB6option!{X=!#4i+5is_x0C!#67?!xU#unsignedC56Stdlib6ZArith6BinInt1Z3eqbK!t=D4core01!tfE6c_regs!sOE4rge!#7IE2w!v'F7c_f!tDJc_pc!u<Hfcsr!ueJsvK!z-<!#7m[8!w8#!#7lD!vo/set!t<[<!#9&&!zd,!~RT2Nd:and_elimF5!{Q'!ypI!xSF4f!uV^=f!uW6!ynEwith!yGH9!sP$!yJI!sR%!yM#!yvFaccrue!sOBFpu;fflags_bits!~J=lor!#39@7Z_to_bvI!t?D6!t?%!x$G6fwrite!w6Fnan_box!xT\!|B'_f!#6k,!tD?5Instr4ffmt!#8L-!#CL5!u^F:inval!~o7!#8142!sHD1!wpA9bv_conca!#6CA!#@J&4sext!syA6bv_add!#;/[!wD+mk!#IN&!wBE5i!s+#01!sRN2!sRN3!uiE!#JI#!v6Dnd!zTer!zT+!#MO\get!#MO-!v#L4!z~E<branch_taken!#>RD3eff01k!u@Z7eff!u?#01!uAT5!{XJzext!u=J7i!u=c0!u=%!v,d7!v,T6!xHE5low32!v&J8!z[[C!{O+!#5_+!v4j8!v4T7!v4Falu64!szN8!sRN9!sRN:!tzI3!#5ON;!sRN<!sRN=!sRN>!sRN?!y:d3!y:G!{L+4!t>d4!t>P5!#A5Emul_div!vTNB!sRNC!txJ6!v8d5!#;'`B!#3N'!#GP+!~]SD!sRNE!waFamo_val!s|NF!#^Y;4negb!tBEAcsr_!#G`#_illeg!tLC!x/+3!#YU<prod!#FIF9!tJ#slic!#I+E9!sN$!#dv$!#A}>5bv_or!svLse!#=SJ2!zod6!zop!#Om#!sw`!#Gq+if!#<0i2!|QTG!sRNH!sRNI!sRNJ!#jx?2!ycFfp_form!#M=B!#R1$p_neg!sOIfma!xL[?!#Q]+!#Rw$!w`SK!tqIadd!sOIsub!sOImul!sOI!#:dPL!s{E7!tu#qrt!s|NM!#7}Eunbox_!#aoE8sgnj!#8PQN!uME!z]#minmax!s~NO!s~E5fp_eq!sNIlt!sNJe!trNP!szE:fp_convert!vGIof_in!sRJto!sRI8int_wrap!#^s<!|+#!sC;7testbit!#>&<and!se=6shiftlK!#=F@1!u=E<round_scaled!v@Iencode!#wf<snd!x^NQ!sRNR!w]F!y2#lass!s}NS!}|E4exec!#@4@:bv_extrac!#n\E;amo_al!#pp@!xS%r!sF<4lan!wzF>rmode!{k#field!$'B?!#q_E2w1I!vzM0!sRG;!#\-%co!#vg$!t+Fmsize!sRC!#Co'!szIaluop00K!sRM!#b[N@!sRNA!uzIul!t~#!sRG6awidth!v#Kmo!t#K5csr!sRLfma!sRE!#9+#!zq$!uQJfari!u~Lfsgn!sSK9f!#<P$!t'Mcmp!sSK7fcvt_ty!z-I!#n#$1!sQM!$$X,6Floats9Spec!s1$:spec_f!s1#!uOKmvdir!$$Y\6m!$2vU!$1S17ms!#~`?!seB8ms!#~&@!sfB9ms_pc_val!sgZ>ms_svc_pending!u|`!#xP<!seF!#yc>!seB!x6#mem!sd^rom!$#Qeym!#S,`!#}l-!sr'!$$E`!#h6%I!v8Y=machine_state!$9oL!sm2Cinterp_eff_!$:i$es!#Zq<list!$5H>!sF$!$,]\are!~Se;!#:U#_byte!}o[=ov_read!sk%I!}s[!wg&resul!$>YM6BvBase@le!tN%_to_word!uCZ<!$@0%val!$'c<!sjB?!y1&d_range!#GP;!v1R2!snj3!snj1!{@B2!~Oa3!{>`8store_ok!y^R=!$05#!yc'!y[[!#gB$to_me!#74[;!#aV%!$C+#!#\v?!}VC!$HC01!#4_;3nat!#5q[=memory!#5m%I!#Lr>!$@kA4BvWf!#;H^eg!w:[:!se%_!$'MC!v'D!#9e/1!uDZDdecode_exec!#9f'!{w[is_ecal!#a]A7D!tA$C:!tI&any!sWIBis_!x3$ed!#o{&!wL[9ms!#:y/!#?k[!vV$!|Q#core!sraG!#>85!#<kc=step!xGc:fetch!#;:^=!sh,_o!#FwZ>!sk%tail!yK?!tYIfailure!ws[H!|F7!wt-!#[V;modulo!u2Z@!u2%byte_trap!$Y8=orb!w,ahalf!w,#!v@[A!z80!{/U!$Z/$Jmaterialize_model!sy+!#FT[m!#FTW3Run?mi!tM#ount_!uU#I!uBP5M!u6#!#;EL!t@#<syscall_arg!$Hj<6of_nat!#i=<addK!#=&?2!sEA!#Ja[@!u6/!w;Y9sys_input!{7Z<!#<a#!#J\%!}0[ms!$&m#ab!#C?%K!xiP<S!u}%I!u=#01I!sc^!yUQapply_effect!}0Q!#~{#re!s\R:!s\#unm!#4J#!tvT!s_Q!t@%9!t@#zero!t?P;!t?%!s^P!uX-copie!uXW!s_Q!t@-!#If#!t@W!s_%!z0Q=!z0&E!yN$!z1Q@advance_past_svc!#3AZ7cfg!#38X6!s`#m!vKP9!sY$odel!#IO^!#\{/I!u$Ponfig!#et\C!#:81!#J~T!tU/!#8=[6to!tH,!uwO9s!u+$cfg!#jk<!s^77!s]$to!#LoL!{H%8m_haltedK!tsY!$vz:x!#lO<!sxB2!s^Z3!uoQG!#=#&!#8b$!#B+c=!#=4'!z1Y!u@-4!#?K[!#;+-!#O;dD!#4p2!#F;Vpecs!#CC'spec!v3Z5!{>Tkil!$+6=!s]94m_fs!tpZ6!s^Z7!#AyKMonad7outcome!|7\8I!}i;0!tXZ1!#9XNDspurious_refusal!tc#!#DtP5even!#e4M!s\04!#75N!#6U'!#73X2I!tpW0!tpO;S!vm&Cf!#;}]>!y5%s!#?Q1!y>1Peano2l!#Mu<6to!#N=#!#bR?D!$|?,_in!#l#$!$3UD!#V-#u!#Oa<!tf#!$MPCeq!$qpAbv!$:f@>pow_pos_nonneg!#Pw<pow!sC<:!sk#!sgB7compareK4!sG&9micromega6VarMap1!$%O#!sD>0!sD6=RingM!s4'7Formula!{D#!sQ47Env!sT#5PExp!$mr#!sIC2K!t?L!stF7C!sI55Tauto8B!sm&!sH6:Z!t;+=Z!sT$CheckerC!vI<4f!%?+#!sq?C!sq0_soun!$:I<4of_N!y~A=!y~&_sm!#gM#!sR?@!$yD%!%,\;4Znat5Z2Nat2i!%,z=max!sC<8max!#=4#!|n>e!#9-8or!yU8!xg15Psatz!y8F!sO&6K!wV@;!tk%!#57#!s{8!{l,1!sD@3K!y{<G!zj'6!y26;ZifyClasses;rew_i!#U{#v!suF4!sJF5!sJF8!sJF3!u1B5mkapp!sKErel!}D<5eKind!$&y<unit!y88!se%4kind!#{#>!sf$1!yOD3Op205!tt68!uA#Inst@!#aS$_!#:C$_eq!|W9!|U#Z6inj_lt!uL<:!#7E$ison!#6f7!zj;0!u>I3!{eN!v9J1!xTB7!{+&!v3>9i!#;>'!$#U_2!#K]`:reg_!#fg%!#@6$!t\V9ex!t[%1!t[a6mkR_of!#OV&!w%4!#:s13!v}>8!z2#succ".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos3h5LinuxProcessSemantics5Riscv7Preludehf5bvmap35stdpp9bitvectorbdefinitionskd2bv37Corelib4Init5Logicmf2eq3h5LinuxProcessSemantics5Riscv3Semo87reg_getmf1Imf3notkd2BVkd4BvWf69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRegsEquivM~~~~~~sa8regs_eqvsa9fregs_eqv37Corelib4Init9Datatypeshhe4boolhf6bv_eqbhf9bvmap_seto84Coreo84rgethhe6optiono84coremf3ando86c_fcsro87c_fregso84c_pco86c_regso86c_resvsa8core_eqvo84rseto84fseto87with_pco89with_fcsro89with_resvo86accrue3h5LinuxProcessSemantics5Riscv3Fpuhu86fflagso86fwrite01Z3h5LinuxProcessSemantics5Riscv5Instrii04ffmto8ainval_resvo84execii05instrsa7eff_eqv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsin3dmachine_statein37ms_fcsrin38ms_fregsin36ms_memin39ms_pc_valin37ms_regsin37ms_resvin36ms_romin3ems_svc_pendingsa6ms_eqvhhe4prodin3daccess_reportin3emachine_resultmf5Falsein3caccess_valuehhe3fsthhe3sndmf4Truein3faccessed_rangeshhe4listin3dmemory_accessin3h3interp_eff_accesseso83eff79OSSVerify6Proofsaboost_jsonafuzz_parse3libaRegsEquivM8WithSegs~~~~~~js68ares_eqvin36ms_regin3h4decode_exec_accessesjs69msres_eqvin3dstep_accesses3h5LinuxProcessSemanticsfLinuxProcessSem5Statekl95Model3h5LinuxProcessSemanticsfLinuxProcessSem3Runkp0fmi_account_stepjs68mres_eqvkp0csyscall_argskp09sys_inputkl9cSyscallInputkp0capply_effectkl9dSyscallEffectkp0h0advance_past_svckp06configkp09cfg_modelkp06cfg_msjs67cfg_eqvkp07step_tokp05mkCfgkp09sstep_cfgmf2exkp0bSpuriousCfgkl95eventjs66to_eqvhhe3nat37Corelib4Init5Peanolr92lt46Stdlib6ZArith6BinInt1Zlt36of_natkd7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lvf3mkRsa6mkR_of3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypemkb7Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition regs_eqv : ltac2:(zQ "30!h9!k5!ma>1R@2$1@1$0#5@1$2@1$0#k0>2R'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "90!h9!ma!o3!k5!qa!r4!r8!re!s3\1R@2$3@1$0#5@1$1@1$0#k0\2R'@2$3@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@1$6@3$2@1$1@1$0#5^1@3$7@1$0#5ZKv$5@2$8@1$0#5Z@3$2@1$1@1$0#k0@2$4^4^2@2$4^3^2").
Definition fregs_eqv : ltac2:(zQ "30!h9!k5!ma>1R@2$1@1$0#5@1$2@1$0#k0>2R'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "50!h9!ma!k5!qa!o3\1R@2$2@1$0#5@1$1@1$0#k0\2R'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5@3$4@1$1@1$0#k0@2$3^3^1@2$3^2^1").

Lemma regs_eqv_sym : ltac2:(zQ "40!h9!k5!hg7!ma>1R@2$1@1$0#5@1$3@1$0#k0>2R'@2$1@1$0#5@1$3@1$0#k0>0@2$2^2^1@2$2^2^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##&oh01Hh12Hrh21Rh32R'h41rp;1p;2p;3p;4g0000R0p4p7210R1p1000\p4p710p8P!s6$18!s62V!sU&!s7'23!sG12Q!s6'g002nj10Tg003Sj1:Tg0048j12!s/$Vj11TP0j29Tg0059j24Tg006@j38!s/$cj37Tg007=j16!s/$Vj23Tg008@j45!s/$\#0R0#:#2R1%00#!s$'2#1R0'9R2f1R3f0R4'4%11R5g009Ag009_5819754#6P0f4/33f3/33f2R0P3P4O2C5W1W41430eW0X32W2o"). Qed.
Lemma fregs_eqv_refl : ltac2:(zQ "40!h9!k5!hh2!ma>1R@2$1@1$0#5@1$3@1$0#k0@2$2^1^1").
Proof.
ltac2:(KReplay.run1 (kr_t_RegsEquivM ()) [] "h01Rh11rp;1p;2g002nj10Tg003Sj17Tg0048j12Tg004Vj11Tg0000j26Tg007Vj25Tg00:;j24Tg00:Uj23Tg008\#0R0#7#2R1%00#0#0#0#0#2#1R0'6%11f1f0R1'5,40W11311eW0o"). Qed.
Lemma fregs_eqv_sym : ltac2:(zQ "40!h9!k5!hh2!ma>1R@2$1@1$0#5@1$3@1$0#k0>2R'@2$1@1$0#5@1$3@1$0#k0>0@2$2^2^1@2$2^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_RegsEquivM ()) [] "h01Hh11Rh22R'h31rp;1p;2p;4g002nj10Tg003Sj17Tg0048j13Tg004Vj11Tg0000j26Tg00:Uj24Tg007Vj22Tg008@j45Tg008\#0R0#7#3R1%00#0#0#0#0#3#1R0'6R2f1R3f0R4'4%11P0f3/24f2R0/24P3P4O1C5W31430eW0X22W1o"). Qed.

(* [comment removed for export] *)
Lemma reg_get_set : ltac2:(zQ "80!h9!ma!hj6!qa!o3!hje!k5!hk7>1R@2$6@1$0#5@1$1@1$0#k0>1k@1$1@1$0#5>1r@1$1@1$0#5>1v@1$1@1$0#k0@3$4@1$1@1$0#k0@2$3@5$7@1$0#5@1$1@1$0#k0^3^1^4^2M2\0$2@1$1@1$0#k0@3$5@1$0#5^3^2^1@2$3^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##1qp'0h01Eh11bi001bh21Hh31kh41ah51Rh61eh71rh81vp;1p;2p;3p;5p;6p;7p100;]p4p70R0g00:;R1p4p710R2p8P0g000\R3!s9&4p8P0p10018!s8&5!s8+Vp4p7210R6!s^&23R0!sL&7p8p100<M!t7%8P2p8P8P4!s+$5!s+$6!s+$7p8P!sQ$=;!sa%p8g0000R8!t+&!sB$X!sB'p100>_!s{%9!s{$9!s{$9!s{$9!s{$9P7!sk$2nj12Tg003Sj1DTg0048j18!s/$Vj16TP8j2CTg00?Uj31TP1j2<Tg006cj30Tg00@Bj57Tg007Vj24Tg00A2j3;!s/$gj3:TP0j6Bj7>Tg00C6j2ATP3j69Tg00DBj2=!sb$=j1?!s8$aj5@Tg00F1R3f!wD%FQR130p=5g00G1R89030p=3g008\#2R7#D#8R9%27#2!s$&8#6R7'C%69R6f2R5f1R4519R2P31<30f3R:=195=030P3f5R;f4R<519!s7$9P7f6R=P<f7R>D7/4;P3P7P4P<14>;n010!s#$20000507]0P4A19<:R?#!tp$QA1940#5A0654[R@A0640%52R2[A06:5\2A;940P4n20!ss'1!st$000X16X46P@^16^46P0P=P;P4O3A06=;P6P=P9P7P0P=f9D7/4>=07=X36f8?:=;P>P0EBb0b2W0%3?!sb$<P:A06;<R<P6P;A190=#3g00GlR:]0X36A19;;#3P3A19==%30X13P0P11A9=E9A0318P3P1P3p-0!{$$HIP:n011!u|,X63g009_P8P0E9P:1=:0b2b0W0P=P0P4F>W2%?<eD@W0!s`1P0O1b0b1X87X76W3W5o"). Qed.

Lemma regs_eqv_set : ltac2:(zQ "50!h9!ma!k5!hk7!hg7>1R@2$2@1$0#5@1$1@1$0#k0>2R'@2$2@1$0#5@1$1@1$0#k0>1k@1$1@1$0#5>1v@1$1@1$0#k0>0@2$4^4^3@2$4@5$3@1$0#5@1$1@1$0#k0^3^2^5@5$3@1$0#5@1$1@1$0#k0^3^2^4").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##,lp'0h01bi001bh11Hh22Hrh31Rh42R'h51kh61rh71vp;1p;2p;3p;5p;4p;6g002nj11Tg003Sj1>Tg0048j14!s/$Vj15Tg0000j2=Tg0059j28Tg006@j3<!s/$cj33Tg007=j1;Tg00?Uj36!s8$Vj20Tg00@Bj52Tg00:;j2:Tg00Hej49Tg0023j67Tg008\#1R0#>#4R1%10#1!s$&4#5R0'=R2%51R3f3R4f2R5'8f0R6g009Ag009_5<1533#;P0g00F1R7P0f4R8f1R9561R:P4f6R;/09n010!s#$20000P1P0f5R<P8P;D2/059306X00P0P7P0P:P410<!sZ37P0A61<5P8f7R=/05!sF1=!si&:P7!s$$0P6P<f8/04!sn5P6P<10=!s@2530P61:08P4P5P9O2n011!sE,b!u,$P8P4P<D2/09P<P8P9P4C9E7!sA+!uF$9P;!sA,W2X63!sF$5P9P8D2!s2+4D2'8eW1X70W5X42W3o"). Qed.
Lemma fregs_eqv_set : ltac2:(zQ "50!h9!ma!k5!hk7!hh2>1R@2$2@1$0#5@1$1@1$0#k0>2R'@2$2@1$0#5@1$1@1$0#k0>1k@1$1@1$0#5>1v@1$1@1$0#k0>0@2$4^4^3@2$4@5$3@1$0#5@1$1@1$0#k0^3^2^5@5$3@1$0#5@1$1@1$0#k0^3^2^4").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##,;p'0h01bi001bh11Hh21Rh32R'h41kh51rh61vp;1p;2p;3p;5p;4p;6g002nj11Tg003Sj1<Tg0048j15!s/$Vj14Tg0000j2;Tg00:Uj29Tg00?Uj36Tg007Vj20Tg00@Bj52Tg006cj33!sS$;j2:Tg00Hej47Tg0023j68Tg008\#1R0#<#5R1%10#1!s$&5#4R0';R2%41R3f3R4f2R5'9P0g00F1R6P0f0R79614R8P5f5R9/07n010!s#$20000P1P0f4R:P4P9D2f1R;'09307X00P0P6P0P8P510:!s]36P0A61:;P4f6R</0;!sF1=!si&8P6!s$$0P7P:f7/05!sn5P7P:10<!s@2530P71:04P5P;O1n011!sC,b!u-$P4P5P:D2/07P:P4P7P5C7E8!sA+9!sA%9!sA,X53!sD$5P;P:D2!s2+4D2'9eW1X60W4X32W2o"). Qed.

(* [comment removed for export] *)
Lemma rget_eqv : ltac2:(zQ "80!h9!ma!k5!hl3!hla!hm1!o3!hg7>1R@2$2@1$0#5@1$1@1$0#k0>2R'@2$2@1$0#5@1$1@1$0#k0>0@2$7^2^1>1F@2$2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$5@1$1@1$0#k0>1r@1$1@1$0#5@3$6@1$1@1$0#k0@2$4@5$3^8^5^4^3^2^1@2$4@5$3^7^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##/Mp'0h01Eh12H0h21rh31Fh41Hh51Rh62R'h71bi001bh81eh92fch:2pch;2rvp;1p;2p;3p;6p;7p;5g002nj11Tg003Sj1ETg0048j15!s/$Vj16Tg0000j2DTg0059j2@Tg00Ioj1<Tg00JQj12Tg00:;j27Tg006cj30Tg007Vj23!s8$@j3;Tg00K9j2C!s/$cj2B!t$$\j6ATg00DBj2?Tg0023j7=!se$=j1>Tg00L@j58!s/$ij19Tg00MRj2:Tg00F1R0f0R1g00G1R230p=4g008\#1R3#E#5R4%13#1#1!s7$1#5#6R5'DR6f1R7/@1%53#6%<5%64R3%21R8P01701%27=001P0f3R9#2!s2%P5P7g00N9R:f;f4R;'3n010!s#$20000!sI%P:f:/3;!sA1505]0P7f2R<#2R=g00FQ500175:W0%4=f8P9g009A!sB$9_R>5;4R?9039R@P3P?%48g00GlRA]0X23%2?#4P01C4?/B=P0p-0P1g00HIPAn011!tH,X80P>P2P1EAPA1?A1b1W0P;P1P7F=W1%>@eO2W0!s[1P1O1b0b7!uH$8P:f7P;P9P<P7D8R@#9/31!uq68P:f6!sO-7!sO6505e1:@11:71505eW2W;W9X:5X36W4X66W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition core_eqv : ltac2:(zQ "10!hmb>1c$0>2c'$0P") := ltac2:(zQ "d0!hn2!o3!h9!ma!hn8!ho1!hob!hp2!hpb!hmb!hm1!hh2!hg7\1c$9\2c'$9@2$0@2$c@1$7^2@1$7^1@2$0@2$b@1$5^2@1$5^1@2$0@3$1@1$3@1$2#k0@1$6^2@1$6^1@2$0@3$1@1$3@1$2#i0@1$4^2@1$4^1@3$1@1$a@1$3@1$2#k0@1$8^2@1$8^1").

(* [comment removed for export] *)
Inductive eff_eqv : eff -> eff -> Prop :=
| EqvDone : forall c c', core_eqv c c' -> eff_eqv (EDone c) (EDone c')
| EqvIllegal : forall c c', eff_eqv (EIllegal c) (EIllegal c')
| EqvEcall : forall c c', eff_eqv (EEcall c) (EEcall c')
| EqvEbreak : forall c c', eff_eqv (EEbreak c) (EEbreak c')
| EqvFault : forall c c', eff_eqv (EFault c) (EFault c')
| EqvDefIllegal : forall c c', eff_eqv (EDefinedIllegal c) (EDefinedIllegal c')  (* [comment removed for export] *)
| EqvLoad : forall n a k k', (forall v, eff_eqv (k v) (k' v)) -> eff_eqv (ELoad n a k) (ELoad n a k')
| EqvStore : forall n a v k k', eff_eqv k k' -> eff_eqv (EStore n a v k) (EStore n a v k').

Lemma core_eqv_mk : ltac2:(zQ "80!h9!ma!k5!hl3!hm1!hq4!hh2!hg7>1R@2$2@1$0#5@1$1@1$0#k0>2R'@2$2@1$0#5@1$1@1$0#k0>1F@2$2@1$0#5@1$1@1$0#k0>2F'@2$2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$4@1$1@1$0#k0>0@2$7^7^6>0@2$6^6^5@2$5@5$3^9^7^5^4^3@5$3^8^6^5^4^3").
Proof.
ltac2:(KReplay.run1 (kr_t_RegsEquivM ()) [] "h01Fh12F'h21Rh32R'h42fch52pch62rvp;1p;2p;5p;3p;4g002nj10Tg003Sj1ATg0048j13Tg004Vj16Tg0000j2@Tg00Ioj1?Tg0059j2<Tg00:Uj2;Tg00L@j5:Tg00Lij19Tg00N^j17Tg00OHj18Tg006cj32Tg00Ooj1>Tg00PXj1=Tg00GQj25Tg00:;j24Tg00QAj41Tg008\#0R0#A#3%00#0#0#0R0#0#3#6R1'@R2%30#6R0%?1R3f6R4f5R5'<f4R6,;5f8P4P6f3R4f2R7D:R8#9f7P5P6P4P7D:R7#9'<%78%77';R4%88%87R6521R5%>8%>7R9520R:%=8%=7R7523R8'5R;'5R<'5f1P4P<f0P5P;1416P:P814091437C1C1C1C1UUW6W4X51X12X02X32W2o"). Qed.

Local Ltac core_tac :=
  unfold core_eqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_eqv_rset : ltac2:(zQ "50!h9!hmb!hqf!hq4!ma>1r@1$4@1$0#5>1v@1$4@1$0#k0>1c$1>2c'$1>0@2$3^2^1@2$3@3$2^5^4^3@3$2^5^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##<Bp'0h01Hh12c'h21fh31ph41sh51Fh62F'h72HFh82HRh91Rh:2R'h;1bi001bh<1ci011ch=2f'h>2p'h?1rh@2s'hA1vi026c_fcsri037c_fregsi044c_pci056c_!s8%6!s0$svp;1p;2p;3p;5p;4p;6p;8g002nj1<Tg003Sj1KTg0048j1E!s/$Vj1CTg00Q\j2>Tg00Rcj3=Tg0000j2JTg00Ioj1HTg00L@j50Tg0059j2ATg00:Uj2@Tg006cj31Tg00JQj1BTg00@Bj5:!s\$ij13Tg00N^j15Tg00OHj16!s/$oj14Tg00PXj12Tg00GQj2;!t$$;j2D!tg$Aj4?Tg00SJj5GTg0023j6FTg00TUj8ITf2R0f1R1#2f0R231p=7f6R3f5R4#6f4R531f3R6%40;11/;2';p=8%35/A6%50/@!s:'9g008\#<R7#K#ER8#C%<7#<#<!s9$<#E#CR9g00UZR:P:1>12A=450A=451'>[^1:P21J89R;%E7#CR7%H9R<P:P3P4P5P6P0D0/>2f?R=f>R>f7R?!sA'D03=A==>1'>[P2P=P>f=R@f<RAf;RBD0!se%P1P2D0'>f@RC/A4RD1@=5A19>6A17@0A1<A1g00F1REP:fHRF#BRGPCP=P>P@PAD0RHP8P9PFfGRIPCD:!s@,n010!s#$20000R@PEP:PG!u-'P1D0R>!sb%PIP4D:!s>,!s`2=#3P@%5=P9P@%6=P7P@%4=%2=97<@F8D91@C4A19C4P9P3fAR@=173A1<@3R=PEP:fNRJ#BRKfFRLfERMP0fCRNfBROD0!tP$JfMRPPLD:RQPMP0PNPO!tT4N!u6$KPBf:RRf9RSf8RTP?D0RU!sj%PPPBD:RVPRPSP!s@%W!sj2X#3RYPN%5XRZP9PN%6XR[P7PN%4XR\%2XRX97<NF8D9[[X39A17C4P7P3!tJ&LPMPSP1POD0PQ!s2,!t42OPYPOPZP9POP[P7POP\A7<OXF8D9\=X27A1<C4P<!s}2TP2!s}+!s2$!s}2KPYPK!s}$K!s}$K!s}$K!s}$X4<%BPPE!s$$:P2PIPL!u~%!w$%fORKPJPID:!s>,!v:3!s`&APB!s`/PKPJPAD:!s<,!s^2A#3PX%5AP9PX%6AP7PX%4A%2A97<!tj$P21ALB1@MRRRA19SSRXA17TTRAA1<??RK';R\';R[';RZP4PRP[P5PXP\1D9SPAPK1D7T1D<?C!s$$RKC?!vP+?D0RA%3UPA%5UP9PA%6UP7PA%4U%2U97<AF8D9e1AQVPZPLPB!y=$4DGPKC?!w2+?D0R?%3WP?%5WP9P?%6WP7P?%4W%2W97<?!sl$n0110001020101b;P@P2EFW0!s-3W7X8DP2GI!}$&!}X&PI%3HD:%5H%6H%4H%2H!vk4D!sY&!}O+%3>D:%5>%6>%4>%2>!sY48#3PD%58P9PD%68P7PD%48%2897<D!u-$A=FIHA=FI>'>eW0X@<X=7X>9X6;X:;!#46+O5!uX$!uZ$51105103104102106X1:W4W2X39X5;W9!s\JW<WAW?o"). Qed.
Lemma core_eqv_fset : ltac2:(zQ "50!h9!hmb!hr6!hq4!ma>1r@1$4@1$0#5>1v@1$4@1$0#k0>1c$1>2c'$1>0@2$3^2^1@2$3@3$2^5^4^3@3$2^5^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##4kp'0h01Hh12c'h21fh31ph41sh51Fh62F'h72HFh82HRh91Rh:2R'h;1ci001ch<2f'h=2p'h>1rh?2s'h@1vi016c_fcsri027c_fregsi034c_pci046c_!s8%5!s0$svp;1p;2p;3p;5p;4p;6p;8g002nj17Tg003Sj1HTg0048j1A!s/$Vj1@Tg00Q\j25Tg00VCj36Tg0000j2FTg00Ioj1DTg00L@j52Tg0059j2:Tg00:Uj24Tg006cj30Tg00@Bj53Tg00GQj28!sw$jj5G!sS$;j2C!t:$Aj4?Tg0023j6BTg00TUj8E!t1$ij1>Tg00N^j1<Tg00OHj1;!s/$oj19Tg00PXj1=Tf2R0f1R1f0R2'8'8p=1g008\#7R3#H#AR4#@%73#7#7!s9$7#A#@R5g00UZR6P61512f5R7f4R8;60A6781'5[^16P21F45R9%A3#@R3%D5R:P6f6R;P7P8f3R<P0D2/52f?R=f>R>f7R?P!sC$P<D236A6=>1'5[P2P=P>f=R@f<RAf;RBD2P8P<P0P1P2D2'5f@RC/:7RD14=8A05><REA03@0RFA0:A1RGP4P5fHRHfGRIP=D3P4P5PHPIP8D3'4A1EFG51D14C7A05C7P5P;fARG=03;A0:G;RFfF/:BRB!so$NREfMRJfERK!sq&EPJf:RED3'4RLf9RM9050fCf8RN503fB=0:?RO3131[[X35A03C7P3P;A05MMRPA031N;1O91BL\FX23A0:C7P:P;A03NNA0:2?51P91BLX4:1:KE!tD$JfLREfD!tT+JPEPM!tR%A05NNRBA03??RPA0:;;RF'8RO'8RQ'8P8PLPQPKPM!s[$<DGPBPO1C5NPPPF1C3?1C:;C?!s$%PGP2EBW0!s-3W7X8DP2GEPCP=P>P@PAD2RA#>!v}'%<AD3%;A%9A%=AD2R@#>!xO%P0P1D2R7!sR/7D3%;7%97%=7D2R4#>':%<@%<4'4%;@%;4505%9@%94503%=@%=450:3131eA6HIAA6HI7'5eW0X?:X<3X=5X69X:9!yE,O5n01100000151104102103101105X16W4W2X35X59W!s\KW;W@W>o"). Qed.
Lemma core_eqv_with_pc : ltac2:(zQ "50!hmb!hrd!hq4!h9!ma>1v@1$4@1$3#k0>1c$0>2c'$0>0@2$2^2^1@2$2@2$1^4^3@2$1^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##2hp'0h01Hh12c'h21fh31sh41Fh52F'h62HFh72HRh81Rh92R'h:1ci001ch;2f'h<1ph=2p'h>2s'h?1vi016c_fcsri027c_fregsi034c_pci046c_!s8%5!s0$svp;1p;2p;5p;3p;4p;6p;8g002nj15Tg0048j1>!s/$Vj1@Tg00Q\j23Tg00X6j24Tg003Sj1FTg0000j2DTg00Ioj1CTg00L@j51Tg0059j28Tg00:Uj26Tg006cj30Tg00GQj27!sA$;j2?!t1$Aj4=Tg0023j6BTg00TUj8E!sw$ij1<Tg00N^j1;Tg00Ooj1:Tg00PXj19!s8$Hj1ATf2R0f1R1f0R2'7'7p=2g008\#5R3#5!s$%R4#5#>#@R5g00UZR6P61312f4R7/401471'3[^16P2%F3#>/D5R3%>4#@R4%C5R8P6f6R9f5R:P7f3R;P0D1/32f>R<f7R=P9P:P7P;D1'414<1'3[P2f?R>P<f=R?f<R@f;RAD1P7P;P0P1P2D1'3f@RB/8:RC16>7RDA05<;A04?0REA08@1RFfGRG=05G?2EF92CD16B:A05B:A04B:P4P9fARD=089fF/8ARAfERFf:RE'6RHfMRI=05IRIf8RJ9041fB=08=3232[X24A08B:P8P9A04JJA082=52I92AHX3818FEfDf9'6REfLRF=05FRHA04==RAA0899RI'7RJ'7RK'7P7PEPKP;PHPJ1?5FPAPI1?4=1?89C=!s$%PDP2EBW0!s-'W0W6X7CP2GEPBP>P<P?P@D1R@#<%;@PG%:@%9@D1R?#<!v}%P0P1D1R:#<%;:PG%::%9:D1R<#<'8%;?%;<'6%A?%A<505%:?%:<504%9?%9<5083232e14G@14G:'3eW0X>8X;4X=5X53X93!we,O5n01100000151104102103101105X16W3W2X<5X43W8!s\JW:W?o"). Qed.
Lemma core_eqv_with_fcsr : ltac2:(zQ "50!hmb!hs7!hq4!h9!ma>1v@1$4@1$3#i0>1c$0>2c'$0>0@2$2^2^1@2$2@2$1^4^3@2$1^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##2pp'0h01Hh12c'h21ph31sh41Fh52F'h62HFh72HRh81Rh92R'h:1ci001ch;1fh<2f'h=2p'h>2s'h?1vi016c_fcsri027c_fregsi034c_pci046c_!s8%5!s0$svp;1p;2p;5p;3p;4p;6p;8g002nj15Tg0048j1>!s/$Vj1@Tg00Q\j23Tg00X`j24Tg003Sj1FTg0000j2DTg00Ioj1CTg00L@j51Tg0059j28Tg00:Uj26Tg006cj30Tg00GQj27!sA$;j2?!t1$Aj4=Tg0023j6BTg00TUj8E!sw$ij1<Tg00N^j1;Tg00OHj1:Tg00PXj19!s8$oj1ATf2R0f1R1f0R2'7'7p=2g008\#5R3#5!s$%R4#>#@R5g00UZR6P61312f4R7/401471'3[^16P2%F3#>%5!sT%4'DR3%C4R8P6f6R9f5R:P7f3R;P0D1/32f>R<f7R=P9P:P7P;D1'414<1'3[P2f?R>P<f=R?f<R@f;RAD1P7P;P0P1P2D1'3f@RB/8:RC16>7RDA04<;REA05?0A08@1RFfGRG=05G=2EF92CD16B:A04B:P4P9fARD=059A08D9fF/8ARAfERFf:RE'6RHf9RI9040fMRJ=05JRJfB=08=3232[[X24A05B:A08B:P8P9A04IIA082=72J92AHX3818FEfD/6IRIf8RE=04ERFfLRH=05HRAA0899RJ'7R='7RK'7P7PIPKP;PFP=1?4EPAPJ1?5H1?89C=!s$%PDP2EBW0W0!s0+6X7CP2GEPBP>P<P?P@D1R@#<%;@%:@PG%9@D1R?#<!w,%P0P1D1R:#<%;:%::PG%9:D1R<#<'8%;?%;<'6%:?%:<504%A?%A<505%9?%9<5083232e14G@14G:'3eW0X>8X<5X=4X53X93!wm,O5n01100000151104102103101105X16W3X;5X24X43W8!s]JW:W?o"). Qed.
Lemma core_eqv_with_resv : ltac2:(zQ "60!hmb!ht3!hq4!hm1!h9!ma>1v@1$3@1$5@1$4#k0>1c$0>2c'$0>0@2$2^2^1@2$2@2$1^4^3@2$1^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##2tp'0h01Hh12c'h21fh31ph41Fh52F'h62HFh72HRh81Rh92R'h:1ci001ch;2f'h<2p'h=1sh>2s'h?1vi016c_fcsri027c_fregsi034c_pci046c_!s8%5!s0$svp;1p;2p;5p;3p;4p;6p;8g002nj15Tg0048j1>!s/$Vj1@Tg00Ioj1CTg00Q\j24Tg00YLj23Tg003Sj1ETg0000j2DTg00L@j51Tg0059j29Tg00:Uj26Tg006cj30Tg00GQj27!sA$;j2?!t$$Aj4=Tg0023j6BTg00TUj8F!sw$ij1<Tg00N^j1;Tg00OHj18!s/$oj1:Tg00PXj1ATf2R0f1R1f0R2'7'7p=2g008\#5R3#5!s$%R4#5#>#@R5#CR6g00UZR7P71412f4R8/301381'4[^17P2%E3#>/D5R3%>4#@R4P7f6R9f5R:P8f3R;P0D1/42f>R<f7R=P9P:P8P;D1'313<1'4[P2f?R>P<f=R?f<R@f;RAD1P8P;P0P1P2D1'4f@RB/9:RC16>8RDA05<;REA04?0RFA06@1fGRG=06G92EF92CD16B:A05B:P5P9fARD=049A06D9RFfF/9ARAfEREf:RH'6RIf9RJ9050fCf8RK504fMRL=06LRL3232[[X35A04B:P4P9A05JJA041K;2L92AI\FX24A06B:19EHfD/6JRJA05KKRHA04==REfLRF=06FRI'7RA'7RL'7P8PJPLP;PHPA1?5KPEPI1?4=1?6FC=!s$%W0PDP2EB!s-,W6X7CP2GFPBP>P<P?P@D1R@#<%;@%8@%:@PGD1R?#<!w1%P0P1D1R:#<%;:%8:%::!sG$<#<'9%;?%;<'6%8?%8<505%:?%:<504%A?%A<5063232e13G@13G:'4eW0X>6X;4X<5X53X93!wq,O5n01100000151104102103101105X17X=6W2X35X43W8!s]JW:W?o"). Qed.
Lemma core_eqv_accrue : ltac2:(zQ "40!htf!hmb!hq4!iga>2fl$3>1c$1>2c'$1>0@2$2^2^1@2$2@2$0^4^3@2$0^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##4^p'0h01Hh12c'h21fh31ph41sh51Fh62F'h72HFh82HRh91Rh:2R'h;1ci001ch<2f'h=2flh>2p'h?2s'i016c_fcsri027c_fregsi034c_pci046c_!s8%5!s0$svp;2p;1p;5p;3p;4p;6p;8g00Q\j26Tg00Z8j23Tg002nj14Tg003Sj1FTg0048j1?!s/$Vj1ETg0000j2LTg00Ioj1JTg00L@j55Tg0059j2;Tg00:Uj27Tg006cj30!t1$aj1<Tg00GQj28!sJ$;j2>Tg00QAj49!tL$3j6=Tg00TUj8KTg00Ooj1:Tg00X`j2D!t:$ij1CTg00N^j1B!sJ$Hj1@Tg00PXj1ATg00K9j2ITg00[Oj2H!s/$lj2GTf3R0f2R1f1R2'If0R3'H'Gp=21823,81p=1g00\Rg00UZR4P41623f4R5/311352'6[^14P3g008\#4R6#F#?%46#4#4!s5$4#?#ER7'LR8%?6R6#ER9%J7R:P4f6R;f5R<P5P0P1D5/63f>R=f7R>P;P!s=$D5'313=2'6[P3f?R?P=f=R@f<RAf;RBD5!sb%P2P3D5'6f@RC/;<RD17?5REA07=0RFA09@1A0:A2RGP6P6P@fGRH#<RIC2!s6$1PIC2509=1FG91DE17C<A07C<P7P;fARE=09;A0:E;RGfF/;BRBfERFf:RJ'7RKf9RL9071P6P6fCfM#<RM!t$%f8RNPMC2RO509fB=0:>RP3131[[X37A09C<P9P;A07LLRQ!tZ$2PMC2=09O;1P91BK\GX29A0:C<P:P;A09OOA0:3>51Q91BKX4:1;FJfD/7LRLA07NNRJ!so$>fL#<C2R>=09>RFA0:;;RK'8RB'8RQ'8P5PLPQP0PJPB1>7NPFPK1>9>1>:;C9!s$%PEP3E=W0!s-3W7X8DP3GK!t8$CP?P=P@PAD5RA#:PIC2/DAR@#C!sE$!xN&P2D5R<!sE'<RI#C';%B@%BI'7%@@%@I507%:@%:I509%A@%AI50:3131e13HA13H<'6eW0X?:X<9X>7X68X:8!xq,O5n01100000151104102103101105X14W4W2X37X58W9!s\JW;W=o"). Qed.
Lemma core_eqv_fwrite : ltac2:(zQ "70!hmb!ih4!hq4!h9!ihd!ik4!ma>3fmt$5>1r@1$6@1$3#5>1v$4>1c$0>2c'$0>0@2$2^2^1@2$2@4$1^6^5^4^3@4$1^6^5^4^2").
Proof.
ltac2:(KReplay.run1 (kr_t_RegsEquivM ()) [] "p'0h01Hh11ch22c'h33fmth41rh51vi001fp;1p;2p;4p;5g002nj10Tg003Sj18Tg0048j11Tg004Vj16Tg00Q\j25Tg00]=j44Tg00[lj23Tg00]fj17Tg00^Pj52Tg00_\R0g008\#0R1#8#1#6g00`Gg00UZR2f1R3f0R4'5P0P4f5R0f4R5f3R6C4P4P0P5f2R7C4'5P0P5%01#0#0#0R1#1/36#7P7P3P4D2P5%01#1/36P7P3P4D2n0110000020000W0X22W1W5W4W3o"). Qed.
Lemma core_eqv_inval_resv : ltac2:(zQ "50!hmb!ikc!hq4!h9!ma>1a@1$4@1$3#k0>1c$0>2c'$0>0@2$2^2^1@2$2@2$1^4^3@2$1^4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##A~p'0h01Hh12c'h21fh31ph41sh51Fh62F'h72HFh82HRh91Rh:2R'h;1ah<1bi001bh=1ci011ch>2f'h?2p'h@1ri021rhA2s'i036c_fcsri047c_fregsi054c_pci066c_!s8%7!s0$svi081oi091xp;1p;2p;5p;3p;6p;8p;4g002nj1>Tg0048j1E!s/$Vj1JTg00Q\j2=Tg00`ej2?Tg003Sj1OTg0000j2NTg00IoR0j1MTg00L@j50Tg0059j2BTg00:Uj2ATg006cj31Tg00K9j2C!s/$cj2KTg00aRj1PTg00YLj24!sn$ij16Tg00N^j18Tg00OHj17!s/$oj15Tg00PXj13Tg00b4j2GTg00GQj22!tC$;j2@Tg0023j6DTg00TUj8L!uG$Aj4FTf2R1f1R2#3f0R331p=:f6R4f5R5#7f4R631f3R7%51;12/23'2p=;%66/B7%81/A!s:'9A1456A17!sL+I1B671A!s6+HP4P5P6P7P1P2P3CFCFp=<g008\#>R8#>!s$%R9#>#ER:#JR;g00UZR<P<1=231?611?62'=[^1<P3%O8#E/N;R8%E9#JR9%M;R=P<!t5,D0R>/=3f>R?f7R@!s?'D0'?1??2'=[P3f?RAP?f=RBf<RCf;RDD0!ts,D0'=f@RE/B5RF1AA6A1;?7A19B1A1=C2P0P;P<PCg00F1RGP<1C:3RHfHRI,C:'KRJ%P;RKfARLPEPAP?PBD0RM'4PMn010!s#$20000RM!sF'PCD0RAn10110900021010200RN!t;&2PGP<PJ14K>P>!sl2>!w$,D0RJ!sl6O#6PN%8OP;PN%7OP9PN%5O%3O9:=NF;D91AE5A1;E5P;P4A19L4A1=L4!tM'fBROPGP<fN,C:,KHRHfGR:fFRPP7fDRQfCRRD0RS,4KPS!tl1PPfERSP1PRPOD0!tj6T!uX&@!uX$HPCPDf:RUf9RVf8RWD0RX,4KPX!s}2DPUPVPWP@!s{8X#6RYPT%8XRZP;PT%7XR[P9PT%5XR\%3XRX9:=TF;D9[[X3;A19E5P9P4!t[&O!t[&:PPPUP1PRD0RR,4KPR!uT3PSPVP2!uR:OPYPOPZP;POP[P9POP\A:=OXF;D9\NX29A1=E5P=!tF+3!tF0V!x?$E,4KPE!tF8WP3!tF8P#6REPY%8PRYPZP;%7PRZP[P9%5PR[P\%3PRP=1=XFIDHX4=!tL$E!tR2C!w&&!tR<!wI'!tR9E#6PY%8EP;PZ%7EP9P[%5E%3E91=PFIDHP4PHPG!s$$<P3fIPIPCPD1G;1RHD0RP,4KPP!{Q2P!sS%!|A%PDPHD0RH,4KPH!sO2H#6PP%8HP;PP%7HP9PP%5H%3H9:=PF;D9P31BIBRP1A:CRHA1;DDR?A19UURGA1=KKRE'2R['2RZ'2P@PHPZP4P?P[1@;DR[PGPE1@9URZ1@=KRYF<F<PIP:PDPU1G;2RI!zw&R\!ty&UPID0RD,4KRC#6P\%8CP;P\%7CP9P\%5C%3C9:=\F;D9ePPA1=IIRP,2GR\,2?RC,2H!tU$C!tU$\P[PGPPPZ1@=I!tK$X%6DPX%8DP;PX%7DP9PX%5D%3D9:=!z0$en01100!wf$101b<X@;P3O11BSU1AQVRXA1;WWRDA19@@RI/2ERZ'2RP'2P6PXPPP7PDPZ1@;WPI!uu$@P!uo%SPQPWP@PKD0RQ!}O'!s4$K#6PQ%8KP;PQ%7KP9PQ%5K%3K9:=Q!tc%!yQ$801021!tm%PLP3EDW0!s-3W7X8FP3GL!zg%%3APMP!#636M!sG'JP>P!#5f6>#6PM%8>P;PM%7>P9PM%5>%3>9:=M!td$1?:A1?:J'=eW0XA=X>9X?;X68X:8!#8x+O5!vq$!u+$51106104105103107X1<W4W2X3;X58W9!s\JW=W;o"). Qed.
Lemma core_eqv_if : ltac2:(zQ "30!hmb!hj6!hq4>1b$1>2c1$0>3c1'$0>2c2$0>3c2'$0>0@2$2^4^3>0@2$2^3^2@2$2M1\1b$1$0^7^6^4M1\1b$1$0^7^5^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##%Rp'0h02c1h13c1'h22c2h33c2'h42H1h52H2h61bi001bp;2g00Q\j20Tg00F1R0P0g00UZR1f3R2f2R3'0R4f1R5,03R6P0P1f6R7f5P2n0110000020000P0P1P7f4P3!s>1'0[[^31^21^11]0f0R3P5X56X44X31X21X11X01P3!s:5!so1W6o"). Qed.

(* [comment removed for export] *)
Local Ltac solve_core HR HF :=
  repeat first [ apply core_eqv_rset | apply core_eqv_fset | apply core_eqv_with_pc
               | apply core_eqv_with_fcsr | apply core_eqv_with_resv | apply core_eqv_accrue
               | apply core_eqv_fwrite | apply core_eqv_inval_resv | apply core_eqv_if
               | match goal with |- core_eqv (match ?X with _ => _ end) _ => destruct X end ];
  apply (core_eqv_mk _ _ _ _ _ _ _ HR HF).

Local Ltac eqv_struct HR HF :=
  repeat first
    [ apply EqvDone; solve_core HR HF
    | apply EqvIllegal | apply EqvEcall | apply EqvEbreak | apply EqvFault | apply EqvDefIllegal
    | apply EqvLoad; intros ?
    | apply EqvStore
    | match goal with |- eff_eqv (match ?X with _ => _ end) _ => destruct X end
    | match goal with |- eff_eqv (match ?X with _ => _ end _) _ => destruct X end ].

(* [comment removed for export] *)
Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].
Local Ltac unfold_rget := cbv beta iota zeta delta [rget c_regs].

(* [comment removed for export] *)
Lemma exec_eqv_core : ltac2:(zQ "a0!h9!ma!k5!hl3!il9!hm1!im0!im9!hh2!hg7>1R@2$2@1$0#5@1$1@1$0#k0>2R'@2$2@1$0#5@1$1@1$0#k0>1F@2$2@1$0#5@1$1@1$0#k0>2F'@2$2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$5@1$1@1$0#k0>2sz@1$1@1$0#k0>1i$6>0@2$9^9^8>0@2$8^8^7@2$7@3$4^4^3@5$3^b^9^7^6^5@3$4^4^3@5$3^a^8^7^6^5").
Proof.
  intros R R' F F' pc fc rv sz i HR HF.
  destruct i; unfold_exec; rewrite ?(rget_eqv R R' HR); unfold_rget; rewrite ?HF; eqv_struct HR HF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_eqv : ltac2:(zQ "10!iqa>2ms$0>3ms'$0P") := ltac2:(zQ "h01!h9!ma!hn2!o3!hm1!iqa!irb!is6!it2!itc!iu9!iv4!ivf!jg9!hh2!hg7&>0@1$1@1$0#k0@1$4@1$1@1$0#8\2ms$5\3ms'$5@2$2@2$f@1$a^2@1$a^1@2$2@2$e@1$7^2@1$7^1@2$2@3$3@1$1@1$0#k0@1$9^2@1$9^1@2$2@3$3@1$4@1$1@1$0#k0@1$d^2@1$d^1@2$2@3$3@1$4@1$1@1$0#k0@1$b^2@1$b^1@2$2@3$3@1$1@1$0#i0@1$6^2@1$6^1@2$2@3$3~0@1$8^2@1$8^1@3$3~0@1$c^2@1$c^1").

Lemma ms_eqv_sym : ltac2:(zQ "20!iqa!jhb>2ms$0>3ms'$0>0@2$1^2^1@2$1^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_RegsEquivM ()) [] "h02H1h12H2h22H3h32H4h42H5h52H6h62H7h72H8h82msh93ms'h:5nd_i2p;2p;1p;3p;4p;;g02D0j2BTg02E5j1<Tg0059j2ATg02F4j1:Tg00:Uj2?Tg002nj12Tg0048j1>Tg004Vj1=Tg02G4j13Tg006cj30Tg00Ioj1@Tg02H5j17Tg02I;j18Tg02J:j19Tg02K9j15Tg02L7j1;Tg00GQj24Tg02M5j3ETg02N@j3DTg008@j46Tg00QAj41Tg02OLl;CTg02PQR0f1R1f0R2'Bf2R3#<%<1'AR4%:3R5%:1'?g008\#2#2#2R6#2#2R7#2#>#=R8%33%3130%@8R9%73%7130%83%81509%>7#=R7%93%9130%>6#=#@\8R6%53%5130%;3%;15061B13f3R:#:/?5f4R5#3%3:508f5R;#7%75509f6R<#8%8;509f7R=#9%9<507f8R>#5%5=506f9R?#;R@%;>506%<?R>f:RA#<RB'A%:?RC%:ARD'?RE%3?RF%3ARG508RH%7?RI%7ARJ509RK%8?RL%8ARM509RN%9?RO%9ARP507RQ%5?R?%5ARR506RS%;ARA906@RT'4RU'4RV'4RW'4RX'4RY'4AEB>=PEPYADDC<PHPXP8PGPFP;C6PKPWP9PJPIP5C6PNPVP9PMPLP:C6PQPUP7PPPOP3C6PSPTP6PRP?P1C6P6PAP@P2C6C1C1C1C1C1C1C1W7W6W5W4W3W2W1X04P2M;CW:X90W8o"). Qed.

Section WithSegs.
Variable segs : ltac2:(zQ "20!jof!mo0@1$0$1").

(* [comment removed for export] *)
Definition ares_eqv : ltac2:(zQ "74!h9!ma!hm1!ji4!jic!jjd!hmb&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@2$3$6~0&@1$4~1&@1$5~2>1r~3>2r'~3P") := ltac2:(zQ "h28!h9!ma!hm1!hmb!ji4!jic!jjd!jkf!jl7!jm7!jme!jn5!hn2!o3!jnc!jof!jp7!hq4&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@2$4$3~0&@1$5~1&@1$6~2&\2r'~3P&@2$8~1^2&@2$8~1^1&\6result~2$7\1r~3\2r'~3M6\1r~3P^2\1a~2M6~4^2\1b~2@2$c@2$h1@3$9$3~0~5@3$9$3~0~6@2$c@3$d~0@3$a$3~0~5@3$a$3~0~6@3$d@1$f$h0@2$e~1^2@2$e~1^1$7$7M6~4^1~7$b$7M6~4^1~7$7$b").

Lemma interp_eff_accesses_eqv : ltac2:(zQ "70!h9!jq8!js0!ma!hm1!kgc!im9>1t$2>2t'$2>0@2$6^2^1>1m>0@1$3@1$0#k0@1$4@1$3@1$0#8@2$5@3$1?4segs^4^1@3$1?4segs^3^1").
Proof.
  intros t t' H.
  induction H as [c c' Hc | c c' | c c' | c c' | c c' | c c' | n a k k' Hk IH | n a v k k' Hk IH]; intros m;
    cbn [interp_eff_accesses]; try exact I.
  - cbn. auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (IH (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [ra| |]; destruct (interp_eff_accesses segs (k' _) m) as [rb| |];
      cbn in IH |- *; try exact IH; try contradiction.
    destruct IH as (A & B & C). rewrite C. auto.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IH (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [ra| |]; destruct (interp_eff_accesses segs k' _) as [rb| |];
      cbn in IH |- *; try exact IH; try contradiction.
    destruct IH as (A & B & C). rewrite C. auto.
Qed.

Lemma ms_reg_eqv : ltac2:(zQ "a0!h9!ma!o3!iqa!kh8!r4!r8!jhb!re!s3>2ms$3>3ms'$3>1r@1$1@1$0#5>0@1$6@3$2@1$1@1$0#5^1@3$8@1$0#5ZKv$5@2$9@1$0#5Z>0@2$7^4^3@3$2@1$1@1$0#k0@2$4^5^3@2$4^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "##0&h01Hh12HRh22Hrh32_Hh41bh52msh63ms'h71rp;1p;2p;3p;6g002nj12Tg003Sj1LTg0048j15!s/$Vj14Tg02gVj2KTg006@j3D!s/$cj30Tg007=j1JTg02D0j2ITg02E5j13Tg0059j2ATg02F4j18Tg00:Uj2@Tg02G4j1=Tg00Ioj1ETg02H5j1<Tg02I;j1;Tg02J:j17Tg02K9j19Tg02L7j1:Tg02h9j26!tL$Vj2?Tg00?Uj3BTg00[lj2H!t:$;j2FTg0023j6GTg00GQR0j2>Tf3R1f2R2f1R330f0R4'>p=11>34,>2p=Cg02PQR5g008\#2R6#L#5R7#4R8g009AR9g009_R:1K79d5D79084#J1I12P0f4R0#3%31'A%80%81'@%26!sl$2#2R2#2#5R8#4R;%=0%=130%E;R<%<0%<1P<%;0%;1%52#4R2%70%71%56#4#E\;R6%90%91%:0%:1506C1!s$%3Cf5R=/61160150;P4f6!tT%='Af7R1#8%80'@%=1%=050;P<%<1%<0P<%;1%;0P2%71%70P6%91%90%:1%:0!t00P;%31/?0R6g00F1R2P;AD79:R:9B71R<1H89R8P4n010!s#$20000P2P;P<P8f8R<#3R9/?1!sG150;X4;P2P;AB70:P8P6!sG1,F;1?90P3P0P=O2EG16<0161050;eW3W1P3P4O2n20!s]'12!s/&W0W2W7X65W5o"). Qed.

Definition msres_eqv : ltac2:(zQ "30!jic!jjd!iqa>1r@1$1@1$0$2>2r'@1$1@1$0$2P") := ltac2:(zQ "c0!iqa!jic!jjd!jkf!jn5!jl7!jnc!jof!hn2!o3!jp7!jhb\1r@1$2@1$1$0\2r'@1$2@1$1$0M2\1r@1$2@1$1$0P^2\1a@1$1$0M2\2r'@1$2@1$1$0P^2\1b@1$1$0@2$8@2$b@2$5$0^2@2$5$0^1@3$9@1$7$a@2$6$0^2@2$6$0^1$3$3M2\2r'@1$2@1$1$0P^1\6result@1$1$0$3$4$3M2\2r'@1$2@1$1$0P^1\6result@1$1$0$3$3$4").

Lemma decode_exec_accesses_eqv : ltac2:(zQ "60!ki2!iqa!h9!kjb!jhb!ma>2ms$1>3ms'$1>1w@1$5@1$2#i0>0@2$4^3^2@2$3@3$0?4segs^4^2@3$0?4segs^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "#$7dp'0h01Kh13H17h21Hh31mi001mh44Heqvh54acc'h6<access_valuei01!s60h7?!s5%ed_rangesi02!s93h83m1'h96resulti03!s0&h:1bi041bh;2c'h<1Eh=2fch>2pch?2roh@2rvhA3svchB1FhC2F'hD2H1hE2H2hF2H3hG2H4hH2H5hI2HFhJ2HRhK3HfchL2HmhM3HpchN3HrohO3HrvhP4HsvchQ1RhR2R'hS3acchT1ci051chU1ehV3fc'hW1ii061ihX3iszi073iszhY2m'i082m'hZ2m1h[2msh\3ms'h]1oi091oh^1pi0:1ph_3pc'h`3ro'ha3rv'hb4svc'hc1wi0;1ai0<7ms_fcsri0=8ms_fregsi0>6ms_memi0?9ms_pc_vali0@7ms_!sH%A!s1%svi0B6ms_romi0C>ms_svc_pendingi0D6reporti0E1xi0F1zp%0p&0p;1p;2p;3p;6p;5p;8p;4p;;p;7g002nj1WTg0048j1`!s/$Vj1]Tg02D0j2OTg003Sj1pTg01V[k100Tg02gVj2iTg006@j3_!s/$cj31Tg00K9j1tj2fTg001Vj6sTg000\j6aTg00DBk203Tg007=k102Tg02i7k501Tg02h9j2;!sV$0j2}Tg00IoS00j1bTg02j@j8!tL$E5j1DTg0059j2[Tg02F4j17Tg00:Uj2PTg02G4j19Tg02H5j1TTg02I;j1:Tg02J:j1@Tg02K9j1ATg02L7j1HTg02kGj3\Tg02lSj1rTg00=XS01j1eTg02W2R0j1dTg00b4j2YTg02SCj1qTg01KPR1j2oTg02mSj1nTg00[lj2mTg02Y:j2MTg00Lij1JTg00N^j1<Tg00OHj16Tg00aRj1~Tg00PXj18!sA$oj15Tg02Z>j2LTg02[Ej1lTg02\Mj1kTg02nDj1jTg02o=j2!vm$Rcj1|Tg00GQS02j2=!v6$;j2CTg00QAj4VTg0023j6{j7UTg030El;zTg031Qj4yTg02QXj3^!uV$cj24!u0$@j5BTg02]Uj2ITg02dMj3Z!sz$\j2xTg02_=j6wTg02OLl;vTg01oGj3cTg01j@j4uTf3R2f2R3f1R4';f0R531p=>f5R6f4R7;\2A\345'2p=KA\234/25p=gf7R8f6R9P6P7P2P3P4%H5G0p=Eg02PQS03?Z45,I3p=3%D!sI$%@4P5DBp=SAc234%A55^7p=N1O34/=5p=RP!su-P5CVCVp=X!s7,DB9c96p=h1m72?c34=^65p=Fg00UZR:!sM%Cu=Z75p=?%J8!sv1G0p=QA12!t<&GQ03Q03g008\#WR;#W#WR<!s+$=#`#]R>1O34!u/$p;#`R;%p<$00R?g009_S041i;?d3_R@%];RAg009ARBQ045_;RC71@PAg00`GRD%t;Q049_;?R?PCP5Es1f;?RE1f;CRC51DPDPEPDp-0P5g00GlREg00HIPEn0110F000300100!s'&XUDQ04!sp$aPE203E5b2b<W<Q!tc$Bd9_;B91A@$02eP5I01%W=#`R=#]RAP2P@1;3@C>Q031O571;4?R@1;6?51Ap,4segsRBP3P6PBP9P6EK]1]4P71};AS05Q05%bAR;%`<#]#b\AR<P!w/4REfCRC'Of8RF!sD1G0/;?RGfDRH/;?51AQ03f:RIf9RJP!sR-G0RK/O5PAf;RLPIP!sC-G0RMP?P@C>PBf<R@P!sF0G0RNfGROPBP3PO!u3%fERPQ!u1$fIRQfHRRPOfFRSPPPHPCfBRTG0RU/OEPAfJREPQPRPOP!sE&G0P?PGC>fKRGP!sB0G0RV#D!ti/P2P3G0RW#D'[S06%7V%7W'P%9V%9W51A%TV%TW51;%:V%:!s/$@V%@W51>%AV%AW51<%HV%HW51<PBPVfVRVPBPWPVEKQ06fLRWP!tT0G0RX#7S07%7K'PfMRKP!sH0G0S08#9S09%9M51AfNRMP!sJ0G0RY#T%TN51;fORNP!sF0G0S0:#:S0;f=RZP!w30G0#:51;fPR[P!s]0G0S0<#@f>R\P!sZ0G0#@51>fQR]P!sZ0G0S0=#Af?R^P!sZ0G0#A51<fRR_P!sZ0G0#HS0>f@R`P!sZ0G0#H51<PAP^PAfTRafSRbP5!sd,!x?$TfARcP!sa-!zW%d!yk$URePaP4P!tA+G0f`S0?PBPCPTP!s^-G0RfQ0?EK]1X>APAPbP_P^!tv,!t:$!t60PIG0S0@/;?C>P;P^PAPePaPc!tp,G0P?1;f?RfC>PBPVPePT!t[,G0faRgPBPH!tZ1G0RhPg!tW$A;PAPaPb!sA$!uk/d!tA+!s{%!tC+!tA%h?Rh!uv$WRdPV!t,$!tE&G0fbS0APB!{y%!tF,G0RiQ0A!tE$@;!uB+!tG+!tE$fC>P>!tE$!s}'!tG&!tE%i?Ri!tE$XRfPd!t-&!tG$G0fcS0BPB!}B'!tG'G0RjQ0B!tE$=>!uF-!tG&!tE$hC>P<!tE$!s},!tG$!tE%j?Rj!tE$YRhPf!t-+4P_G0fdS0C!~a,!t%%G0RkQ0C5\BS0DCg]1X3<!uJ0!tK$!tI$i!tI+!t%/cP5!tI%k?!tG$ZS0EPh!t3-4G0feS0FPB!#4/-PTPc!tJ%F!ug$?<!uI2!v/$P?PjC>Q0C#rg00F1RjPjPjQ03#eRi#dRlP5f[S0GQ0E!t%/G0Rm#D%7m%9m1;m?,YA%:m%@m%AmPmGEg02f3S0H#qRm53iQ00g0247Rn/oDRoPlffRp#nS0IP1PnPDPlP5P01o:<Rq#eRrPlPB1m=5RsP4f^S0Jf]!#4l1t%7t%9tPt%:tDSPtDNP1P:P<Pl1Mq5Rt%J4Ru%<4Rv%64Rw%~ARx%84Ry%54RzP5PgQ0?!#4`0R{GE1Lq3R|53in200110E000120105108%liR}%kiR~n1!sC'31010D0000!sX&:!sX$1106107PjPl%jpS0KP}P~n!#<v$0020000Rp!sl,21!s`%!sH01PjPlP5%DU%7U%9U1;U?,YAS0L%:U%@U%AUPUGE=3imQ00PoPlQ!vn1P!vf$PsP4PXQ07%9XPX%:XDSPX!vM,PtPuPvPwPxPyPzP5Q0:!sz$|!ux7!u<$!urK!uVD'2P5PA1;k?RpQ!yy&1YA5!y{,!xa%Q0L!s9,Q0H#|RX?1mmS0H3RX:AQ!{v%1YApS0L!{b-p!yG%Q!s;0U'OQ0H%Dp%DU'[%7p%7U'PS0H%9p%9US0751AS0I%Tp%TUS0M51;S0N%:p%:US0O!s5$P%@p%@US0Q51>S0R%Ap%AUS0S51<S0T%Hp%HURU!s4$U'=S0V'=S0W'=S0X'=S0Y'=Rp'=P\Q0HPpPZQ0IQ0YQ07,CAQ0NQ0XQ0M,C;Q0PQ0WQ0O!s2$RQ0VQ0Q,C>Q0TQ0UQ0S,C<1C<UCVFXFXFX1CXmCVQ!#3#1!um$/;?R?P4E{!yg,YA?!ya4%Dk%7k%9kQ0L%:k%@k%AkPk!sC%'2eQ0F#n%bo!z1$!z6&P5!z59f_RmQ0J!#??0R!t-&Pk%:kDSPk!zJ?APg!#>`0!zZjjPlfg#j!}L6k!zt5!u\BQ08Q08#7Q09!s1&:DSQ08!uN?<!u>j!t|6!|d$!tw%!t}:?Pm!#CP1m!#7p$Pm%:mDSPm!u1?BQ0A!#Bb0!uBj!t|8PY%7Y%9YPY%:YDSPY!ti?=!tXi!v`$sP4!#8r&EPGFhRY!s9$!uo%!s8%mPgPNQ0?!s9'!sG$PPHM;zPQCyA^BYQA^BmQ'4PBP=P4P3!{8'GPWDBPEEF%drS0A!uh$BP=P2P7!#C8%KPMDBPWEFS0=,4!v2'4!us;PNG0!ur;Rm!ut;!w0+=P7P6Pb!tJ$MPNDBPKEFP!s^<'2]0P5Q01Pq1Ir5Rm!si$6P9Pa!sk$NP[DBPMEF'!u#+1Mq4S0<!u+2[G01Lq2RY!#<a9!to-9P8Pe!t-$[P]DBPNEF!v'<]!v'=S!xz=!uL%!s{%AZq45,IrRk!tK$JPIPfPdPVPbPaDBP_!uQ/AZq34,MqS09!tV2aG0AZq72,LqRU!uYEIPLPh!t6$aPeDBPb!uY>e!uY=!uV?^7XP5PqP<!#Xj%?,IrRa!tL$@PZ!#<t%hPVPdDBPe!u\$BP=PZP\f\Re!sF&dPfDBPVEFQ!zy&qP<!#Q~$D?Rd,Ir/45!u/+qP<!#RD$D?,Mq!}i3EG0!sH$FP8P9D?R?,Lq!vGA!{i<Q0G!v2Y!{0&!tV$8P9P6D?S0G!u=$m!z}-?!wH5Re!s[$IPJPFD!u1?!sl&Q0<A3ieY!sJ7!z</!s|$LPIPJ!wg$/4k!vm0@PLPI!vm8?!tb+\PZP@!voB!td+9A3ieU!td;!yJ$1Ir?/4a1x^2S0?A1<\3A1XZ4R?%J^S0E%<^S00%6^S0LPx%8^S0S%5^S0UP\PgG0P2%<2%62Px%82%52P3PgGQ;R?Q0?Q02%J`%J7'[%<`%<7'PPA%6`%67P>%5`S0T%57%8`S0Q%8751;CGCG'=A1<`7A1X`7%JCS0V%<CR?%6CS0RPx%8CRg%5CS0OPTQ0FG0P8%<8Re%68S0WPx%88Rp%58S0PP9Q0FGQA1Xc63R[[P5%JT%J9'[1P?ePAQ0RQ0WP>Q0OQ0PA1;gp!tP%Q02%<H%<F!u$%H%6FP>%5H%5F%8H%8F!tz&A1<HFA1XHF%JOS0P%<OS0W%6ORpPx%8ORe%5OROPSfiS!ty$L%<L%6LS0MPx%8LS0X%5LS0NPI!tx'PJ!tx&<SRJ%<I'PPAPpQ0MP>PO!#Dr$91;eCGCGQ02%6R%6@51AP>%5R%5@%8R%8@!tm$A1<R@A1XR@PG%<G%6GPx%8GRR%5GR@PEfmRIGQQ0EQ00Q0LPxQ0SQ!xF$IG0A1XQZ!tX&6E%6\!t2$P@!#Eu$91;R!tN%5WQ0T51>%8WQ0Q51;A1<W`A1XW`PN%<N%6NPx%8NRR%5NPMfqR@GQQ0VP?Q0RPxPgQ0OPTP@!t@$Kc!t@&5M%5T51>A1;RgA1<NCP<P[A1X[HPb%<b%6bPx%8b%5bP_fuRRGQRg!#G{$PpPxPePOP4PR!s{$]P3R[X8<A1XNCPXP[!sN2_!sN'55RgX5XP_%<_%6_Px%8_%5_P]ftRgGQRRPSPJ%6SPx%8S%5SP]PgGQRg'OA1X[[%DR%Dg'[S0W%7R%7g'PRS%9R%9g51ARJ%TR%TgR!#K/&:R%:g51;Re%@R%@g51>Rp%AR%AgR@51<S0O%HR%HgRg!s4$R'=RR'=R?'=RE'=RQ'=RI'=P^Q0WePSPIPLPSePJPQP8PJeQ0PPE1C;OPeP?P3PeePpPRP2Ppe!{T$R1C<@1C<g!#K%,[CVPHP5EaW2!s-'WHWGP4P5O2n2!#h>%0012!s/&W2WF!sD@E!sD@D!sD?P5Ew!#5t/^P\PZ!#5t7BG0RZ!sJ$cP`P^!#7XF!sT$2P3P4!sx$R^1LqdR\93iZ!#6,8eW0X5XX8<X;:!u,-10:01!#E9$5109X6q!sC&10110;!sB'1102X9rP5O1!tH$7P2P3!#=;$Z%lrRg'4!#8r'l1Mqd!uY1PhG0RdQ0G!uO=R@/2}eW0%krRp,4ZP512@~eW0!tX%00103111030101P4O1b3W0XSXXZ<XT!uHbBP=P3P2!#c8%WPKDBPGEFR=,4gQ0=!#?4%14g!#Fm'Q!#=P<R@,2}!#E]+4gm!#<T,!v52_G0=3i!#<e7RY!sm&!sd%14gk!sn,!#CV2V!sn$!#;o7RU!sn$!#;r$4ga!wm,P^A3id\!s[8d,!wS$!yHW0!v~414ggP512}}eW014gp!s3$!xJ/0!xJ'000!xJ'14p=!wC/p512~@!vw-pm12~Y!vA/pk12~U!uc+paP512~d!u?np!u?$~!u?%p!u?$~!u?C!{#=b0!#Pa/{%7{%9{P{%:{DSP{!#Pa>CQ0B!#mV0!#PrT!#T+0:Q0:#7Q0:#9!s3$;DSQ0:!tR?>!#FUVeXXDXWn!wN9610FX^oP5O1Q0KPj!s$$lP5!#X^5~/2~P5Q04Q04n01104!sA'b:!tH%901!#V{'b]!sJ&1020101b:PB!#iC1`G0!vu$DCgeW1P]P6P5FU!s0RFFUPB!#Qf%!#pD,Q0JPBQ0@Q0JEKeWNWLWKWOWPWMWIWJP4M;vW1W4X`<XY<XV>Xa;Xb;X_AWCWR!#z-2O8n!z''18110@10=10?10C10A10<10>10B!w#%!s|$?<W3X=>X@;WAX>AWBWQ!sz_b1W4WcW\W[o"). Qed.

Lemma step_accesses_eqv : ltac2:(zQ "40!iqa!kk8!kjb!jhb>2ms$0>3ms'$0>0@2$3^2^1@2$2@2$1?4segs^3@2$1?4segs^2").
Proof.
  intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
  unfold RiscvSemantics.step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
  destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_eqv; exact Heqv|].
  unfold fetch_failure. destruct (vdso_text_at segs (ms_pc_val ms)); [exact I|]. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

(* [comment removed for export] *)
Definition mres_eqv : ltac2:(zQ "40!ji4!jjd!iqa!ko7>1r@1$1@2$0$2$3>2r'@1$1@2$0$2$3P") := ltac2:(zQ "90!ko7!ji4!iqa!jjd!jkf!jn5!hn2!o3!jhb\1r@1$3@2$1$2$0\2r'@1$3@2$1$2$0M3\1r@1$3@2$1$2$0P^2\6result@2$1$2$0M1\6result@2$1$2$0P^1\1a$2\2mo$0M3\2r'@1$3@2$1$2$0P^4\7result0@2$1$2$0M1\7result0@2$1$2$0P^1\1b$2\3mo'$0@2$6@2$8^5^2@3$7$0^4^1$4$4M3\2r'@1$3@2$1$2$0P^1\6result@2$1$2$0$4$5$4M3\2r'@1$3@2$1$2$0P^1\6result@2$1$2$0$4$4$5").

Lemma mi_account_step_eqv : ltac2:(zQ "50!iqa!krc!ko7!ksf!jhb>2ms$0>3ms'$0>2mo$2>0@2$4^3^2@2$3@3$1?4segs^4^2@3$1?4segs^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "##;>p'0h01Kh11mi001mh21bh34Heqvh42K1h52K2h61ah71lh82moh92msh:3ms'h;1oi011oi026model'i032r'i046reporti056resulti061xp;2p;3p;1p;4p;6g02D0j29Tg03<`j3ITg032gj26Tg02o=j21Tg00=Xj1HTg02W2R0j1>Tg01KPj2DTg03>0j22Tg02[Ej1<Tg02\Mj1;Tg03?9j20Tg02]Uj27Tg02Rcj1GTg006cj3:Tg00IoR1j1FTg00:;j2ETg00QAj4CTg000\j6BTg00DBj28Tg03@@j3=Tg02Z>j2ATg02Y:j2@Tg01j@j4?Tg02PQR2f0R3'Ap=51@23p=4f2R4P2g03A<R5f1R6P3C?'7p=31946f3R7?I43p,4segsR8/671684'1f4R9,68R:%H2R;#>R<P0P;f5R=,68R>,13P0P;1D25R?#>R@P6P1P5P@f6RA%53RB'2%46RC=3?3RD%<?REn10110600021010200RFPE%;?RG!sA,3101040000P0P;P@168ARHPFPEP!sL8'0]0P317;3RF/1Hf7RH,68P!t|$17;7/13!tg&9RI%59RJ'2%4=RK=3?3P!tb6!tE%!uE+:RL/2BPD!sQ8!tbC9/1Fg00GQ19KCg02f3#GRK%5=R=%56RC3:!t4&;RM%5A'2%4HRH!vQ$N!t?8!sT$%54,2M%47RO!u;;'0P319HOf8RO#5=:KJPK%5IRI!t>&?RJ%5L'2%4M!u~<!sP$12J3P!tZ8'0X7Kf>/2I%F5!sS$!sW$P3f<#4RI!s}AP3%4O!wJ=!u5%IKA:533P91E53CCX15P3O1g009_!sY%1!sY'000b;P=P3EBW5W4P6P3O2n20!sA%0012!s-%!uK+L=%4A!upCLC%44!wS$L!ts9eW0X2;P3O117;4RA%<;R='1!wl'7,2O%49!t5;RK/0ERI/83PIeW0%;;RI,1A10KGRK/83PKeW0!s]%0!yu$1105!u;$6O1b1W0X6!tJ%1=:P>!{X&1=3!{#112O!z|RRD,0E!{#$1=FP0P?p-0RB!st+CP!v+8RLg00GlROg00HIRCPO!sJ%3!t&'!u1$/8310EL!vW-1==P310EEeW011=I!s3$G!up20!up211I!ui-I310GD!u$%I!u$$PBPLPOPOPC!tS<G!tS0I!tS$G!tS%I!tS$G!tSC!wa=A=894A=874'0eb0W3X85X:2X92o"). Qed.

Lemma syscall_args_eqv : ltac2:(zQ "70!iqa!ktb!jof!o3!h9!jhb!ma>2ms$0>3ms'$0>0@2$5^2^1@3$3@1$2@1$6@1$4#k0@1$1^3@1$1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "##9tp'0h01Eh11Hh21bh32HRh42_Hh51eh62msh73ms'i001zp;2p;1p;3p;6g02D0j2ZTg02E5j15Tg0059j2MTg02F4j1BTg00:Uj2OTg002nj16Tg0048j1F!s/$Vj1ETg02G4j1DTg006cj30Tg00Ioj1LTg02H5j1ATg02I;j1CTg02J:j1HTg02K9j1JTg02L7j1ITg02Rcj1WTg03B2j1GTg003Sj1VTg01V[j1U!sA$kj19Tg03CKj2=Tg00[lj28Tg007Vj21!sA$hj1@Tg02SCj1TTg02^]j33!uE$;j2S!ty$@j3RTg00K9j1Qj27Tg00DBj2P!sq$=j1?!ul$3j6:Tg00GQR0j2KTg001Vj6YTg000\j6XTf3R1f2R2f1R330f0R4'Kp=41K34,K2p=Nf4R5A3234731p=2P5g00`GR6P1P2P3P4EYp=;A0634p=<P!s=$g009_R7!sD$Xp=>g02PQR81Z34P0%52%53'M%B2%B3'Og008\#6R0#6#6R9!s+$:#6#F#ER;%D2%D330%L;R<%A2%A3P<%C2%C3%F:#ER:%H2%H3%F9#E#L\;R9%J2%J3%I2%I3509C4!s$%3N%W;R=%G1%G230P4%55%51'Mf5R1#B%B5'O%D1%D550;P<%A1%A5P<%C1%C5P:%H1%H5P9%J1%J5%I1%I5!t+0P;%51R9%V0R0#FR5%60#UR0g03DGR:#9'='8R<'1R2P;P4P;f7#5R>%@:R:#9,=0,85R?'1!s71@,1!sI2A!s84B!s8%!s6+0,1>%T;R>53;R:53;RC53;RD53;RED2P;f6RF#5RG/1<RHP;11G?RI!s-$@RJ!s-$ARK!s-$BRL!s-$0RGP>D2D2D2RM50=X2;P;119?RNP;PH!uG$ED2=0=M!sA'@RE!sA&IA3;4D!sD1ARD!sD'P;PJ!sg$CD2!sK1BRC!sK2KA3;4:!sN30R9!sN3P;PL!s{$!u+&!sU+P2P;PNP;PEP;PDP;PCP;P9!sM',S=PGP3P0%E5RGg009A=R57R7700R>PG%Q5R9P0P7P4D;1750R01757R;'<P0P6p-0P4g00GlR0g00HIP0n01100000300!s/$!s'$X56R6P;P4C>P01P04RCb1b0W0%?>eO2E:PLP3PBA0GB7RLPGP9PB!tC+BRB/<;PBP!sh+P!sd+L!sd%KP3PAA0GA7RK!sd$A!sd+ARA/<;PA!sd7K!sd%JP3P@A0G@7RJ!sd$@!sd+@R@/<;P@!sd7J!sd%IP3P?A0G?7RI!sd$?!sd+?R?/<;P?!sd7I!sd%HP3P<A0G<7RH!sd$<!sd+<R</<;P<!sd7H!sd$%GF%G150=eW4W3P3P4O2n2!w:&0012!s/&W1X78W6o"). Qed.

Lemma sys_input_eqv : ltac2:(zQ "70!iqa!kub!o3!h9!kv8!jhb!ma>2ms$0>3ms'$0>2x8@1$6@1$3#k0>0@2$5^3^2@3$2$4@3$1?4segs^4^2@3$1?4segs^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "##CFp'0h02Hah14Heqvh22fch31mi001mh42pch52roh62rvh73svch81Fh92F'h:2HFh;2HRh<3Hfch=2Hmh>3Hpch?3Hroh@3HrvhA4HsvchB1RhC2R'hD3fc'hE1lhF2m'hG2mshH3ms'hI3pc'hJ3ro'hK3rv'hL4svc'hM2x8i017ms_fcsri028ms_fregsi036ms_memi049ms_pc_vali057ms_!sH%6!s1%svi076ms_romi08>ms_svc_pendingp;1p;2p;3p;8p;4p;6p;7p;;g002nj16Tg0048j1@!s/$Vj1CTg02D0j27Tg03Dfj3RTg02Rcj1QTg03B2j13Tg006cj31Tg003Sj1LTg0000j2JTg00Ioj1ETg02j@j80Tg02E5j1HTg0059j2PTg02F4j1=Tg00:Uj2GTg02G4j1<Tg02H5j1:Tg02I;j18Tg02J:j1;Tg02K9j19Tg02L7j1?Tg03F5j3>!s/$kj1DTg03Goj2ATg03I7j4B!t1$;j2KTg0023j6Nj75Tg02OLl;OTf2R0f1R1#3f0R231p=2g03J4R3f5R4f4R5f3R63>A>01!sE$4f7R7f6R8P4P5P6P0P1P2G0#3p=IA>601=132p=FA1312p=Mg02PQR9g008\#6R:#6#6R;!s+$<#6#@#CR=1701AR602%Q=R>%30726P91725%31R?%3451>p,4segsR@P0P4P@P8P4E4]0]1P5%L:#@/J=R:%E=RA%@<#CR<%@;#C#E\=R;P7P!t~2RBfCRC'7f8RD!sD1GIREfDRF#351>P9f:RGf9RHP!sM-G0RI/72f;RJPGP!sA-G0RK=2>?P@f<R?P!sD0G0RLfGRMP@P0PM!u1%fERNfIROfHRPPMfFRQPNPFPCfBRRG0/7BfJRBPOPPPMP!sA&G0=2>EfKREP!s@0G0RS#H!t[/P6P0G0RT#H'PRU%=S%=T'G%<S%<T51=%:S%:T51A%8S%8!s/$;S%;T51<%9S%9T51;%?S%?T51;P@PSfVRSP@PTPSE4fLRTP!tP0G0#=%=I'GfMRIP!sC0G0#<%<K51=fNRKP!sD0G0#:%:L51AfORLP!sD0G0#8f=RVP!vh0G0#851AfPRWP!sW0G0#;f>ROP!sW0G0#;51<fQRXP!sW0G0#9f?!v}$!sW-G0#951;fRRYP!sW0G0#?f@!w<&!sW+G0#?51;P=PBfTRHfSRZP2!s_,G0PRfAR[P!s]-GIR\52>P@fUR]PHP1P!t8+G0f`R^P@PCPRP!s[-G0R_P^E4]0X4=PZPYPB!ti,G0!sQ/PJPGG0RG#352>PAPBP]PHP[!tc,G0%3_R_!tP$PSP]PR!tP,G0faRJP@PF!tP1G0RVPJ!tN$7APHPZ!s?$!uZ+=2>\!t9$!su%!t;+G0%3VRV!uc%WR\PS!s}$!t=&G0fb!t;$N!t=1G0RO!t;&6A!u4&!t=+!t;$_P<PBP!su'!t=&G0%3ORO!t;%XR_P\!s}&!t=$G0fcRHP@!|T'!t='G0RJPH!t;$2<!u6+!t=&!t;$VP;PBP!su,!t=$G0%3JRJ!t;%YRVP_!s}+1PYG0fdR]!}i,!sz%G0RH=>@]R?CF]0X3;!u8-!t?$!t=$O!t=$!sw/[P2G0%3H!uR'ZRSPV!t%-1G0fe!yL$P!tA1G0RM!yL&5;!u80!uo$=2>JP>POP^P2P!sy1[G0RQ#D1A@QCBP^%3M%DM1A@MCB'MXE>P]PO%DH1A@HCB,K3!t~2EG0RE#3P2ENP@PEP]P?CFeW0PXP4P2F5!s0RDF5P@!{\$!}G-G0f^RTP@PGPTE4eW?W=W<W@WAW>W:X;UP1M;OW0W1XJ;XF;XD<XKAXLAXI=X9:XC:!#8a2O8n01100000181105102104108106101103107!sP$2!s~$5;W3W2X6AW7X4=X8:WB!sz_b0W1WMXH9WGo"). Qed.

Lemma apply_effect_eqv : ltac2:(zQ "40!iqa!lg8!jhb!lh8>2ms$0>3ms'$0>3eff$3>0@2$2^3^2@2$2@2$1^4^2@2$1^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "##ACp'0h03effh12fch21mi001mh33ms'h42pch52roh62rvh73svch81Fh92F'h:2HFh;2HRh<3Hfch=2Hmh>3Hpch?3Hroh@3HrvhA4HsvchB1RhC2R'hD3fc'hE2m'hF2mshG5nd_i5hH3pc'hI3ro'hJ3rv'hK4svc'i017ms_fcsri028ms_fregsi036ms_memi049ms_pc_vali057ms_!sH%6!s1%svi076ms_romi08>ms_svc_pendingp;2p;1p;8p;3p;5p;4p;6p;;g02D0j2@Tg03K1j2ATg002nj1;Tg003Sj1WTg0048j1C!s/$Vj1HTg0000j2TTg00Ioj1KTg02j@j80Tg02E5j1:Tg0059j2JTg02F4j13Tg00:Uj2ITg02G4j14Tg006cj31Tg02H5j17Tg02I;j18Tg02J:j16Tg02K9j15Tg02L7j19Tg01V[j1V!se$@j3L!u3$jj1STg00@Bj5BTg03L`j1RTg03MYj2GTg03NRj1QTg03OJj2FTg03PBj1PTg03Q;j3DTg03R4j1O!s/$mj2ETg00GQj2=Tg00SJj5N!u<$;j2>Tg00QAj4<Tg00?Uj3M!vY$3j6?Tg02OLl;UTf2R0f1R1'Af0R2'@p=2g02PQR3P3g03SfR41@01f3R51A01R6721[]0^33P2g008\#;R7#WR8#CR9%;7!s5$;#;R:#;#C#HR;'TR<%K;R=%C:#HR:%C7#H#K\;R7P3f:R>f9R?f8R@f7RAf6RBf5RCf4RDP5G0RE/@1f;RFP>P?P@PAPBPCPDG0RG?216[^04P2fIR6fHRHfGRIfFRJfERKfDRLfCRMfBRNG0!s`,P5P0P1G0'@fJROP6PHPIPJPKPLPMG0RM#:!t6/P5P0G0RP#:'JRQ%3M%3P'I%4M%4P51;%7M%7P51=%8M%8!s/$6M%6P51:%5M%5P517%9M%9P5171AP192M1fKRMP!tH0G0#3%3E'IfLREP!sC0G0#4%4G51;fMRGP!sD0G0#7f<RJP!v;0G0#751=fNRKP!sW0G0#8f=RIP!sW0G0#851=fORLP!sW0G0#6f>R!tV%!sW+G0#651:fPRPP!sW0G0#5f?R!u/'!sW&G0#5517fQR@P!sW0G0#9f@!wG-!sW$G0#9517P;P6fSRRfRRSP2!s_,G0PNfARN!v?-FG0/A>RT72>X4;P=PHPRPSPOP2!s[,?2>TX7=P=PI!sC&6P2!sC06=P:PJ!sC+HP2!sC-1:P7PF!sC-IP2!sC+27P7P>!sC0JP2!sC&57P9P;%;8#Vg009_R85L9RT%S?RRPSDBP@!sY'%R?RU,GF%Q?RV'F%P?RW5DF%O?RX'ERYP>G0RZ#:P9P;PTPRPNDB!t?-!sF%Y!zd$[%3Z%3Y'IR\%4Z%4YR]51;R^%7Z%7YR_51=R`%8Z%8YRa51=Rb%6Z%6YRc51:Rd%5Z%5YRe517Rf%9Z%9YRY517RZ'=Rg'=Rh'=Ri'=Rj'=Rk'=PSPN!t`$ADNP[eP\PkPBP\eP^Pj1>;]P`Pi1>=_PbPh1>=aPdPg1>:cPfPZ1>7e1>7YC<!s$/g00F1RYP3g009A=L989M9TR8PS!vN,PF!uh$e!v-'%:eDB%3e%4e%7e%8e%6e%5e%9eG0n010!s#$2000!vd$%3Z%4Z%7Z%8Z%6Z%5ZRf1GfU/FV;DW/EX%9ZG0PYP3P8P!z+0!tD$>!tD,>DB%3>%4>%7>%8>%6>%5>%9>!tD4R#:%3R%4R%7R%8R%6R%5RRT1GT!tD/RG0'@e1A>?R>92e?ePMP2E?PEP1E?PGP0E?PKP5E?PLPDE?PPPCE?!v6$!|k-G0?2?>eW?W=W<W@WAW>W:X;QP2M;UWGX04XI7XE7XD:XJ=XK=XH;X9<XC<!#5z0P2O8n01!u=%181105102104108106101103107X33X57W2W1X6=W7X4;X8<WB!ssYWFo"). Qed.

Lemma advance_past_svc_eqv : ltac2:(zQ "30!iqa!li9!jhb>2ms$0>3ms'$0>0@2$2^2^1@2$2@1$1^3@1$1^2").
Proof.
  intros [R F pc svc rv fc m ro] [R' F' pc' svc' rv' fc' m' ro']
         (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
  unfold advance_past_svc, ms_pc; simpl. repeat split; auto.
Qed.

Definition cfg_eqv : ltac2:(zQ "10!lje>1c$0>2c'$0P") := ltac2:(zQ "70!lk8!ll5!lje!hn2!o3!ko7!jhb\1c$2\2c'$2@2$3@2$6@1$1^2@1$1^1@3$4$5@1$0^2@1$0^1").

Lemma cfg_eqv_sym : ltac2:(zQ "20!lje!llf>1c$0>2c'$0>0@2$1^2^1@2$1^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_RegsEquivM ()) ["WithSegs"] "h01Hh12H1h22H2h31ch42c'p;2p;1p;3p;4g03Uaj24Tg03Vgj10Tg02D0j22Tg03WZj11Tg006cj33Tg03XPj37Tg008@j46Tg00QAj45Tg03YYR0f1R1f0R2'4g00GQf2R3#0%01'2g03A<R4%13%1133f3R5,43P2f4R3#0%05'2f5R5#1R6%13534%05R5f6R3#0R7'2%13R39346A7751P4P3P6P2C6C5W2W1P1P2O2n2001000000120000000W0X40W3o"). Qed.

Definition to_eqv : ltac2:(zQ "10!lma>1X$0>2X'$0P") := ltac2:(zQ "50!lma!lje!jkf!jn5!llf\1X$0\2X'$0M0\1X$0P^2\1c$1M0\2X'$0P^2\2c'$1@2$4^2^1$2M0\2X'$0P^1\1c$1$2$3").

(* [comment removed for export] *)
Lemma vdq_ms_reg : forall ms ms' r, ms_eqv ms ms' -> ms_reg ms r = ms_reg ms' r.
Proof.
  intros ms ms' r H. unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  destruct H as (HR & _). apply HR. intros Hc. rewrite Hc in E. vm_compute in E. discriminate E.
Qed.

Lemma vdq_ms_sp : forall ms ms', ms_eqv ms ms' -> ms_sp ms = ms_sp ms'.
Proof.
  intros ms ms' (HR & _). unfold ms_sp. apply HR.
  intros E. apply (f_equal bv_unsigned) in E. discriminate E.
Qed.

Lemma vdq_read_byte : forall ms ms', ms_eqv ms ms' -> ms_read_byte ms = ms_read_byte ms'.
Proof.
  intros ms ms' (_ & _ & _ & _ & _ & _ & Hm & Hrom). unfold ms_read_byte. rewrite Hm, Hrom. reflexivity.
Qed.

Lemma vdq_read_regs : forall ms ms', ms_eqv ms ms' -> vdso_read_regs ms = vdso_read_regs ms'.
Proof. intros ms ms' H. unfold vdso_read_regs. apply List.map_ext. intros r. apply vdq_ms_reg, H. Qed.

Lemma vdq_set_reg : forall ms ms' r v, ms_eqv ms ms' -> ms_eqv (set_reg ms r v) (set_reg ms' r v).
Proof.
  intros ms ms' r v H. pose proof H as H0. destruct H as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold set_reg. destruct (bv_eqb r 0); [exact H0|].
  cbn. repeat split; auto. apply regs_eqv_set, HR.
Qed.

Lemma vdq_write_regs : forall rs vs ms ms', ms_eqv ms ms' ->
  ms_eqv (vdso_write_regs ms rs vs) (vdso_write_regs ms' rs vs).
Proof.
  induction rs as [|r rs IH]; intros vs ms ms' H; [exact H|].
  destruct vs as [|v vs]; [exact H|].
  cbn [vdso_write_regs]. apply IH. apply vdq_set_reg. exact H.
Qed.

Lemma vdq_with_mem : forall ms ms' m, ms_eqv ms ms' -> ms_eqv (vdso_with_mem ms m) (vdso_with_mem ms' m).
Proof. intros ms ms' m (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom). unfold vdso_with_mem. repeat split; auto. Qed.

Lemma vdq_set_pc : forall ms ms' pc, ms_eqv ms ms' -> ms_eqv (vdso_set_pc ms pc) (vdso_set_pc ms' pc).
Proof. intros ms ms' pc (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom). unfold vdso_set_pc. repeat split; auto. Qed.

Lemma vdq_post : forall ms ms' model fr eff, ms_eqv ms ms' ->
  ms_eqv (vdso_post segs ms model fr eff) (vdso_post segs ms' model fr eff).
Proof.
  intros ms ms' model fr eff H.
  unfold vdso_post. cbv zeta.
  rewrite (vdq_ms_reg ms ms' _ H), (vdq_ms_sp ms ms' H), (vdq_read_regs ms ms' H), (vdq_read_byte ms ms' H).
  match goal with |- ms_eqv (vdso_set_pc (apply_effect (vdso_with_mem (vdso_write_regs ms ?rs ?vs) _) _) _) _ =>
    pose proof (vdq_write_regs rs vs ms ms' H) as HW end.
  pose proof HW as (_ & _ & _ & _ & _ & _ & Hmw & _).
  rewrite Hmw.
  apply vdq_set_pc. apply apply_effect_eqv. apply vdq_with_mem. exact HW.
Qed.

Lemma sstep_scfg_eqv : ltac2:(zQ "c0!lma!iqa!ln5!lne!jof!hn2!lob!lp0!ko7!lpf!lq8!jhb>4scfg$7>2ms$1>3ms'$1>2mo$8>3evs@1$4$9>1X$0>0@2$b^5^4>0@5$3?4segs^7@2$2^6^4^3^2@2$6$0\2X'$0@2$5@5$3?4segs^9@2$2^7^6^5^1@2$a^4^1").
Proof.
  intros scfg ms ms' mo evs X Heqv Hst.
  pose proof (mi_account_step_eqv ms ms' mo Heqv) as Hres.
  pose proof Heqv as (_ & _ & Hpc & Hsvc & _ & _ & _ & _).
  inversion Hst; subst.
  -
    match goal with Hx : mi_account_step _ _ _ = _ |- _ => rewrite Hx in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    destruct Hres as [Hres <-].
    exists (SNext (mkCfg ms1' model')). split; [apply sstep_cfg_instr; auto; congruence|]. split; [exact Hres| reflexivity].
  - match goal with Hx : mi_account_step _ _ _ = _ |- _ => rewrite Hx in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [apply sstep_cfg_instr_fault; auto; congruence| exact I].
  - match goal with Hx : mi_account_step _ _ _ = _ |- _ => rewrite Hx in Hres end. destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    apply sstep_cfg_instr_unmodeled; first [assumption | congruence | (unfold ms_pc in *; rewrite <- Hpc; assumption)].
  - match goal with Hx : mi_account_step _ _ _ = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    eexists. split.
    + eapply sstep_cfg_vdso_call;
        first [ eassumption | congruence
              | (unfold ms_pc in *; rewrite <- Hpc; eassumption)
              | (rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption) ].
    + split; [apply vdq_post; exact Heqv | reflexivity].
  - match goal with Hx : mi_account_step _ _ _ = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    eapply sstep_cfg_vdso_materialization_fault;
      first [ eassumption | congruence
            | (unfold ms_pc in *; rewrite <- Hpc; eassumption)
            | (rewrite <- (sys_input_eqv ms ms' _ Heqv); eassumption) ].
  - match goal with Hx : mi_account_step _ _ _ = _ |- _ => rewrite Hx in Hres end.
    destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E; simpl in Hres; try contradiction.
    exists SError. split; [|exact I].
    eapply sstep_cfg_vdso_unmodeled;
      [ eassumption | congruence | eassumption | (unfold ms_pc in *; rewrite <- Hpc; eassumption) | ].
    match goal with Hun : vdso_call_unmodeled _ _ _ _ |- _ =>
      unfold vdso_call_unmodeled in Hun |- *;
      destruct Hun as [Hn0 | [(n0 & Hn0 & Hsp0) | (n0 & e0 & m0 & v0 & Hn0 & Hsp0 & Hor)]] end.
    * left. exact Hn0.
    * right. left. exists n0. split; [exact Hn0|]. rewrite <- (sys_input_eqv ms ms' _ Heqv). exact Hsp0.
    * right. right. exists n0, e0, m0, v0. split; [exact Hn0|]. split; [|exact Hor].
      rewrite <- (sys_input_eqv ms ms' _ Heqv). exact Hsp0.
  -
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms' eff)) model'')). split.
    + apply (sstep_cfg_syscall segs scfg ms' mo x8 eff model' model'' evs);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
        | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption | assumption| assumption].
    + split; [| reflexivity]. apply advance_past_svc_eqv, apply_effect_eqv, Heqv.
  -
    exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_materialization_fault segs scfg ms' mo x8 eff model' evs0);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption
      | rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_exit segs scfg ms' mo x8 eff model' evs0 code);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption| assumption].
    + split; [exact Heqv| reflexivity].
  -
    exists (SNext (mkCfg ms' model')). split.
    + apply (sstep_cfg_killed segs scfg ms' mo x8 eff model' evs0 sig);
        [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption| assumption].
    + split; [exact Heqv| reflexivity].
  - exists SError. split; [|exact I].
    apply (sstep_cfg_syscall_unmodeled segs scfg ms' mo x8);
      [assumption| congruence| rewrite <- (sys_input_eqv ms ms' x8 Heqv); assumption].
Qed.

Lemma sstep_scfg_cfg_eqv : ltac2:(zQ "a0!lma!lje!lne!jof!hn2!lob!lp0!lpf!llf!lq8>4scfg$6>1c$1>2c'$1>3evs@1$3$7>1X$0>0@2$8^4^3>0@5$2?4segs^6^5^3^2@2$5$0\2X'$0@2$4@5$2?4segs^8^6^5^1@2$9^4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) ["WithSegs"] "##/ap'0h02X'h13Hsth21Xh33evsh42c'h52moh61Hh73Hmoh83Hmsh91ci001ch:3mo'h;2msh<3ms'h=4scfgi019cfg_modeli026!s3$sp;1p;2p;5p;3p;8p;7g02Rcj1<Tg03Uaj27Tg03]Zj51Tg03\Uj26Tg00GQR0j25Tg03ojj24Tg03[`j20Tg03Vgj13Tg02D0j29Tg03WZj12Tg006cj38Tg047Ej8;Tg0023j7:Tg046Kg03YYR1P1g045U#<R2g043iR3f3R4f2R5'7p,4segsR6f6R7f4R8P5f1R9D1P6f8R:f5R;P8f0R<D1164<R='5X03,43[[]2]3^41P<g02PQR>g03A<R?P110;8/75P6f:R@107;RAP5P!sz%<RBP;P8P<D1/5=!sq'^23^32P<f7R=,0:1045'7P0f9R0/0:RC#31084RD#3'9%2C%2D58?P6f>RD10@0P4P5!t+$@10=7R5P;P!t~$8<!t|+P<f;R8/0@#3%3A'910B8R8#2%25!sq%Af=R5/0BP7P;D1P?P:P6fCR;f?RB/0<P:P=!t1$EP8P@!t,%0!t,+]1X5?P6fB10D:P=P7D1P;PBP@P0P:P=P4P<G;W1P5P9P<F:W1W7W8P9P<O2n20010!s#$12!s-%0W6X23X32X:?X<>!sN&011!sL'102101X41W5W;!sE;W9W=o"). Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reg_of_nat : ltac2:(zQ "90!h9!lr2!ma!hn2!o3!lob!lsd!lub!lv5>1r@1$2@1$0#5@2$5$1\1n$1@2$3@3$4@1$2@1$0#5^2@2$8@1$0#5@1$7^1@2$6^1Ni0").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##>\h04__x1h16__sat1h24__p1h37__arithh44__ffh58__varmaph65__with71nh82Hah94__p2h:4__p3h;!sq%0h<!s/%2h=4__x2h>2b1h?2b2h@1xhA1zhB1HhC2H0hD2HrhE1rhF2z0p;1p;2p;3p;4p;6p;7p;8p;<g002nj1:Tg003Sj1xTg0048j1Z!s/$Vj18Tg03BkR0j1MTg00[lj2>Tg006cj30Tg03Chj14Tg048RR1j2GTg00GQR2j22Tg00K9j23!sE$jR3j1NTg049Jj2pTg04:=j1d!s/$fR4j21Tg04;Bj3_!s/$fj2^Tg01V[j1ATg04<Lj2[Tg04=4j2L!s/$Qj3WTg04>5j2VTg00:;j2=Tg02SCj1TTg02Rcj1S!sJ$Vj2HTg04?4j1R!s/$Rj1QTg04@=j2D!s/$`j2FTg04ACj4;!s/$nj3PTg00aRj1OTg04BQj2wTg04C3j2v!s/$_j3uTg04D>j4oTg04E0j1n!s/$Nj3hTg008@j4fTg04F:j2eTg0023j6K!s8$ij2cTg04GGj2C!s/$dj2bTg04HFj2E!s/$bj2JTg04I<j2B!s/$ej3ITg04JNj2]Tg02^]j3gTg04K:j1\!s/$Xj4iTg04L6j7j!s/$Zj4kTg00QAj4lTg03a7j4mTg04MEj7Y!s/$ij7XTg04NMj8qTg04O1j6r!s/$Ul<sTg04P:l<tTf0R5#4#4p=U%4!s0$#4p=6g009AR6/E5p=5f1R7g04P_R8g04Q>R9P9g04Q^R:P5g04R>FYp=7g00`GR;P7g04R^P5C;p=@f2R<P8P9P9P:P7P5FXp=9f3R=!s;+<P7P5Gqp=<P7!s;+5Erp=?P;g02eTR>P;P;P3f4R3P0P=g04SE!s^%M<sp=`P>P;P1P0P4g04T2f5R4P3P=!sI'tp=ag008\R0#:R1#xR?#ZR@#8RAP>%M5,>@90A7g03DGRB#4RC#4RD#U#6!s$/RE,G5'2X7>13@5R>#N1p@5%5>%d@RF,1>'213@7R>#NRG#MRH!s}&1GGERIP;P>1>@590A<XA;g02g8RA%85RJ%87RKP2%8<?07513=<13=750;R2[13<713<550;%8=?0<7[RL%83?0=<\2A_<75P5n20010!s#$12!s-%0W?W>W7PL^?K^>J^7AP5P@P<13@<RA,>@RJP;1^@ARK13@==0;5XA;P;PKPA%A1RK%A?R?'[RL116KR2%5?1LK?RM,16[RN[RO%5KRPg00HIRQAWK?7UW8R?%5M\Q^8PRP!xu$TT1V6K'=P2eO1R2PNg04U:RQ#TRR%SQRS1H;7RT%R;RU%Q;RVP;1D;6RWg04Uf1F;0R0C;,7VRX1D;K=P;@RY,@0,7V59VRZ%O9R[PZC<1wV:RZP5P<g00F1R\g00FQR]'=1v5<=0\]dAu;67CoR]b4b5b6X0;%55R\115M'2%57R^117M'2[^0;P5f6R_,3@P4O2b3b1b;b1%5AR`%n@,LK,1A'2e11AF,2`e9h@ACf13@J1e@AEKO4bBPHPLPOP?PPP2PNp-0RHPRPSPTPUPV1?V=99VXP[PXC<PZP!tb,W212\7P^[^0;^2HP513@4R^/1MP^P3O3!t[',c>EKPI1C6>RI%:1#:!s$$AR^'1PGPIP5X@;1C65X@;P>P>1=;>D`PEP^1=;^Ea1b6>116>A0;I>'21E>6A0;I6'2'J1C6AP;!u6/1B;D1B;C1B;B5I;5I;g04VM']=gQRPSP;1H;<P7%\;CiPUPVPV!~$'1?V3P;P0g04W9R:1F;1R1!xA$59V1?V4P;P0P:PW!s:'FjP[!v@$_1@1Y!s:%P[1D;^!xf%C<!vP2X=;X2HX9HX:HA0;57,2<A0;56,2='J11<M,2411<^[!vr$=;^2H^9H^:HP5f7,3@R@#51E@6116@P@P3P4P_O7b3b<b1b<bFbCCkClbDCmWEo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkR_of : ltac2:(zQ "30!h9!k5!ma>1R@2$1@1$0#5@1$2@1$0#k0@2$1@1$0#5@1$2@1$0#k0") := ltac2:(zQ "80!h9!r4!qa!re!s3!k5!mjb!ma\1R@2$5@1$0#5@1$7@1$0#k0@hf$6@2$2^1@3$3@1$0#5+1Kv$1@2$4@1$0#5+1@2$2^1@3$3@1$0#5+2Kv$1@2$4@1$0#5+2@2$2^1@3$3@1$0#5+3Kv$1@2$4@1$0#5+3@2$2^1@3$3@1$0#5+4Kv$1@2$4@1$0#5+4@2$2^1@3$3@1$0#5+5Kv$1@2$4@1$0#5+5@2$2^1@3$3@1$0#5+6Kv$1@2$4@1$0#5+6@2$2^1@3$3@1$0#5+7Kv$1@2$4@1$0#5+7@2$2^1@3$3@1$0#5+8Kv$1@2$4@1$0#5+8@2$2^1@3$3@1$0#5+9Kv$1@2$4@1$0#5+9@2$2^1@3$3@1$0#5+aKv$1@2$4@1$0#5+a@2$2^1@3$3@1$0#5+bKv$1@2$4@1$0#5+b@2$2^1@3$3@1$0#5+cKv$1@2$4@1$0#5+c@2$2^1@3$3@1$0#5+dKv$1@2$4@1$0#5+d@2$2^1@3$3@1$0#5+eKv$1@2$4@1$0#5+e@2$2^1@3$3@1$0#5+fKv$1@2$4@1$0#5+f@2$2^1@3$3@1$0#5+h0Kv$1@2$4@1$0#5+h0@2$2^1@3$3@1$0#5+h1Kv$1@2$4@1$0#5+h1@2$2^1@3$3@1$0#5+h2Kv$1@2$4@1$0#5+h2@2$2^1@3$3@1$0#5+h3Kv$1@2$4@1$0#5+h3@2$2^1@3$3@1$0#5+h4Kv$1@2$4@1$0#5+h4@2$2^1@3$3@1$0#5+h5Kv$1@2$4@1$0#5+h5@2$2^1@3$3@1$0#5+h6Kv$1@2$4@1$0#5+h6@2$2^1@3$3@1$0#5+h7Kv$1@2$4@1$0#5+h7@2$2^1@3$3@1$0#5+h8Kv$1@2$4@1$0#5+h8@2$2^1@3$3@1$0#5+h9Kv$1@2$4@1$0#5+h9@2$2^1@3$3@1$0#5+haKv$1@2$4@1$0#5+ha@2$2^1@3$3@1$0#5+hbKv$1@2$4@1$0#5+hb@2$2^1@3$3@1$0#5+hcKv$1@2$4@1$0#5+hc@2$2^1@3$3@1$0#5+hdKv$1@2$4@1$0#5+hd@2$2^1@3$3@1$0#5+heKv$1@2$4@1$0#5+he@2$2^1@3$3@1$0#5+hfKv$1@2$4@1$0#5+hf").

Lemma mkR_of_eqv : ltac2:(zQ "50!h9!k5!mk2!hg7!ma>1R@2$1@1$0#5@1$4@1$0#k0@2$3^1@1$2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_RegsEquivM ()) [] "##r-p'0h02Hrh12Hnh21ni001nh31Hh44__p1h54__x1h62b1h72b2h81rh93Hn0h:1Rh;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@1xp%0p;1p;2p;3p;4p;6p;7p;5p;<p;8g002nj1?Tg003Sj1mTg0048j1K!s/$Vj1>Tg0000j2lTg006@j3e!s/$cj3;Tg03ChR0j10Tg048RR1j21Tg00GQR2j2TTg03BkR3j1BTg00[lj2GTg00K9j2ATg04;Bj3dTg00:;j25Tg00DBj2^Tg01V[j1MTg04:fR4j2L!t;$Kj2@Tg04W`j4YTg04XGj1XTg04HFj2JTg02SCj1WTg02Rcj1VTg04>Vj2UTg04?4j1S!s/$Rj1RTg04@=j2E!s/$`j2QTg04ACj4HTg00aRj1kTg04O1j6jTg04BQj2iTg04C3j2h!s/$_j3gTg04D>j4fTg0023j7c!tg$lj4bTg04Z1j1`Tg04[:j5_Tg04\>j1FTg0059j2aTg007=j1N!s/$Vj2D!tC$Ul<OTg04P:l<]Tg04MEj7\Tg04]Cj3CTg04NMj8[Tf2R5f1R6f0R73;#Np=4%B7,G6p=2f4R8f3R9/D5%F6/D73;p=3%B6,G5=;97#Np=6!s@%p=71D56=;97p=81@89/@5/@6/@7p=:g02eTR:P:g00`GR;P;P0P3P3f6g04]fR<f5R=P8P:P:P!sC+P9P<P5P6P7M<OM<Op=9!sE$1P3P4g04T2P=P8P9!sJ']p=ZP6g04P_R4g04Q>R3P3g04Q^R1P7g04R>F\p=IAC;89=C;5=C;6=C;7p=<P9P4!tC$1!su%G[p=P%07#0#0#0p==g008\R<#?R0#m#KR>%?0#?#?!s7$?#K#>R?'l%>>R@g009ARAg009_5e>RB94@7RCP:12>7RD9;@5REg03DGRF#0RG#0RH#0RI#0RJ#0RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf,17Rg'TX2:P?!up$5P6D3PEPgP?!vy$9P5D3P@12>6Rg119fP?f7RhP5PhP5D3[^0CX8@A4@gB115fP:A4@DB116fP?f9RD%B5Rg,G>RCPDPCD3]1]0P912>FRC=4@B11FfP?f8RFPCPFPCD3P6g02g8RF%>7RD%>6RhP2%>5?;671A951A965;;R2[1A561A575;;%>9?;56[Ri%>8?;95\2Ad567P7n20010!s#$12!s-%0W7W6W2Pi^7h^6D^2FP7P>PCPB1A>B,5;O4b3O1'^W1W0P@P>%07RCPBC6RF%06RD/1fRhP:P?f=Ri%05R2,2>R8PiP8D3^1h^0FP512>GRF!uZ%Gff<RG/7FRh,5?P?PGPFPhC8e!t0,C!t0&h%0D!t0%F!t0$ARG%02R8,2>RiPGPiD3^1F^0h!t0$HRh!t0%Hff@RH/7hRF!t0%HPhPF!t08F!t0+!u:%ERH%08Ri,2>RGPHPG!u:0I!u:'IffDRI!u:-I!u:LIRI%0iRG,2>RHPIPH!u:0J!u:'JffHRJ!u:-J!u:LMRJ%0GRH,2>RIPJPI!u:0K!u:'KffLRK!u:-K!u:LQRK%0HRI,2>RJPKPJ!u:0L!u:'LffPRL!u:-L!u:LURL%0IRJ,2>RKPLPK!u:0M!u:'MffTRM!u:-M!u:LYRM%0JRK,2>RLPMPL!u:0N!u:'NffXRN!u:-N!u:L]RN%0KRL,2>RMPNPM!u:0O!u:'Off\RO!u:-O!u:LaRO%0LRM,2>RNPOPN!u:0P!u:'Pff`RP!u:-P!u:LeRP%0MRN,2>ROPPPO!u:0Q!u:'QffdRQ!u:-Q!u:LiRQ%0NRO,2>RPPQPP!u:0R!u:'RffhRR!u:-R!u:LmRR%0ORP,2>RQPRPQ!u:0S!u:'SfflRS!u:-S!u:LqRS%0PRQ,2>RRPSPR!u:0T!u:'TffpRT!u:-T!u:LuRT%0QRR,2>RSPTPS!u:0U!u:'UfftRU!u:-U!u:LyRU%0RRS,2>RTPUPT!u:0V!u:'VffxRV!u:-V!u:L}RV%0SRT,2>RUPVPU!u:0W!u:'Wff|RW!u:-W!u:Kp+01BRW%0TRU,2>RVPWPV!u=0X!u='Xfp+01ARX!u@-X!u@Kp+01FRX%0URV,2>RWPXPW!uC0Y!uC'Y!t6$ERY!uF-Y!uFOJRY%0VRW,2>RXPYPX!uF0Z!uF'Z!t6$IRZ!uF-Z!uFONRZ%0WRX,2>RYPZPY!uF0[!uF'[!t6$MR[!uF-[!uFORR[%0XRY,2>RZP[PZ!uF0\!uF'\!t6$QR\!uF-\!uFOVR\%0YRZ,2>R[P\P[!uF0]!uF']!t6$UR]!uF-]!uFOZR]%0ZR[,2>R\P]P\!uF0^!uF'^!t6$YR^!uF-^!uFO^R^%0[R\,2>R]P^P]!uF0_!uF'_!t6$]R_!uF-_!uFObR_%0\R],2>R^P_P^!uF0`!uF'`!t6$aR`!uF-`!uFOfR`%0]R^,2>R_P`P_!uF0a!uF'a!t6$eRa!uF-a!uFOjRa%0^R_,2>R`PaP`!uF0b!uF'b!t6$iRb!uF-b!uFOnRb%0_R`,2>RaPbPa!uF0c!uF'c!t6$mRc!uF-c!uFN22Rc%0`Ra,2>RbPcPb!uF0d!uF'dfp+021Rd!uF-d!uFN26Rd%0aRb,2>RcPdPc!uF0e!uF'e!t6$5Re!uF-e!uF5PBC6%0D/1f%0b!t8$Pg%M<RBP!s$$D:P!s0h%M0R0'LS00PD1@7BX@;RDP!s$agO1S01O1S02O1S03O1RCO1R@O1RhO1RFO1ReO1RcO1RdO1RjO1RkO1RlO1RmO1RnO1RoO1RpO1RqO1RrO1RsO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1PDPbP~PDPaP}PDP`P|PDP_P{PDP^PzPDP]PyPDP\PxPDP[PwPDPZPvPDPYPuPDPXPtPDPWPsPDPVPrPDPUPqPDPTPpPDPSPoPDPRPnPDPQPmPDPPPlPDPOPkPDPNPjPDPMPdPDPLPcPDPKPePDPJPFPDPIPhPDPHP@PDPGPCPDPiQ03PDP8Q02PDP2Q01PDP5Pg15;gF9!s$APfP015;0EZP7CYQ00%X9%B9,JAp-0Rfg04U:Rg#W%Vg1U;6%S;%R;RgP;1E;Ag04Uf1Q;<R<CH,Ig%k3RDPgP;P<1E;BR<P!s$$D!s-&!s0cg04R^1E;0!t;$PDPg!#Y%'9EjCPCP1ig1P7P5g00F1Rgg00FQR1'51h75=;g1dAg;A6Cfb<b=b>X5;W41JA7P6P!{zr/L0P9[[^5;^4fP7!~<%:R?%==#!s$0,2>R>P?P>D3%B=P6P5O4b;b?b9W1W0X2:P7O1n0110001020111100P6P7O2!sH~!sH~!sH~!sH~!sH~!sH$0!sH~!sH~!sH^0!sH~!sH~!sH~!sHe!w<3P9P7P5FcX3ECbX2:%`6D_W0W8%F7,a7eW:o"). Qed.
(* [comment removed for export] *)
