(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PlacementSearch.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export LiaTuning.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_PropExec () := KReplay.lz_vm "#%JUC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK!sD+7Numbers7BinNums8positive02!sKG1!sK=1N02I45stdpp9bitvector;definitions2bv00!uKA3Sem5is_x0K!uG72eq!tQ?!tv,3I!se19Datatypes4bool00!u>>Z02C56Stdlib6ZArith6BinInt1Z3pow!sC<6moduloI!t%?0C!vA@;bv_unsigned!t6<8eqb_refl!y7I6bv_eqbI!vo;0I!xB?!wO3!vh31!tu<2le!sB>t!t^83and00!s]<7testbit!vc'7n!t~%1ZGbounded_iff_bits_nonneg!{~85proj1!uOB2!y9@1!t#=!yT=4land!wN9or!um>;!s^#!uG'!sK;>pow_pos!sNC:!sN#!sJB7compare!vA=list01I!sFA0K4!t/&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr01!sIE2!uc<6op!}S#!sH#!sk45Tauto8G!tZ'6C!sJ<B!sJ&!sH6:Z!uL+=Z!sT$CheckerC!vA<4find!sqAC!sq0_s!|0#!wX@!{;3!x>-andb!vbE7K!w{L1c89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib8PropExec>Z_!~f&_highC13~~~!{2<9!|K$spec!t@]AZ_!#3f&by!#3e#!tC%K!#4r;1!yBF4!sJF3!sJF5!sJF8!w`D3Op203!z}<5eKi!#4k3!y7-uni!~O9!se%4ki!v4%!sf@1!#5s74True!#:E-!sb2:!#4\$ison!#3=7!{y-;!y3%!xk$!t|8!v265!#>L<lor!#6f<lor!#6f%!}'@3!}'<3orb!#>C<!t,#!{<#!#9d=xor!#:E73iff!#9c=x!u/?!yo39!#3:<x!u6?9!t5$!u7@3div!#:A<div_pos!x2D5Psatz!#4I7!#4l&3Pol!#8q?!sG$3!t9K3!{L<3nat!#9=7!sn8!sOL6K!{[M2!#=jA!#;'F!#<<E!|C>mul!sC<B!xD#le_upper!#6r$!zg>e_lt_trans!sK<6shift!}\=?!sF%_!yd%w!w9L5!xRA1!wXN1!#J1@7bv_wrap!vo=add!siA?bv_half_!#Kg#u!vL=3su!#=|E3C3!#HM%tactics<f_equal_help!tYAC!uD&_add_idemp_l!#4R76!#Qr$!stA8bv_s!su#!#7pH!#Kr<8!t]#comm!#>b\D!tZ'!uQ0!#@&$!u;@=!s_+!s'#I!#E\B!#SH;?!s<2>!#Ol#!sE+=ov_read_bytes!u^]3rdn!#A47!ty51!tyZ;memory!t}$K!#VQC!|NB6bv!wX#!ug]7seg_rom!x:'!uk:7nat_!#AY#!ujI<MemImageType7Segment!#@t=!#3^#!#Xe8!#AW$!u~B5!#U]#!sJA:!sJ#xtract!#VZH4sext!vy]4v_lw!|2G9!|2#!#Xd$!#6'@Z_to_b!#>u<4of_N!#C:<!#8\%0_r!#4uD!vG&!#ZN+!sX@@!th&!sUJ>!ug&!t4#e!#5]BG!sS1!t1+!#`;?!}SL6BvBase=!#3>#_le!u>#Z!#<_Al!u#AD!u~-_in_range!zYE!#:]B=!tJ%!#[A8!|X,8list!#9S$!#4o:length!u[=of_nat!#eK8iff!#`+%!#:23;ZifyClasses;rew_!sR%v!#9l^!w\/!up'!#Rp74Znat5Nat2Z9is!#IX<!#@6:3!uGB5mkre!ulC7!ul&!#?LD4!#D#<!xU&!#J[#!t=A3inj!u,Eapp!sKB6!sK$2!sL68!sL#Inst7Inj_Z!|$5!w=-8inj_succ!#OY<!tY#!un;7lor_0_l!#4mAl!#4m#!sk<mu!sGA9!t4#assoc!|vD!~I&!t]Clo!#6LA@!#DC&!~i'!{v]6!#>'#i!#9JF!#Ea5!tvB?!#?1$!#4i'!tu]9b!so#sext!tx'!#o|Calu64!v7an!v7'!u/^u64!#7U%!spb<!wB#!sslZ_!#`u#!ss-!#HCD!xk$smal!#KH<sym!#E4En!#N>Ea!#=-/!x\?5Instr!x^#op0:!v2]5v_or!x_d;Z!}v#!vwM5b!tE#!#@kDor!v,W9!{g`x!v-f!z$#x!v/O!y8#xo!#3`Ex!v1Y6!#T|<lt!#_f,N!sC+Nat1N2l!#BOAE!#E'1!#F4&!#yiJlts!ws`slti!#@W=3N2Z6inj_le!vKN4!u6Ou!#PB]!u6%u!#S/&!toL5!~N`add!{Fc5v_sub!slglt!slc!xt%u!t[fan!v7d4!#5-#!tYex!sl'!#ShIz!#Sh_8u6!#4Y/!#C|;mod!#;R%!sI;4ones!#De=and_!sI$!#<g@!#Rf&!#<g%!#8vBzero!#RcK!sS-!#C'e!z=$l!#<0dshamt6_mask!#9#F!#X:#!#SKEB!sN+!#9,V3!v6ar!v6e>Z_!#Ye%!#<:K!v9+r!v9J!#<@W7!v9ba!#KEG:bv_a!uCGC!sO,!uDW8!#7lal!xVc=reg!{g#4!{h-!tbarl!#4|A=mod!$4z#!#sH$!#Td49SatDivModCZ_!sS#!#X\$!s,&!tlba!#8-F!#O:#low32!xlAA!#bH,!#5#b8u5!|z/!$AY9x01!vP+!vw&:Znumtheory<Z!vM#di!#_t#!y'^!#N>%32!sn#!#3Qc!vg$!#e1+!wFKalu32!tE]7!#Vk$w!u5c!#sA6!#?Qc>!#s]/'!suc?sext!w&4!#46M1!w-`sll!w-'!$$/E7!~x<?mul!~O$!#wG&!sO<!#<I%!sV#pow2!wOgcong!xFd!#?5$5!#6K,!$5K75False00!w<arl!{De7!#;Z$!snd<!~C%!z=/!ss]!#a^$w!smfsub!#tq'!#Q^2divBZminus!z2-r!sNJl!#VVDsub!#VVDsub!#>vV2!v4all!v{d!#>w%32!#>wg!#F4$!x`hra!smd5v_mul!t[fmulh!smc8!sm%su!~If!so#!#T`fdiv!slfre!$'='!#>KB!#p##div!wTc!~k'!#9xIr!~DE!y?#!~DD!s|#!~DPmulop!$5%=3eqb!$Wi?3!tcA8bv_quot!#V1<4!sE#!#F|D!sk$!#T}e7div0_32!}'fdiv!#?s'!w1L5!uaA7b!zm$!$<K=!{3#!si@@!si&!#XJhrem!u[U7!u[Ediv!#e0`!sg#!thU6!thEmod!tharem!thV8!$M{8n!|'CE!$Bu1_twic!#lDA>!$/m+!$LlN4!#@B7?!#SB$p!ss#fu!#`\B9bv_concat!#7y_lui!#6`A;lt_ge_cases!$,>D!#pN=opp!vlEs!#y=A9!#HW#_in!}D^;!t6+h!usC!$+S%r!#rW;!$IeDB!wo+!#6tfv_auipc!#=ccb!xh-!|j:!$DEA:fetch_word!shZ8is_ecall!$]^<prod!$tTB7DecodeC:d!s-$_any!#35Gi!s+#08K!tKA1I!uSY>machine_resul!$Dy#!snX=ac!s?#_report!#Q8^4mkst!xa`D!w$&exec_!tf%es!srZ6ms_mem!$MUZ!z;,_ov!skZ>!sk%tail!yK#!tYafailur!#|+;!yDR2!snj3!uKZBdrop_!z90!z7^get!#ZGc6regupd!z~`7m!uC#g!zq[8ms_f!sf^9ms_pc_val!|B^reg!ut`sv!se^fcsr!u2_om!{>Z=!{>'stat!%-w#!sm9!#Q7+4core!$Mm<!sO-exec!uKZCinterp_eff!#5fb<!|{&value!u+E6c!{0@!#T7,c!zrA!vP/_pc!tHJ!y\=!sO0!yF^?!vn&!$?+%!u6B!#>B&Bis_!#BZ#ed_illegal!#BK]fp!w'%!#4ibfp_!v##!#Y1Jreg_ge!$[:I9!%9##_se!#7G]6b_npc4!u^c=!%4I$0_!%8A#!#7P_5!#6%#!scZ4ste!#K1A4BvWf!#4:Z!#Bp01!#=Ai!#E?Z!#5q1!#E>;!#5q2!sOB!#i4/!sRI!#Gw$!$j0[!$h5%!v|%!zD]9alu!$>,-!sp]>!y^#_opimm_gen!{7Q!$`6&!$6_#le!$lV$!#Pv<mod_1!#o3,4Bool!s'$;orb_f!#RT#!$U}<=!%0Q&neg!sM>A!$'P$w2!%<C$l!%A5=;!$/J%!$~R?B!sv1!%1v#!u8@!#xp<9!sh$inj'!ww]<!$%=%8!$%<+!vP=!uV&!$,zb@!$a%'!xX&!#5N_@!#L@#!yH-".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemantics5Riscv7Preludek15bvmap37Corelib4Init9Datatypesmf4bool37Corelib4Init5Logicoe1Ik16bv_eqb3h5LinuxProcessSemantics5Riscv3Semqf7reg_gethf2BVhf4BvWfhf7Z_to_bvk19bvmap_setoe2eqqf5is_x001Z46Stdlib6ZArith6BinInt1Zhgd6modulohgd3powhf7bv_wraphgd2lemf5falseoe3andhgd2lthgd7testbithgd4landhgd3lorhgd4lxorhgd6shiftrhgd3addhf8bv_swrap01Nhf9bv_signedhfbbv_unsignedhgd3subhgd3mulk16bv_ltsk16bv_ltu89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec7WithFP1~~~~~~ht56v_addiht54zsighgd3ltbht55c_ltsht55c_ltuhgd6shiftlhgd3eqbhgd4quothgd3remhgd3divmf4listmf6option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeine7Segmentmf4Nonemf4Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiscbmemory_readmf3natiscdov_read_bytesht53rdn02N0k14sextht54v_lwhfabv_extract3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejl0dbytes_le_to_Zmf6lengthhgd6of_natmf3apphf6bv_add3h5LinuxProcessSemantics5Riscv5Instrjr27ALU_SLTqf5alu64ht56v_sltijr27ALU_ADDht55v_addjr27ALU_SUBht55v_subht55v_sltjr28ALU_SLTUht56v_sltujr27ALU_ANDht55v_andjr26ALU_ORht54v_orjr27ALU_XORht55v_xork14zexthf6bv_andjr27ALU_SLLht56v_sllijr27ALU_SRLht56v_srlijr27ALU_SRAht56v_sraiht55v_sllht55v_srlht55v_sraqf5low32qf5alu32ht57v_addiwht57v_slliwht57v_srliwht57v_sraiwht56v_addwht56v_subwht56v_sllwht56v_srlwht56v_srawjr25M_MULqf7mul_divht55v_muljr26M_MULHht56v_mulhjr28M_MULHSUht58v_mulhsujr27M_MULHUht57v_mulhujr25M_DIVht55v_divjr25M_REMht55v_remht56v_mulwht56v_divwht56v_remwjr26M_DIVUht57v_divuwjr26M_REMUht57v_remuwhfabv_modulusoe3nothffbv_half_modulusht55v_luihf9bv_concatht57v_auipcjr25instrmf4prodiscdmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mnc4mkstmf4pairisc9MachineOkiscafetch_wordisc8is_ecalliscemachine_resultisc4step3h5LinuxProcessSemantics5Riscv7DecodeCngbadecode_anyjr25OpImmjr25aluopmnc4getrmnc6regupdmnc6v_addimnc7v_sltiumf4trueisch3Build_machine_statemnc6fp_csrmnc7fp_regsjl0dZ_to_le_bytesisch0word_to_le_bytes" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.

Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition getr : ltac2:(zQ "30!h9!jc!m7>4regs@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5@1$1@1$0#k0") := ltac2:(zQ "a0!h9!jc!o7!q2!q6!m7!t1!tb!u0!u7\4regs@2$5@1$0#5@1$1@1$0#k0\1r@1$1@1$0#5M2\0$2@1$1@1$0#k0@3$4@1$0#5^1@3$7@1$0#5ZKv$3@2$8@1$0#5Z@2$9@1$0#k0Z@2$6^2^1").
Definition regupd : ltac2:(zQ "30!h9!jc!m7>4regs@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0@2$2@1$0#5@1$1@1$0#k0") := ltac2:(zQ "40!h9!jc!m7!v1\4regs@2$2@1$0#5@1$1@1$0#k0\1r@1$1@1$0#5\1v@1$1@1$0#k0@5$3@1$0#5@1$1@1$0#k0^2^1^3").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb0_is_x0 : ltac2:(zQ "90!h9!o7!q2!vd!q6!hg2!tb!u0!jc>1r@1$8@1$0#5@3$3$1@3$4@1$0#5^1@3$6@1$0#5ZKv$2@2$7@1$0#5Z@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01rp;1p;2p10000p4p7210p1000\p4p710p8g001:j15Tg001_j14Tg002Dj10Tg002bj11Tg003Ej13Tg003mj22Tg004G#5#4#0#1g004lf0#3'2W0o"). Qed.

Lemma bv_wrap32_mod : ltac2:(zQ "60!hga!vd!h9!hi5!hif!hj6>1z$0@3$1$0@2$5@1$2#i0^1@2$3^1@2$4+2+i0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zp;1p;2g001:j10Tg005Lj11Tg005jj23Tg006Gj22Tg003mj24Tg006gR0f0g004G#0R1#1%01#0#0#0#1'3'2,40W0o"). Qed.

Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01ah11np;1p;2p;3g002bj14Tg007Ej23Tg007oj10Tg008Qj31Tg009>j32Tg009Xf0R0#4f1R1/30#0g004lA1100g00:632eW0W1o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_testbit_high : ltac2:(zQ "90!hga!hk0!o7!hk6!hke!vd!hl4!hif!hla>1n$0>1a$0>1k$0>0@2$1Z^3>0@2$4@2$1Z^3@2$6^3@2$7+2^4>0@2$1^5^3@3$5$2@2$8^5^4$3").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01lh11Hh23Ha1h33Ha2h42Hkh52Hnh61ah71kh81np;2p;1p;4p;6p;3g00:Vj20Tg001:j1:Tg005Lj18Tg005jj21Tg00;2j22Tg00;NR0j29Tg00;ij24Tg00<Jj47Tg00=4j66Tg009>j35Tg004lf0R1g00=O35p=3g006gR2g00=oR3f2R4'0R5g004G#:#8R6f3R7'1,24,95P01037f4R0,16,27f5R5/071450#3[P11035f6R5f7R3,16'2f8R0/05f9R7,16,20f;R8/01f1R9,48#3[^02[f:R8/011489#3[^021168,27[P7P0P5P4C7P9P3P1E6W4W3W2P9P1O2n2001000000120000000W1W5X72X62W8o"). Qed.

Lemma Z_bounded_by_bits : ltac2:(zQ "80!hga!hk0!o7!hk6!vd!hl4!hif!hla>1n$0>1a$0>0@2$1Z^2>0@2$1Z^2>0>1k$0>0@2$1^5^1@3$4$2@2$7^5^2$3@2$5^4@2$6+2^5").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##&,h01lh12Hah22Hbh32Hnh41ah51kh61np;2p;1p;4p;3g00:Vj20Tg00;ij22Tg001:j15Tg005Lj19!s/$jj24!sJ$2j23Tg00<Jj48Tg00>Mj47Tg009>j36Tg004lf0R0g00=O36p=1g006gR1g00=of1R2'0R3f4R4/001242#1[^51f3R5g004G#5#9R6/44'3f6R7!sK$7!sK$01[f5!s821467,34[P4P5f2P2C8P0C7W2X13W3X41W6o"). Qed.

Lemma Z_land_range : ltac2:(zQ "60!hk0!hke!hga!hm5!hl4!hif>1a$2>1b$2>0@2$1@2$0Z^2@2$4^2@2$5+2+k0>0@2$0Z^2@2$1@2$0Z@2$3^4^3@2$4@2$3^4^3@2$5+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##74h06__sat1h14__x1h21bh37__arithh44__ffh5!sK%0h68__varmaph75__with82Hah91ah:4__p1h;4__p2h<1Hh=2Hbh>2Hkh?1kp;1p;2p;3p;7p;4p;6p;5p;8g001:j12Tg005Lj1@!s/$jj2GTg00;2j21!s/$NR0j2=Tg00>hj24Tg00?Fj26!s/$`j2OTg00@Ej2H!s/$mj3FTg00AQj2ETg003mj2;Tg00B2j1_!s/$Rj1\Tg00C2j2V!s/$Pj1U!s/$nj1TTg00DYj2:Tg00E<j2R!s/$_j1PTg00FAj7N!s/$ej2MTg00GGj2ITg009>j39Tg00H3j3J!s/$Rj4KTg00IDj1LTg00:Vj28!uP$ij25!sA$bj2ATg002Dj1QTg00J@j3D!s/$cj4BTg00KNj6STg000\j6CTg00L]j3^Tg00M@j5]Tg00NRj4[!s/$mj7WTg00OQj6XTg00P5j7Y!s/$Yj8ZTg00=oR1f0R2'8p=0g006gR3f1R4g00Q=P2CBp=<P!s4$dR5g00RCR6P6g00RcR7P2g00SCFWp=3P4P5P6P6P7P2EXp=?f2R8!s9+4P2FYp=>f3R9!s;+8P4P2GZp=7%04R:g004GR;#2R<#@R=%2<#2!s$%!s7$>'GR?,14'=R@1498RA#0RB11A?P01442#0%08/6:R0[%02RC,6:1484#0[RDPB\01O42P2n20010!s#$12!s-%0X23X93PD^23^93P2f4RDP91H=>R0111=RB%0>RE111?[RF[RG%0=RHg00ScRIAF=>4UW8RJ%0?\I^8HRH!vO$T?1E1=';PBeO1RBPFp-0RIg00TeRK#_RL%\KRK1V34RM%U3RN%T3RO1:31RP1R3;R;'<,3ORQ1?O95>O%P6RRPO!v\+Q1?ODFNC71MO7R7P2P8g004lR6g00:6R5';1I28=965dAJ314CKR1b4b6b7X13X:IW;1=C416:9[^13^:I^;IP2f7RI#0f8R9/1?P9f6O4b3b0b5b0O3b<R9P>PAP0PGPJPHPBPFPLPK%L3PN1:3>RA,<P,3OP7P!t:&PEP2!sg'REP918>2R9P6f5RP/54R515D4'Ag00=ORS9962X26P6PS15P8,A2=96SX261;6SP5P>PPP4PE!tN3PMPNPOP3P;g00UQ1:3=%Q<5D3CB,3O9>OQRQPRPQC7!tg,X13112?,=CP@[^13P2f9PIO!t{+!t291<A;,3OROPRPO!su38>4\9!sq$PPPD!sq,ESEC14PD/54A^PD4ECW>X?3D]C[X=:W8!z?%o"). Qed.

Lemma Z_lor_range : ltac2:(zQ "61!hke!hk0!hl4!hif!hga!hmd&@2$0@2$1Z^2@2$2^2@2$3+2+k0>1a$4>1b$4>0~0>0~0@2$0@2$1Z@2$5^4^3@2$2@2$5^4^3@2$3+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##8Qh06__sat1h14__x1h21bh37__arithh4!sD%0h54__ffh68__varmaph75__with82Hah91ah:4__p1h;4__p2h<4__x2h=1Hh>2Hbh?2Hkh@1kp;1p;2p;3p;4p;6p;5p;7p;8g001:j13Tg005Lj1B!s/$jj2JTg00;2j21!s/$NR0j22Tg00V8j29!s/$Uj2RTg00@Ej2Q!s/$mj3NTg00AQj2ITg003mj2>Tg00B2j1G!s/$Rj1_Tg00C2j2FTg00IDj1WTg00W9j4V!sA$Pj1U!s/$nj1TTg00DYj2<Tg00E<j2C!s/$_j1PTg00Fej2OTg00GGj2MTg009>j3@Tg00H3j3L!s/$Rj4KTg00:Vj2=!uG$ij26!tC$Wj2:Tg002Dj1HTg00J@j3S!s/$cj4DTg00KNj6ETg000\j6?Tg00X4j3^Tg00M@j5]Tg00NRj4\!s/$mj7[Tg00OQj6XTg00P5j7Y!s/$Yj8ZTg00=oR1f0R2'=p=0g006gR3f1R4g00Q=P2CDp=7P!s4$dR5g00RCR6P6g00RcR7P2g00SCF[p=4P4P5P6P6P7P2EXp=Af2R8!s9+4P2FYp=5f3R9!s;+8P4P2GZp=8g004l!t-$=OR:7@2p=;%04R;g004GR<#3R=#BR>%3=#3!s$%R?#BR@'JRA,14'2RB1998RC#0RD11CAP01942#0%08R0/2;RE[%02RF,2;1984#0[RGPD\E1R42P2n20010!s#$12!s-%0X23X93PG^23^93P2f4RGP91Q>@RE111>RD%0@RH111A[RI[RJ%0>RKg00ScRLAN>@4UW8RM%0A\L^8KRK!ve$T?1I1>'>PDeO1RDPIp-0RLg00TeRN#GRO%_NRNP31F38P4%W3RPCV%U3RQ%T3RR1<31RS1C3='7,4RR=1ARG55R%P6R6PR1C3<R<,7S,4RRTf5RU,AR55RP6A5RT=C8C81OR7R7P2P8g00:6R=,>51M28=@5=dAL314CKR1b5b6b7X13X<3X:LW;12;812;G%09,20[[^13^<3^:L^;LP2f8RL/1Af7R0/1AP0PLPUf6R9O6b3b0b4b0O3b=R;P@PCPEPJPMPKPDPIPOPNPPPQ1<3@RP!u-%P7P!tM&PHP2!sf'RHP;1=@2R;P516U4RS16G4RC':%;2X25P5P:16U8,:2#;!s6':!s3&1>5:PCP@PGP4PH!tO31F34RCPQPRP3P<g00UQ1<3>%H?5S3CD,4R95RTRTP6PTC8!tm,X13RT112A,2FPB[^13RFP2PLP9O!u,+!uc4!t6$17P<,4RRRP6PR!sy21=@4\;^13P2PUPG!sq,R;EEE?PSP@PU!u=4TPFP2f9P0!tI-!sV$19UG/64A^UG4E?W?X@3D]C\X>BW8!{H%o"). Qed.

Lemma Z_lxor_range : ltac2:(zQ "61!hke!hk0!hl4!hif!hga!hn4&@2$0@2$1Z^2@2$2^2@2$3+2+k0>1a$4>1b$4>0~0>0~0@2$0@2$1Z@2$5^4^3@2$2@2$5^4^3@2$3+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##8nh06__sat1h14__x1h21bh37__arithh4!sD%0h54__ffh68__varmaph75__with82Hah91ah:4__p1h;4__p2h<4__x2h=1Hh>2Hbh?2Hkh@1kp;1p;2p;3p;4p;7p;6p;5p;8g001:j12Tg005Lj1B!s/$jj2KTg00;2j21!s/$NR0j28Tg00XVj27Tg00Y4j2;!s/$Mj2STg00@Ej2P!s/$mj3JTg00AQj2ITg003mj2>Tg00B2j1a!s/$Rj1`Tg00C2j2ETg00IDj1YTg00W9j4W!sA$Pj1V!s/$nj1UTg00DYj2<Tg00E<j2D!s/$_j1RTg00Z2j7QTg00Fej2OTg00GGj2NTg009>j3ATg00H3j3L!s/$Rj4MTg00:Vj2?!uY$ij26!sn$Vj2:Tg002Dj1HTg00J@j3T!s/$cj4GTg00KNj6FTg000\j6=Tg00[4j3_Tg00M@j5^Tg00NRj4]!s/$mj7ZTg00OQj6[Tg00P5j7\!s/$Yj8XTg00=oR1f0R2'?p=0g006gR3f1R4g00Q=P2CGp=5P!s4$dR5g00RCR6P6g00RcR7P2g00SCFZp=3P4P5P6P6P7P2E[p=Cf2R8!s9+4P2F\p=9f3R9!s;+8P4P2GXp=4g004lR:g00=OR;7A2p=@%04R<g004GR=#2R>#BR?%2>#2!s$%R@#BRA'KRB,14'8RC1798RD#0RE11DBP01742#0%08R0/;<RF[%02RG,;<1784#0[RHPE\F1S42P2n20010!s#$12!s-%0X23X93PH^23^93P2f4RHP91P?ARF111?RE%0ARI111B[RJ[RK%0?RLg00ScRMAJ?A4UW8RN%0B\M^8LRL!ve$T?1I1?'>PEeO1REPJp-0RMg00TeRO#aRP%`OROP31E38P4%Y3RQCW%V3RR%U3RS1<31RT1D3>'5,3SR>1CSH59S%R6RUPS1D3=R=,5T,3SRVf5RW,CS59SPUPS!w=+VP>FQC4C41OS7R7P2P8g00:6R>,>:1N28=A:>dAL314CMR1b5b6b7X13X<3X:MW;18<818<H%09,;0[[^13^<3^:M^;MP2f8RM/1Bf7R0/1BP0PMPWf6R9O6b3b0b4b0O3b=R<PAPDPFPKPNPLPEPJPPPOPQPR1<3ARQ!u9%P7P!tM&PIP2!sf'RIP<1?A2R<P:16W4RT16H4RD':%@2X2:P:P;16W8,:2#@!s6':;!s3%1>:;PDPAPHP4PI!tO31E34RDPRPSP3P=g00UQ1<3?%H@5T3CG,3S99SVRVPUPVC4!tm,X13RV112B,8GPC[^13RGP2PMP9O!u,+!uc4!t6$15Q=,3SR!wi$!sy21?A4\<^13P2PWPH!sq,R<EFE=PTPAPW!u=4VPGP2f9P0!tI-!sV$17WH/64A_WH4E=W?X@3D^C]X>CW8!{S%o"). Qed.

Lemma Z_shiftr_range : ltac2:(zQ "60!hk0!hke!hga!hl4!hif!hnc>1a$2>1k$2>0@2$1@2$0Z^2@2$3^2@2$4+2+k0>0@2$0Z^2@2$1@2$0Z@2$5^4^3@2$3@2$5^4^3@2$4+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##>fh06__sat1h14__x1h2!s6%3h37__arithh44__ffh54__p1h6!sG%0h78__varmaph85__with92Hah:!sG%2h;4__x2h<4__x3h=1Hh>2Hkh?1ah@1khA1zp;1p;2p;3p;4p;5p;6p;7p;8g001:j10Tg005Lj1<!s/$jj27Tg00;2j29!s/$Nj2:Tg00[Wj2ITg00@Ej2Ej4S!s2$mj3CTg00AQj2NTg003mj2HTg00B2j1r!s/$Rj1pTg00IDj1jTg00CPj1c!s/$nj1]Tg00DYj2KTg00Fej2XTg00GGj2WTg009>j3VTg00H3j3U!s/$Rj4T!se$2j2ATg00E<j2B!s/$_j1QTg00\4j4O!s/$Uj2FTg00]>j2G!s/$_j4MTg00^@j2q!s/$ij1?Tg00_Hj2=Tg00`1j38!s/$Zj2oTg00aFj3iTg00W9j4hTg001_j1f!sA$fj5bTg002Dj1aTg00J@j3^Tg00bJj3_!s/$mj2`Tg00:Vj2JTg00cJj5\Tg00d6j5dTg00NRj4e!s8$[j2[Tg00e;j3ZTg000\j6g!t$$cj4L!sS$mj7YTg00OQj6kTg00P5j7l!s/$Yj8m!se$dj3nTg00=oR0f0R1'Jp=1%01#0#0#0p=R1901p=4g006gR2f1R3g00UQP1CLp=>P3g00QdR4g00RCR5P5g00RcR6P1g00SCFYp=5P2!sM%=!s[%;P3P4P5P5P6P1Ekp=Df2R7!s9+3P1Flp=@f3R8!s;+7P3P1Gmp=2!tj$p=P!tr+!s$'p=6An231p=3%13R9g004GR:#0R;#<R<%0;#RR=#<R>'7R?,93R@':P217<7RA,I8%11RB191?RC':XA2P<P71E<>RD%4<RE%1>%4?[RF[RG%1<RHg00ScRIAC<>3UW9R>%1?\IRJ^9HRK!ug$T?1N0<'HPEeRLO1RMPFg00TeRN#rRO%pNRP%j2%c2RQ%]2RR1K20RS1K2<RT'>'51XR6RUP1P7g004lRVg00:6RW'H1W17=VVWdAU203CTRWb4b7b8PEP1b3b0b6b0P1CS%4Af4RA17<8RV'IRX#119X?PAPVPDPGP>PKf5RY,E<RZf6R[#1f7R\,7<#4[\EREf8R]=C<3VIX9HR^17<]R_#1\I^9HRIPM%1\%4_[R_PAPLO1RLPFp-0R`POPP1A23RaPQPR1B2:Rb,;S,5RRc1DR8Rd5@R%Q5RePcC2PUP!u6&X12W51:B3P9[^12^5`P1f;Rf/9?RgPff9RhO3b3b2!uY%b:b2!u>'PZPEP^PIPMP_PLPFPOPPP!tM%>Sb,5RRiPePi!t<2%41%43[^12P1f:Ri,7<RjP\O2!t31RkCOPXPAP!vY%APk!tE;%P=#6!s$0<,F2RkP2%<:,G2P:1G20CM,q2g00fMR0#?RV#?#?R?,=2RX'3'3%?!s2$?1=2VRV,3X=82VRV'31F2<1=20R0,3?'3130V,3k1300,3k582!s%+g00fl'o=iNOPPP21A27P31A28ChPQPRPR%f:,B2!wZ&:Pe1B2;R;,>!s6$NC2PePRPR1;ST,5R!s3%!}C'DbPe%a=9^2TRT!sh%C2!sX&N!s+$:PePR1DRY9@RcPeA_2;b,;b!sO&!s$%!wM0X;2X<2X5`%17%47[PJ\H%48%1Y%1A/:\1`[Y,JY[[[[!y-$;2^<!y4%PgPiPjPfP7PYP\P]PhO9!x&1D\!y9GbT,5RRT9@RdPePT!tn35`1:3CP@!zT+%1fPfP!zL4DdCeb=1[87!tC+M!t7/PcP!{Y5P9\B!z@$P[PA!z9$!sv$9Z87EgX>9W9X@2X?2o"). Qed.

(* [comment removed for export] *)
Lemma bv_swrap_add_idemp_l : ltac2:(zQ "60!hga!ho6!hod!vd!hp8!hj6>1n$4>1x$0>1y$0@3$3$0@2$2^3@2$1@2$5^3^2^1@2$2^3@2$1^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__x1h24__x2h34__x3h41zh51Hh64__ffh78__varmaph85__with91nh:1xh;1yp;2p;1p;4p;3p;7p;8p;6g00gXj21j1@Tg00h>j20Tg00h[j15Tg00iIR0j18Tg003mj24Tg00B2j1ITg00BRj1CTg00C2j29Tg00W9j4>Tg00CPj1=Tg00Cnj1<Tg00E<j27Tg001:j1;Tg001_j1KTg00ifj33Tg00Jcj4JTg00Nmj7HTg00Fej2GTg00GGj2DTg009>j32Tg00H3j3BTg00HRj4ATg00jIj86Tg00jfj3?Tg000\j6ETg00kXj6FTg00l4j2:Tg009Xg006gR1P1P1f2R2f1R3,12R4f0R5'0R6%52R7'0R8'1R9#81035R:/07,12R;#8P7P7P1P1\1R<P0P0P9P;P<\1/40g00TeR0#I%C0P11912P3f3R0,91C>%=1%<1R;g00Qdg00RCR9P9g00RcR9P1g004GR=,71R>%;=,71R?%K=,71R=531531g00l[A31>?=31=CJg00SCFH1G;9P5P2g004lR9g00:6R;'41D52=29;dg00=o=B13CAb6b7b8X11X21X31R;1032,051053/02521^11^21^31R9P5%50R=P31102R?O3b01057,04=218P1103=R8,0?R4f4R>/151002%5>R@'0,1>R>521X41P11028RA,10A215>X41P1P1%@0R>P>PA1023/0=14<>P;P9P5P@P2P0O3b0G61104A?028EE10?3/0=P5EFb5G61417G61:261:2:521eX;1W:W9o"). Qed.

Lemma bv_swrap_add_idemp_r : ltac2:(zQ "60!hga!ho6!hod!vd!hp8!hj6>1n$4>1x$0>1y$0@3$3$0@2$2^3@2$1^2@2$5^3^1@2$2^3@2$1^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11nh21xh31yp;2p;3p;6g00gXj27Tg00h>j21Tg00l4j20Tg009>j33Tg003mj26Tg00mBj24Tg000\j62Tg00mdj35Tg009Xg006gR0P0f2R1f0R2'7R3f1R4'1R5f3R6/021114,06R6530X00R7P01124R8,01A3026X00P01142R6P71016,60P81424E21015A5124E211431443E2X30W2W1o"). Qed.

Lemma bv_swrap_wrap' : ltac2:(zQ "50!hga!hod!vd!hp8!hj6>1n$3>1z$0@3$2$0@2$1^2@2$4^2^1@2$1^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zp;2g00o9j20Tg009Xg006gf1f0'0W1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zsig : ltac2:(zQ "30!h9!hga!jc>1x@1$2@1$0#k0$1") := ltac2:(zQ "30!h9!jc!hpb\1x@1$1@1$0#k0@2$2@1$0#k0^1").

Definition v_addi : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!ho6!u7!jc!hq7\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_add : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!ho6!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_sub : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hr5!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_mul : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hrc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_andi : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!hm5!u7!jc!hq7!hj6\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_ori : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!hmd!u7!jc!hq7!hj6\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_xori : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!hn4!u7!jc!hq7!hj6\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_and : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hm5!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_or : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hmd!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_xor : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!hq7!hn4!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

Definition c_lts : ltac2:(zQ "30!h9!jc!o7>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!h9!jc!hs3\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").
Definition c_ltu : ltac2:(zQ "30!h9!jc!o7>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!h9!jc!hsc\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").

Definition btgt : ltac2:(zQ "30!h9!jc!hga>2pc@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "40!h9!hga!ihc!jc\2pc@1$3@1$0#k0\3imm$1@2$2^2^1").

(* [comment removed for export] *)
Definition v_slti : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!o7!u7!jc!hga!ii6!iie\1x@1$3@1$0#k0\3imm$4M1\0$1@1$3@1$0#k0@2$6@1$5^2^1@2$2@1$0#k0+1@2$2@1$0#k0Z").
Definition v_sltiu : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "80!h9!o7!u7!jc!hga!iie!hq7!hj6\1x@1$3@1$0#k0\3imm$4M1\0$1@1$3@1$0#k0@2$5@2$6@1$0#k0^2@2$7@1$0#k0^1@2$2@1$0#k0+1@2$2@1$0#k0Z").
Definition v_slt : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!o7!u7!ij5\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4^2^1@2$3@1$0#k0+1@2$3@1$0#k0Z").
Definition v_sltu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jc!o7!u7!ije\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4^2^1@2$3@1$0#k0+1@2$3@1$0#k0Z").

(* [comment removed for export] *)
Definition v_slli : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!ik7!u7!jc!hq7\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_srli : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!hnc!u7!jc!hq7\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_srai : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!hnc!u7!jc!hpb\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").

(* [comment removed for export] *)
Definition v_sll : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hi5!ik7!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+k0").
Definition v_srl : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hi5!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+k0").
Definition v_sra : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hi5!hnc!u7!hpb!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$5@1$0#k0^2@2$2@2$6@1$0#k0^1+k0").

(* [comment removed for export] *)
Definition v_lui : ltac2:(zQ "30!h9!hga!jc>3imm$1@1$2@1$0#k0") := ltac2:(zQ "30!h9!hga!u7\3imm$1@2$2@1$0#k0^1").
Definition v_auipc : ltac2:(zQ "30!h9!jc!hga>2pc@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!hga!ho6!u7!jc!hq7\2pc@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2^1@2$5@1$0#k0^2").

(* [comment removed for export] *)
Definition v_addiw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!ho6!u7!jc!hod!hq7\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$6@1$0#k0^2^1").
Definition v_slliw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hga!ik7!u7!jc!hod!hq7\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$6@1$0#k0^2^1").
Definition v_srliw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "80!h9!hga!hnc!u7!jc!hod!hq7!hj6\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$7@1$0#i0@2$6@1$0#k0^2^1").
Definition v_sraiw : ltac2:(zQ "30!h9!jc!hga>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "70!h9!hod!hga!hnc!u7!jc!hq7\1x@1$5@1$0#k0\2sh$2@2$4@1$0#k0@2$1@1$0#i0@2$3@2$1@1$0#i0@2$6@1$0#k0^2^1").
Definition v_addw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!ho6!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_subw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hr5!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_sllw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hq7!hi5!ik7!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$6@1$0#i0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+i0").
Definition v_srlw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!jc!hq7!hi5!hnc!u7!hod!hj6\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$6@1$0#i0@2$4@2$7@1$0#i0@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+i0").
Definition v_sraw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hod!hq7!hi5!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$6@1$0#k0@2$2@1$0#i0@2$5@2$2@1$0#i0@2$3@1$0#k0^2@2$4@2$3@1$0#k0^1+i0").

(* [comment removed for export] *)
Definition v_mulh : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hpb!hrc!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1+k0").
Definition v_mulhsu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!h9!jc!hrc!hnc!u7!hpb!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1+k0").
Definition v_mulhu : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hrc!hnc!u7\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1+k0").
Definition v_mulw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!hq7!hrc!u7!hod\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

(* [comment removed for export] *)
Definition v_div : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!jc!o7!ii6!u7!il1!il8!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$5@2$7@1$0#k0^1Z@2$4@1$0#k0-1@2$4@1$0#k0@2$6@1$3^2@1$3^1").
Definition v_rem : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!jc!o7!ii6!il1!im0!u7!hq7\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4@2$7@1$0#k0^1Z^2@2$6@1$0#k0@2$5@1$3^2@1$3^1").
Definition v_divw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "90!h9!jc!hod!hq7!o7!u7!il1!il8!hj6\1x@1$1@1$0#k0\1y@1$1@1$0#k0M4\0$4@1$1@1$0#k0@2$6@2$8@1$0#i0@2$3@1$0#k0^1Z@2$5@1$0#k0-1@2$5@1$0#k0@2$2@1$0#i0@2$7@2$2@1$0#i0@2$3@1$0#k0^2@2$2@1$0#i0@2$3@1$0#k0^1").
Definition v_remw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!h9!hod!hq7!jc!o7!u7!il1!im0!hj6&@2$1@1$0#i0@2$2@1$0#k0^2\1x@1$3@1$0#k0\1y@1$3@1$0#k0M4\0$4@1$3@1$0#k0@2$6@2$8@1$0#i0@2$2@1$0#k0^1Z@2$5@1$0#k0~0@2$5@1$0#k0@2$1@1$0#i0@2$7~0@2$1@1$0#i0@2$2@1$0#k0^1").
Definition v_divuw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!h9!jc!hq7!hj6!o7!u7!im7!il1!hod&@2$3@1$0#i0@2$2@1$0#k0^1\1x@1$1@1$0#k0\1y@1$1@1$0#k0M4\0$4@1$1@1$0#k0@2$7~0Z@2$5@1$0#k0-1@2$5@1$0#k0@2$8@1$0#i0@2$6@2$3@1$0#i0@2$2@1$0#k0^2~0").
Definition v_remuw : ltac2:(zQ "20!h9!jc>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!h9!hq7!jc!hj6!o7!u7!hod!il1!hi5&@2$3@1$0#i0@2$1@1$0#k0^1\1x@1$2@1$0#k0\1y@1$2@1$0#k0M4\0$4@1$2@1$0#k0@2$7~0Z@2$5@1$0#k0@2$6@1$0#i0@2$1@1$0#k0^2@2$5@1$0#k0@2$6@1$0#i0@2$8@2$3@1$0#i0@2$1@1$0#k0^2~0").

(* [comment removed for export] *)
Definition v_lw : ltac2:(zQ "20!h9!jc>1v@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!u7!jc!hod!hq7\1v@1$2@1$0#k0@2$1@1$0#k0@2$3@1$0#i0@2$4@1$0#k0^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_rom : ltac2:(zQ "50!h9!jc!ime!in5!ir3>4segs@1$2$4>0@1$1@1$0#k0@1$3@1$1@1$0#8") := ltac2:(zQ "80!h9!jc!ime!in5!ire!is5!ir3!jg3\4segs@1$2$6\4addr@1$1@1$0#k0M3\1x@1$3@1$2@1$1@1$0#8@1$3@1$1@1$0#8@3$7^2^1@1$0#1\1l@1$2@1$1@1$0#8M2\1l@1$2@1$1@1$0#8@1$3@1$1@1$0#8^1@1$4@1$1@1$0#8\1b@1$1@1$0#8\2l0@1$2@1$1@1$0#8@2$5@1$1@1$0#8^2@1$4@1$1@1$0#8").

Fixpoint rdn (segs : list Segment) (mem : word -> option byte) (a : word) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match mem a with Some b => Some b | None => seg_rom segs a end) with
    | Some b => match rdn segs mem (a+1) n' with Some rest => Some (b :: rest) | None => None end
    | None => None
    end
  end.

(* [comment removed for export] *)
Lemma ov_rdn : ltac2:(zQ "90!h9!jc!ime!in5!jh2!vd!ir3!jh8!ji9>4segs@1$2$6>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$4>1a@1$1@1$0#k0@3$5@1$3@1$2@1$1@1$0#8@4$7^4^3^1^2@4$8^4^3^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##9}p'0h01oi001oh11ah21bi011bh31nh42IHh51li021lh63memh72n'h84resti03!s-$h94segsi042l0i051xp;1p;4p;3p;2p;6g00BRR0j1<Tg001:j14Tg002Dj18!s/$bj1:Tg00oeR1j1>Tg010Gj42Tg011Lj40Tg009>j31Tg003mj26Tg012Pj25Tg0132j37Tg00E_j1;Tg005Lj1?Tg0145j3C!s/$Xj33Tg00aFj39Tg000\j6=Tg015=j2BTg00^ij1ATg016Ej4@!s/$f#<g004GR2#4#4#4R3!s-%#8R4#:R5%83#:R3#>R6[g017eR7%<3R8#>R9f4R:f3R;f0R<f1R=C2P:P;P<P=C031^15R>X37P;f2R?P<g00fMC0,69X15P:P<O1R@P6P1P3!s&$9!s+$6P<153<RAP1P8P6f7RB%82RC77?P0!sF%%;3RD153=n10110200020020!s4$4REPD!s?%5000210!sH$!s82100RF!t0$9f8RGPB%?2g018D5C4R2934;RHf5RIC2RJA93=<,58RK%;8RL!sp2300PL!t+5!uH&!t2&PGPBPHPIC0RBPKP!sj6RF!sl7519P<P9PB!sm&<A93?!tZ$B!sk7!uG&9RMPGA34:2RNf6ROC0RPP!sW8519X09169FPJP:PHO1E=X23P<O1A7O=C!wZ$8!wd+8P6P<P!v~8RH!tq&MPGPNPOC2!u^9!vJ>!sh'P!s`M!v>%0!yW+E!ux&;R0f:RPA34O2RHPG!t\V!sq&P0PPPHPGC0!tdR169LRHP9f=RNf<RJA34G2RGPPC!z8+!x=$;!x=$Q!x=>>PNA34M2P0C0PQ!x5=!s{&F!xY9,69PNPJPGPPC2PMPG!xZ$88X23P=P<O2!|['!x=$21!s4%X58P<O1PH!sD%001021!}&%b0!s:2101b0!~$0@P!}|&A7I<CP!}OJ!u>&OPIA34=2R2P;!x-V!tP+1BI<!t3?P2P;!xLRePIP:P<%A?R?C2!s3%P?C!sA$X15X4>X77P<C@W3W6W9o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma b_lw_val : ltac2:(zQ "70!h9!jc!vd!jj0!jj4!jjb!jk3>1v@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@4$6@1$0#k0$3@1$0#i0^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51vp;1p;3p;2p;4p;6p;8g001:j13Tg002Dj1;Tg002bj12Tg009>j35Tg007Ej20Tg018`j3CTg019Dj49Tg019mj3>Tg01:Xj1=Tg01;]j28Tg00gXj24j1ITg00l4j27Tg01<Ej2<Tg003mj2HTg01<kj1GTg00d[j2:Tg00o9j2FTg01=Ij1BTg000\j66Tg01=mj4ATg00jIj8@Tg01>_j2?Tg01?Nj3DTg01@;j3ETg006gR0f1R1f0R235p=1g004G#3#3#3#3#3R3#3#;R4#2g009XR5%22R6%21R7g00;Nf2R8#2?512f3R9/081091'1R:[10811082'1%29?581[R;f4#2?598\:AC812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%;3R3P4g01A1R5P3P1C9R67>4R7%=1R;P01836R:,441048,73R9,<4,04,12X00P01041R<,73R=,44P4P5P3P8C9,83,44/12X00P0P0%I4R8P8P:P=P0\0/H8P0%G5,:<,431732/19X00P0P<1432,73/19X001F3<g00=o,:<%B<E61036P4P5P3P1CAE611:=eG@1<4=,041?4=E6AD346,04AE346E61047104;'1eO4b4W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_nonneg : ltac2:(zQ "50!ime!h9!jnf!hk0!jc>2bs@1$0@1$4@1$1#8@2$3Z@1$2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##2jh01ah11Hh21bh32bsh47__arithh54__ffh64__p1h78__varmaph85__with94__x1h:1nh;2IHp;1p;2p;4p;3p;6p;7p;8p;5g001:j15Tg002Dj1W!s/$bj1ETg00BRj1:Tg01AOj11!s8$2j19Tg00IDj1DTg00CPj1B!s/$nj1ATg00DYj2@Tg00Jcj4;Tg00Fej2VTg003mj2UTg00GGj2TTg009>j3OTg00H3j3N!s/$Rj4KTg00:Vj28Tg00V8j24Tg00;NR0j22!s:$Uj2CTg007Ej26Tg005Lj1FTg01BLj23!s/$lj2GTg01C_j1H!sg$2j27!t{$2j2ITg00E<j2JTg00OQj6?Tg00P5j7L!sA$_j1M!s8$Yj8>Tg01DHj2PTg00NRj4QTg00aFj3=!sA$oj5R!sA$mj7STg00=oR1f0R2'8p=0f1R3g00QdR4g00RCR5P5g00RcR6P2g00SCFSp=<g004GR7#5#5#5R8#WR9#ER:#:R;P:%12#0R<X3;g00TeR=#9R>%:=R=g006gR?#D%B?R@%A?RAP?1@?1RBg00Q=RCPBC;'<1VA6RDP2f2REg004lRFg00:6RG'U1T2E=OFGdAN?13CKRGb5b7b81811P2b4%9:#1#0eP01432#0%0ER1%03RF'2RH[%02RI,2F14E3#0[RJf3RK/4E#0\H1C32P2n20010!s#$12!s-%0X2?X0?PJ^2?^0?P2169KRJ%1E%F8R8'3RH%0JRL%0H1G9K%H9RH,7J,2Lp-0RLP>P=1I?3P@PAP4P5P5P6!s0-?PBPC1J?7C;,<AR7!sA-KE?FL%M5P7G>PDP!ua&X9?W612I3PF[^9?^6LP2f5,69R9/7HP9P3O3b4b1P01332#0P1[13E3#0\FRF13KE#0\11P!uc<:!uc$F^:!uc%%1KP8PEO3b1CQO3b1A=:E3!w'$X;<X3;X2:P2DRW3o"). Qed.

Lemma bytes_le_to_Z_bound : ltac2:(zQ "90!h9!jc!jp0!ime!jnf!hl4!hrc!jp9!hif>2bs@1$3@1$1@1$0#8@2$5@1$4^1@2$8+2@2$6+8@1$7@2$2@1$1@1$0#8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##Tfh06__sat1h14__x1h22Hah37__arithh44__ffh5!sL%0h68__varmaph75__with84cstrh94__x2h:3Hk0h;1bh<1xh=1ah>1nh?2bsh@2H0hA4__p1hB!sw%3hC1mhD1yhE1HhF2HbhG2HkhH2IHhI!sJ%2hJ1kp&0p;1p;2p;3p;4p;6p;<p;5p;Bp;7p;8g001:j1<Tg002Dk10@!s0$bk100Tg00BRj1\Tg01AOj17Tg005Lj1KTg01EQj24!s8$jR0j22Tg00;2R1j26Tg01F1R2j18Tg00bmR3j21!s<$Qj1kTg003mj2HTg00@Ej2?!s/$mj3ATg00AQj2y!tK$2j1^Tg00IDj1wTg00CPj1v!s/$nj1uTg00DYj2ETg00J@j3]Tg00Fej2pTg00GGj2oTg009>j3[Tg00H3j3n!s/$Rj4m!t^$oj4ZTg01GZj1lTg01Blk20!t_$7Ej2BTg01C_k10>!uV$NR4j2!vB$^iR5j1G!sY$Lj2!sE$V8j2FTg00h>j2CTg00:VR6j2:Tg01Hoj1LTg00_Hj2WTg00`1j3V!s/$Zj2fTg01ITk20:Tg00aFj3U!u`$2j2cTg00E<j2Y!s/$_k10!wR$ifj3b!w$$Jj3P!tP$Uj2~Tg00OQj6}Tg01DHj2|Tg00NRj4{!u;$ij2DTg00WWj2Q!sn$Ij2_Tg01J@l<T!s/$ej4x!sJ$9j4STg01KLj3zTg00KNj6`Tg000\j6NTg00\Uk201Tg00edk30!xx$1_k103!s_$oj4tTg00X4k30!yH$M@k505!tl$oj5sTg01LTk40!yO$M7l<O!s/$\lBX!xI$cj4e!u9$mj7dTg00PYj8r!s/$5j7qTf1R7f0R8#8'1p==g00=oR9/68p=5g006gR:P:g01NBP8H06p=j1H:8p=;g017eR;P:!s$$2P2f3R<f2R=P7g00fMR>P9P8M<Op>0=!sL&!s$%3P8P7P=P3P<f4R?f5R@f6RAf7RBP9f8RCMBXp>0;!s[00!s[&0P<P?P@PAPBPCf9R0!sS%9!sK$1P@P1P?P9P9P<P=P7P8M<Tp>081:98p=0P:!tl$UQP8Cep=M!s4$QdR1g00RCRDPDg00RcREP8g00SCRFFdp=IP;P!t\%5P2P2P<g01Nf!t-'Op=iP!u~-P@P?!tL,Op=h!ut;!u?,P!u=$=g!sH$6P@P6!u<7<P=P1PDPDPE!u?&Q=P8CeP!tt$9P<!sD+!s[$Grp=31478#8p=a!sb-7P8Fqp=Jg004lRFg00=OR37[8p=Rg004GR2#<R5#<#<RG$0@RH$00RI#\RJPI%78%K5RK%KGRL14I8'='2'6RMX?J%8>RN,1LRO,2KRP#5RQ11L9RR,2KRS#5RTP8X<:RU1678#kXD:X<:1H:9RVPPPSPUPUPU1278#j#;XC:X>:PKPK%;KPOPR!sE&1!sE/ROPLPL%;LRPPNPUPU%88#;X<;R;PVH0=N90;N:09J081?KR%5KRN%0RPT[RT[%0KRWg00ScRXAAKR7UW2%0S\X^2W!v}$T?1y9K'HPNeRSO1RRPTg00TeRT#^RY%\TRZ%w:R[%v:R\%u:R]1E:9R^1E:KR_g01A15]:'M'I1p]ER`P8P=g00:6Ra,HF1o8==[FadAn:97CmRab4b6b712K9#5P8b3b0b5b0CZPQe%^IRQ#714IQ,=L,2K'6e%l7%77#020?H<1BH<RQ#0&0>H,6Q'@14I<RQ#GR9#8Rb,1LRc1BH?%7</>L'F%0c%8QRd%K2Re'CRf,1LRg#0PU1:!wc,RhPVPcPg!wB%P!w4$PPPbPf!s6$;P9Pf1C8eRfX<:R9PQPd%;dCiEhM:gJ0<%LQ%0d14I?Rd#8RQ,1L,?K14I@Rb#8Rg!te$#014IARV#8Ri,1LRj,2K#5[\N14IB,=LRk=AK7VXX2W12KkRl#0!wj%R%0j%5l[Rl1W:>Rm%G>R>#G,W:Rn9V:mg00flRo'f+0:=UTYRpPZ1c:7RqP\P]1Y:2R299]^Rr&07DRs1E:LRt1E:eRu9b:25P:Rv99]^C3P`P!we&X1:%08Rw1C7e,1L#0[^1:P81aICRxP?O2!w~'b8CZP41F78#0%0=Ry%07Rz'@R{[1@zw1F=7#0[R|1F<=#0\{1~78P8n20010!s#$12!s-%0X;:X=:P|^;:^=:P81BH@R|%7?/>LR{%0|%0{%Ld%0Q1?KcPl\N11LxRx!vU/x!vU0k!vU%p-0RQPYPZP!v0$P]!#3&'<E}9J]rPsPr!us2WA1@w7Pz[^1:^AQP8f:RQ,BHRE%<G#<!s$&KRG'6PEPAO3!v-,P41>78#0Py[1>=7#0\zR41>!uu$y1|!uu<>!uu$4^>!uu%%7@R4PL%Lb%0g1?Kj!uh$4I0,=LRl!uk/lRj!uk-x%5j[Rj!uf-!uV7Pz\w!x@$%7QPC!x=/O3b@C{O3b@%Gd,=L/:8PF1BHARd/D7RC1>4LRx/D7RE'Q%R8X;FPFP3%7A/>L/D=,Q8#R!s;$1_7LRA,D4RD1Q3!s<%R1PFP3P11HF3PDPcP4PA%GbRA#8Rc,1LRD/:71Cge,1L/:7R3!#8{%UP6PhPDPUP9PgO1RDO1Rh,1L!}i2cPh!}i&APDP9PbPg%;g!}`&P7P7%;7M<TP8CxRgP3%LVRV%0iRi1?KkRkPj\NRj!#4,%Rb!w'+R912KbRD!w,&RAPR%0l%5D[RDPp!w//AP:t2Rp!|]611L7R;#0!w>&f;RU,aIRh!|[1b:PgP3PVPiPkPjP9PAPRPD!x;$:1c:=RcP7P[CSRP!xI+]1Y:5RO,M2,I]R6PsAJ]r6C3!tN2X9:167=16=<,@y[!tU$^9:P811LhR<,2KR6%7UP0PQO4!t_H!tQ$A9]vOPsAz:Ot99]p!tD61Lf/:71_=L,:;[!tE'PBPhP@!|G/b:E`ENPEP4PLP7!tE7201:L>02:n1W:>=V:m5V:/fo=UTYRTPZP:P[P7P:PcP=P[CSCSRcP\P]&035,Y:R599]^RoPsP]Ab:5u9P:t=9]2R5!|1%!u36C=!zI'ePy[\z!u5+hPBP?P@O4R@!u9/CtENPCPLPd!u99!vX$[P\A9]^t!t<,%0LR^!#;T+!w>/1?KL12KLR[#5\^R^\NAAKL!zW%%0[!zP$1?Kl%0b%56[\Nf<,4I,=LRN!#3+-NRN!#3+,<%5N[P?PSO1P^!#32+1E:G!y_%!#5n$A]:_H!s7,!{9368G,@w167[,@z!#8p$f?,BHPU!{:$B!uC&IbB!y_<TPZP!wj$P!w]$P5PsA9]t2!wS8:L=\e!wJ+@!yQ31Fdx/D7B04dx7ENWGXJ:I05bFbEAUI=7R=#714I=!#?B'XHMX?JX;IP8DsW?o"). Qed.

Lemma bytes_le_app : ltac2:(zQ "c0!h9!jc!jnf!ime!jq3!jp0!vd!hga!hmd!hrc!jp9!ik7>2xs@1$3@1$1@1$0#8>2ys@1$3@1$1@1$0#8@3$6$7@1$2@3$4@1$1@1$0#8^2^1@2$8@1$2^2@2$b@1$2^1@2$9+8@1$a@2$5@1$1@1$0#8^2").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##;1h01zh11xh24__x1h32xsh42ysh57__arithh64__ffh78__varmaph85__with94cstrh:2IHh;1mh<1nh=1yp;1p;3p;2p;6p;4p;<p;8p;5p;Bp;7g001:j1@Tg002Dj1p!s/$bj1\Tg00BRj1BTg01OJj39Tg01AOj14Tg005Lj1KTg01EQj27Tg01F1R0j15Tg00bmR1j23Tg01BLj21j1ZTg00V8j20j1[!sx$gj1oTg01PHj1h!s/$lj1dTg000\j6F!tM$2j1ETg007Ej2CTg00^iR2j1<Tg00h>j2:Tg003mj2;Tg009>j1Yj3J!t[$Qj1XTg01LTj4WTg01J@l<RTg01Hoj1QTg00:Vj2=Tg00C2j2O!s/$Pj1P!s/$nj1NTg00DYj2>Tg00E<j2T!uR$Jj3MTg00ifj3LTg00Jcj4?Tg00Fej2nTg00GGj2mTg00H3j3l!s/$Rj4k!tg$oj4gTg00jIj8ITg01QMj3fTg00_Hj2GTg00`1j3c!s/$Zj2bTg01ITj2aTg00aFj3H!t^$_j1eTg00PYj8`Tg01R0j4_!s/$Wj3iTg01Doj5^Tg01M7l<D!s/$\lBjTg00Nmj7]Tg006gR3f1R4f0R53Jp=21;35p=8P3f4R6f3R7f2R8P4P5EFp=6g017eR9P9P3P3P2P0P0P7g01NfP!sK$M<Dp=V!sE&3P0P0f5R0P6P7!sF-U!sD&!s$%1P5P4P8P1P7P6P0f6f7f8f9MBjp=SP4g00QdR0g00RCR1P1g00RcR2P5g00SCF]p=Ag004GR:#@#@#@R;#pR<#\R=#BR>P=A9=45#4%44R?%45R@%K;R;17=4#5'3'1'0'2^4>RAX3>P3g00=oRB11?5,0B,2?X03P@10B5!s2+2?5X03%8@10B@%o@D611@B%h@D613;B%d;EF%E=RC=9=!tG$C17=C#5,3;,1@'0'2eX4>%48RC17=8RD#5RE,3;RF,1@RG'0RH1C<6RI115;'0%47/1;RJ,0I17=7#<!sp&?'0R?'2X0311C;RK11G;RL'010I5/!tz$1:F;RM,1@RN10J5,0I!s>&C<7R</0KRI/0N125!uO$3P3%[IRIPIPN%<DR?#5RJ,3;RO,1@P3\3RP/;I!sM$Z@!sM$MPO1;PI12MO%K:RI,:ERP,3;RQ,2M!sO$Y3RRP5X13RSPR1245#XX=3X13PMPM%8MPOPQPS!s$$3P3g01NB1345CW#8X;3X<3P;P;%8;PJPPPSPS%55#8X19P?PP1:5IRPX13PDPE%8ECVEUM:SM<R%QDRD1=BEREg00TeR?#ER9%B?RS1O34RJ%P3RQ%N3ROP31>3;RM1T3:R:5M3RR=L3Mg00l[1>3I9L3:9M3MC?'A1nO2RMP5P8g004lRIg00:6RT';1m58=JITdAl3B4CkRTb6b7b8X2313;5/:;13;P'2^23P517=6#5R6O1b5b9CgGIGI10KN,0<Af<KND6PLP@PFP;PDPEg00fMRE,G3RD%<E#<,G39c3Dg00fl'b'a=H?9PSPJPQPOP0P1P1P2!uL$BR2g00Q=R0P:C?,AO%e1!}i&R!s6$G`PMP!tx-=B513;4,=B[!tw$P6P4O2!ts$_D611H;AiCG;D6A9=85#4P4P5O1D6AH=78R8!{T'817=8!{T3X:AX3>X1=P5D^W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_range : ltac2:(zQ "70!h9!hq7!hke!hk0!hl4!hif!jc>1x@1$6@1$0#k0@2$2@2$3Z@2$1@1$0#k0^1@2$4@2$1@1$0#k0^1@2$5+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "###th01xp;1p;2g001:j10Tg002Dj13!s/$bj12Tg01Blj21Tg004G#0!s$-3R0#2f0,10W0o"). Qed.

Lemma u6_range : ltac2:(zQ "60!h9!hq7!hke!hk0!hl4!jc>1s@1$5@1$0#6@2$2@2$3Z@2$1@1$0#6^1@2$4@2$1@1$0#6^1+k0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sp;1p;2g001_j14Tg001:j13Tg002Dj10Tg002bj11Tg01Blj22Tg004G#4#3#0R0#1f0,20W0o"). Qed.

Lemma u5_range : ltac2:(zQ "60!h9!hq7!hke!hk0!hl4!jc>1s@1$5@1$0#5@2$2@2$3Z@2$1@1$0#5^1@2$4@2$1@1$0#5^1+i0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01sp;1p;2g001:j14Tg001_j13Tg002Dj10Tg002bj11Tg01Blj22Tg004G#4#3#0R0#1f0,20W0o"). Qed.

Lemma wrap64_range : ltac2:(zQ "70!h9!hj6!hke!hga!hk0!hl4!hif>1z$3@2$2@2$4Z@2$1@1$0#k0^1@2$5@2$1@1$0#k0^1@2$6+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "###kh01zp;1p;2g001:j10Tg002Dj12Tg01S;j21Tg006gg004G#0!s$-2f0'1W0o"). Qed.

(* [comment removed for export] *)
Lemma bv_swrap_congr : ltac2:(zQ "50!hga!vd!hod!hj6!hp8>1n$4>1x$0>1y$0>0@3$1$0@2$3^3^2@2$3^3^1@3$1$0@2$2^4^3@2$2^4^2").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11Hh21nh31xh41yp;2p;3p;1p;6p;8g00gXj20Tg009>j32Tg00h[j16Tg00h>j21Tg00iIR0j19Tg003mj23Tg00jfj38Tg000\j65Tg00kXj6:Tg00jIj87Tg00l4j24Tg009Xg006gR1f2R2f1R3'0f0R4,02521P1P1f3R5%65R6,12'0R7#91136,05R8#9P6P6P1P1\1R9P0P0P7P8P9\1/30P11052R0/16,05f4R9%69R:,12'0R;9214X01R<P11053R=114:,09=21;X01P1P8P<131811=6,05A8536E5P0P4E5P7A8526E:G71316G714521453521eW1X41W3W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b_addsext : forall (a : word) {n} (imm : bv n),
  a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zh22b1h32b2h41Hh51ah63immp;1p;3p;2p;6g001:j13Tg002Dj1CTg002bj11Tg009>j36Tg007Ej20Tg018`j3>Tg019mj3=Tg014Xj39Tg01;]j28Tg01Sjj2<Tg01?Nj3;Tg00h>j25Tg00gXj24Tg01<Ej2:Tg01U1j3BTg01>_j2ATg000\j67Tg01@;j3@Tg01Ucj3?Tg006gR0f1R1f0R236p=2g004G#3#3#3#3#3#3#CR3#1g009XR4%12R5%11R6g00;Nf2R7#1?612f3R8/071081'2R9[10711072'2%18?671[R:f4R;#1?687\9A>712P2n2001000000120000000W3X25X04P:^36^25^04P2P3A=7319938R41871R5,<8R6P01038R:A;731R9,03R<'5,43103;R;1887R='5,:3,03R>,22X10P0143515;2,43/2>X10P015:5R>,43143=,5;,43/22X10AB3:51:3>,031A3>E7P<A@731E7A9389,03A?389E710341036'2eO4b4W6W0W5o"). Qed.

Lemma b_npc4 : ltac2:(zQ "60!h9!jc!vd!ihc!u7!jq9>1p@1$1@1$0#k0@3$2@1$1@1$0#k0@3$5@1$0#k0^1@2$4@1$0#k0+4@2$3^1+4").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51pp;1p;3p;2p;6g001:j13Tg002Dj1@Tg002bj11Tg009>j36Tg007Ej20Tg018`j3=Tg005Lj1<Tg01<Ej27Tg014Xj3;Tg01Sjj2:Tg00h>j25Tg00gXj24Tg01U1j3?Tg01>_j29Tg000\j68Tg01Ucj3>Tg006gR0f1R1f0R236p=2g004G#3#3R3#3#3#3#3#@R4#1g009XR5%12R6%11R7g00;Nf2R8#1?612f3R9/081091'2R:[10811082'2%19?681[R;f4#1?698\:A=812P2n2001000000120000000W2W1W3P;^27^16^35P2P4%<3R3,74R59;41R61:13R7P01041R;1045R:'5,441048R8/53,74,04R9,22X00P01443R<1582,44/29X00P015;3R9,44158<,44/22X00A?4;31749,041949E8P:1943E81046R6A>415E81047,26eO4b4W5o"). Qed.

Lemma alu_addi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$5h01ah13immh21np;1p;3g001:j10Tg002Dj13!s/$bj11Tg01VQj32Tg004G#0!s$-3#1g009Xf0R0#1f2f1;20W1W2W0o"). Qed.

Lemma alu_andi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm).
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##/ch01zh11nh21Hh32b1h42b2h51ah63immp;1p;3p;2p;4p;6g001:j13Tg002Dj1L!s/$bj12Tg009>j35Tg007Ej20Tg018`j3ETg019mj3@Tg01W[j3>Tg01;]j28Tg01XCj2<Tg00>hj26Tg00gXj24Tg01<Ej2;Tg01YJj1KTg00:Vj2:Tg005Lj19!s/$jj2JTg00;2j2ITg01ZTj1DTg01[aj4BTg01\nj3ATg01]Zj4?Tg01>_j2CTg000\j67Tg01?Nj3FTg01@;j3GTg01^6j3H!s/$[j3=Tg006gR0f1R1f0R235p=1g004G#3R3#!s$+R4#LR5#2g009XR6%22R7%21R8g00;NR9f2R:#2?512f3R;/0:10;1'1R<[10:110:2'1%2;?5:1[R=f4R>#2?5;:\<AE:12P2n20010!s#$12!s-%0W4X37X16P=^48^37^16P2P5g01_IA@:51R67>;R718:1R8,<;R=P0105;R<1056'6R?105>R>18;:R@,45'6RA,;5,05RB,12X00P01458R816>2/1B!s8%6<8RB,45R>11A!sL%P>PBP<P8%K;P9g00=oR91452R8':R<%93%94'J,I81451,:9%D2P1!uK7X00P<^00P2P@O1b2CB9A5BC?1;5B,05R@1C5BE7AF:51,05AG:51E711?@eAH5;6,05A=5;6E71057105='1eO4b2W6W1W5o"). Qed.

Lemma alu_ori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zh22b1h32b2h41Hh51ah63immp;1p;3p;2p;4p;6g001:j12Tg002Dj1HTg002bj13Tg009>j34Tg007Ej20Tg018`j3>Tg019mj3=Tg01W[j3;Tg01;]j28Tg01`5j2:Tg00V8j25Tg00gXj26Tg01<Ej29Tg01YJj1GTg01ZTj1FTg01a;j4CTg01\nj3BTg01]Zj4@Tg01>_j2?Tg000\j67Tg01?Nj3ATg01@;j3<Tg01bGj3DTg01bkj3ETg006gR0f1R1f0R234p=1g004G#2#2#2#2#2#2#HR3#3g009XR4%32R5%31R6g00;Nf2R7#3?412f3R8/071081'1R9[10711072'1%38?471[R:f4R;#3?487\9A>712P2n2001000000120000000W3X25X04P:^36^25^04P2P3g01cXA=731R47;8R51871R6,:8R:P01038R91034'5R<103;R;1887,63'5R=,93,03R>,12X10P01636R?15;2/1>X10P0159?R>,63R;11=2X10P0P;P>P9P?%G8%F6CC9B3>C@193>,03R61?3>E7AA731,03A<731E711<6eAD384,03AE384E71035103:'1eO4b4W6W0W5o"). Qed.

Lemma alu_xori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm).
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01nh11zh22b1h32b2h41Hh51ah63immp;1p;3p;2p;4p;6g001:j12Tg002Dj1HTg002bj13Tg009>j34Tg007Ej20Tg018`j3>Tg019mj3=Tg01W[j3;Tg01;]j28Tg01dDj2:Tg00XVj25Tg00gXj26Tg01<Ej29Tg01YJj1GTg01ZTj1FTg01eKj4CTg01\nj3BTg01]Zj4@Tg01>_j2?Tg000\j67Tg01?Nj3ATg01@;j3<Tg01fXj3DTg01g=j3ETg006gR0f1R1f0R234p=1g004G#2#2#2#2#2#2#HR3#3g009XR4%32R5%31R6g00;Nf2R7#3?412f3R8/071081'1R9[10711072'1%38?471[R:f4R;#3?487\9A>712P2n2001000000120000000W3X25X04P:^36^25^04P2P3g01gkA=731R47;8R51871R6,:8R:P01038R91034'5R<103;R;1887,63'5R=,93,03R>,12X10P01636R?15;2/1>X10P0159?R>,63R;11=2X10P0P;P>P9P?%G8%F6CC9B3>C@193>,03R61?3>E7AA731,03A<731E711<6eAD384,03AE384E71035103:'1eO4b4W6W0W5o"). Qed.

Lemma alu_slti : ltac2:(zQ "80!h9!jc!vd!jt6!jj4!ju1!ju9!hpb>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#c@1$0#k0^1@2$6^2@2$7@1$0#c^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##0Hh07__arithh14__ffh28__varmaph35__with41ah53immh61zp;1p;2p;3p;4p;7p;6p;<g001:j10Tg002Dj19!s/$bj18Tg001_j1=Tg01;]j21Tg01hWj24Tg005Lj15Tg01<Ej26Tg009>j33Tg003mj22Tg01?Nj3<Tg01i4R0j2;Tg00:VR1j2:Tg00B2j1P!s/$Rj1OTg00IDj1ITg00CPj1H!s/$nj1ETg00DYj27Tg00Jcj4CTg00Nmj7BTg00Fej2ATg00GGj2@Tg00H3j3D!s/$Rj4?Tg01Foj4F!tY$Pj4GTg000\j6>Tg019mj3JTg01jDj3KTg01W[j3LTg01k1j2MTg01J@l<N!u[$Xg006gR2P0g01<kP1g01l8f5f4f3f2R1f1R0f0R3M<Np=Qg004GR4#0!s$,R5#9R6#8R7%=!s?$R8#9R9#8P21193R:g004lR;P71161R</43%54,66R4g00=oR=,66R>n010!s#$20000P!sU$90,4<P4P!sC2537X62!sI%60/4:!sI5R<,27A<963,16P9P6P31;96%58R8%55R5':R?P9P81228P6P51225EQg00TeR@#P%O@%I2%H2%E2R@g00Qdg00RCRAPAg00RcRAP21728g00Q=1725CCg00SCFB1A@AP3P1g00:6RA,2;1@31=3;AdAD2=0C?b1b2b3P?P3b0CFCGE>P;P7AJ963R99K60!uF5=37<eg01lX?L091M0:537eW5W4o"). Qed.

Lemma alu_sltiu : forall (a : word) {n} (imm : bv n),
  alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm).
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##+5h01ah13immh21nh31zp;1p;2p;3p;6g001:j10Tg002Dj1A!s/$bj14Tg01;]j25Tg00gXj27Tg007Ej23Tg01hWj22Tg005Lj1;Tg01<Ej26Tg009>j31Tg003mj28Tg01?Nj39Tg01@;j3:Tg000\j6@Tg019mj3?Tg01mDj3>Tg01W[j3<Tg01n1j2=Tg004GR0#!s$/AR1#4R2g009Xf0R3#4g006gR4f1R5/53R6,71R7g004lR8P2f3,31R9/23%;0,61R0g00=o,61R:n010!s#$20000P8P2f2R;/55,71,29P0P!sI2512X34P8P2131;/27!sI5R7,82A9513,31A:513E@P8P2A?513R59>1;!s[5=127eg01o9?<;51=;6512eW1W2W0o"). Qed.

Lemma alu_add : ltac2:(zQ "60!h9!jc!vd!jv3!ju1!jve>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg01oej21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_sub : ltac2:(zQ "60!h9!jc!vd!kg7!ju1!kh2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg020kj21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_slt : ltac2:(zQ "60!h9!jc!vd!jt6!ju1!khb>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg0221j21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_sltu : ltac2:(zQ "60!h9!jc!vd!ki4!ju1!kj0>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg0237j21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma alu_and : ltac2:(zQ "60!h9!jc!vd!kja!ju1!kk5>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##-Eh01Hh12b1h22b2h31nh41xh51zh61ah71bp;1p;3p;2p;4p;6g001:j12Tg002Dj1F!s/$bj13Tg009>j31Tg007Ej20Tg018`j3CTg01W[j3=Tg024>j2<Tg00>hj25Tg01<Ej27Tg00gXj2:Tg01YJj14Tg00:Vj26Tg005Lj19!s/$jj2ETg00;2j2DTg01[aj4BTg01\nj3@Tg01]Zj4>Tg01>_j2?Tg000\j68Tg01^6j3A!s/$[j3;Tg004G#2R0#2!s$'R1#FR2#3R3g009XR4f0R5#3R6f1R7#3R8g00;NR9f2R:#3?175g006gR;f3R</0:10<731R=[10:710:551;%3<?1:7[R>f4#3?1<:\=AC:75P5n20010!s#$12!s-%0W2W1W3P>^28^16^34P5P2g01_I?=:7R41<:7R6P;102:R81027R>'5R=102</58R<,72,0291;5X5;P;1:2=R?A1;<!s6%P?P=P8P>%4:P9g00=oR91025R8'6R?%90%91'E,D8169>%45P7!tt7X43P?^43P5P:O1b0CB9@2=C>172=,021?2=E8AA2:7,02A;2:7E81024102651;eO4b0X73W6o"). Qed.

Lemma alu_or : ltac2:(zQ "60!h9!jc!vd!kke!ju1!kl8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31zh41Hh51ah61bp;1p;3p;2p;4p;6g001:j13Tg002Dj1BTg002bj12Tg009>j31Tg007Ej20Tg018`j3<Tg01W[j3;Tg025Dj29Tg00V8j25Tg01<Ej24Tg00gXj28Tg01YJj16Tg01a;j4:Tg01\nj3ATg01]Zj4@Tg01>_j2?Tg000\j67Tg01bGj3=Tg01bkj3>Tg004G#3#3#3#3#3#3#BR0#2R1g009XR2f0R3#2R4f1R5#2R6g00;Nf2R7#2?153g006gR8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P0g01cX?;75R21975R4P81007R61005R;'5R:1009/56R9,40,009183X38P8180:R<A1893X38P8P<P:P6P;%67%65C:9A0:C@140:,001?0:E7A=075,00A>075E710021004518eO4b4X61W5o"). Qed.

Lemma alu_xor : ltac2:(zQ "60!h9!jc!vd!km0!ju1!kmb>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02b1h12b2h21nh31zh41Hh51ah61bp;1p;3p;2p;4p;6g001:j13Tg002Dj1BTg002bj12Tg009>j31Tg007Ej20Tg018`j3<Tg01W[j3;Tg026Ij29Tg00XVj25Tg01<Ej24Tg00gXj28Tg01YJj16Tg01eKj4:Tg01\nj3ATg01]Zj4@Tg01>_j2?Tg000\j67Tg01fXj3=Tg01g=j3>Tg004G#3#3#3#3#3#3#BR0#2R1g009XR2f0R3#2R4f1R5#2R6g00;Nf2R7#2?153g006gR8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P0g01gk?;75R21975R4P81007R61005R;'5R:1009/56R9,40,009183X38P8180:R<A1893X38P8P<P:P6P;%67%65C:9A0:C@140:,001?0:E7A=075,00A>075E710021004518eO4b4X61W5o"). Qed.

(* [comment removed for export] *)
Lemma shamt6_mask : ltac2:(zQ "80!h9!hq7!vd!hga!kn4!u7!jc!knb>1s@1$6@1$0#6@3$2$3@2$1@1$0#k0@3$7@1$0#k0@3$4@1$0#6@1$0#k0^1@2$5@1$0#k0+jf@2$1@1$0#6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##4?h07__arithh14__ffh28__varmaph35__with41zh52Hah66__sat1h7!s/%0h81sp;1p;3p;2p;4p;6p;7p;<g001_j13Tg001:j10Tg002Dj1=!s/$bj1CTg027Oj3`Tg007Ej22Tg005Lj16Tg01<Ej2GTg00>hj2:Tg009>j35!sJ$jj2>Tg006Gj2ATg028:j1@Tg029Cj3_!s/$fj1UTg00B2j1T!s/$Rj1MTg00IDj1LTg00CPj1K!s/$nj1JTg00DYj24Tg00Fej2FTg003mj28Tg00GGj2ETg00H3j3H!s/$Rj4ITg00:VR0j21Tg02:Dj3DTg000\j69Tg00@Ej2BTg00;2j2<!s8$mj3NTg00AQj2OTg00J@j3P!s/$cj4?Tg00P5j7Q!s\$Nj2R!t$$gj3STg02;Sj3^Tg01i4R1j2]Tg01Foj4VTg02<@j4WTg01^6j3X!s/$[j3YTg00Nmj7ZTg01J@l<[!v]$gR2f1R3g00Q=f0R4C?p=;P!s6$dR5g00RCR6P6g00RcR7P4g00SCFZp=7g009XP2P1g01<kP0g01l8f5f4f3f2R0P3P4M<[p=\g004GR1#3R8#0R9#=R:#CP2%01R1#0!s$'R;#=R<A`:<4R='2%38#3!s$$6R8,G<R>,2<R?':R@12:3RA9524X42RBP212:4RC1:4?=52AX42P2P81:A4!s5+%61R1%69R9'>RA,ACPB%@49_CA%U9,:Cg00TeRA#TRB%MARA%L2RD%K2RE%J2RFg00=oRG,42RH1429RI';'71FF7RJP4P0g004lRKg00:6RL'81E40=5KLdAH2G3CIRLb1b2b311G9P4b09DC9E9P?%6;R;,B11<G1R?11G;1>1;RK,<G[R0[11G1RMg00ScRNAN1;3UW511GK\N^5M!wk$T?1OG1'8P?eO1P0PBPAPDPEPFP5P6P6P71428R7,;H,7FP2P7g00UQ1421=P2<C?,7FFQPJP!to,81<8K'RP4b0b6b7b69S<8E9A^:<4,2<P:P<P41]:<119;R8P:P91829P<P;182;E\!tR'142;,;I,7F!t-,P8P4b0CVCWE9A52@CeAX<=>,2<AY<=>E9W8o"). Qed.

Lemma regamt64_mask : ltac2:(zQ "80!h9!hq7!vd!hga!hi5!u7!jc!knb>1b@1$6@1$0#k0@3$2$3@2$1@1$0#k0@3$7@1$0#k0^1@2$5@1$0#k0+jf@2$4@2$1@1$0#k0^1+k0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h02Hah17__arithh24__ffh36__sat1h48__varmaph55__with61zh76__sat0h81bp;1p;2p;3p;4p;6p;7g001:j10Tg002Dj1VTg002bj1HTg007Ej25Tg001_j12Tg005Lj13Tg01<Ej2JTg00>hj29Tg006Gj2:Tg009>j37Tg005jj2>Tg003mj2=Tg029fj1?Tg00B2j1UTg00BRj1TTg00IDj1STg00CPj1MTg00Cnj1LTg00DYj24Tg00Jcj4;Tg00Fej2ITg00GGj2GTg00H3j3FTg00HRj4ETg00:Vj21Tg02:Dj3DTg000\j66Tg00@Ej2CTg00;2j2<Tg00@mj3KTg00AQj2BTg00J@j3ATg00P5j7NTg00;Nj2@Tg02:gj3OTg01^6j3PTg01^[j3QTg00Nmj7RTf1R0g00QdR1g00RCR2P2g00RcR3f0R4g00SCFRp=8g004GR5#0R6#0#0#0#0#0R7#VR8#Hg006gR91584R:%25R5#2#2#2#2#3R;,J8R<,58R='91580R>%37R7':R?9794X69R@P9P;19>4=79?X69P9%36R6%05#3R5'>,::P@1::7,=9%?5,9:g00TeR@#UR?%T@R@%S9R>%M9RA%L9RBP9g00=oRC,49RDg00Q=RE1495C;'81IB3RFP4f2RGg004lRHg00:6RI'=1G4G=7HIdAF9C0CERIb2b4b511C5P4b19D:5E6P=1C671<C6R=11C71>67R5,<C[R:[11C6RHg00ScRGAK670UW011C5\G^0HP0g00T?1BC6'=P=eO1P:P?P@P>PAPBP1P2P2P3P9PDPE149;REC;,8BP9PEg00UQ1496=A98C;,8BFNPFPIb2b4b511C;1<;5'@P4b1b3b7b39O8;E6AP84<,58AQ84<E6W8o"). Qed.

Lemma alu_slli : ltac2:(zQ "80!h9!jc!vd!ko4!kn4!ju1!kof!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6g001:j11Tg002Dj1;Tg002bj12Tg001_j15Tg009>j37Tg007Ej20Tg018`j3@Tg027Oj3:Tg01W[j3?Tg02=6j2>Tg005Lj1=Tg01<Ej28Tg01^6j3<Tg01BLj26Tg00gXj24Tg003mj2ETg02>=j1DTg000\j69Tg01>_j2CTg02?Ij3BTg02@1j3ATg006gR0f1R1f0R237p=3g004GR3#1#1#1#1#1#1#;R4#2%53R3#1#;R5#2g009XR6%22R7%21R8g00;Nf2R9#2?712f3R:/0910:1'3R;[10911092'3%2:?791[R<f4#2?7:9\;A@912P2n2001000000120000000W2W1W3P<^28^17^36P2P4g02@bA:541R67?9R71051R8,>9R<P01049R;%53#5#5#5#=,84R39<46R6,04R='6,44104:R:1059'6R>,84,04,32X00P016;8R;,44R?A:549=<43,04,6:,44/32X00P0P816:2,44144>'3X001E0?P=%D1E9184;,041C4;E9AB496,04AA496E91047104<'3eO4b4W6W5o"). Qed.

Lemma alu_srli : ltac2:(zQ "80!h9!jc!vd!kp9!kn4!ju1!kq4!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##/eh01sh11zh21Hh32b1h42b2h51nh61ap;1p;3p;2p;4p;6g001:j12Tg002Dj1:!s/$bj11Tg001_j14Tg009>j36Tg007Ej20Tg018`j3CTg027Oj3;Tg01W[j3@Tg02ANj2?Tg005Lj19Tg01<Ej27Tg01^6j3>Tg00d[j25Tg00gXj2=Tg01YJj1KTg00:Vj2<Tg00;2j2JTg028:j1ITg02BUj4HTg01\nj3ETg01]Zj4BTg02>=j1DTg000\j68Tg01>_j2ATg02Cdj3FTg02DLj3GTg006gR0f1R1f0R236p=3g004GR3#2!s$,R4#:R5#1%43!s?$:R6#1R7g009XR8%12R9%11R:g00;NR;f2R<#1?612f3R=/0<10=1'3R>[10<110<2'3%1=?6<1[R?f4#1?6=<\>AC<12P2n20010!s#$12!s-%0W4W3W5P?^4:^39^58P2P5g02E=A;651R87@<R91061R:,?<R?P0105<R>%43#4!s$$9,75R39>58R8,05R@'5105=R=106<'5RA,75,05,32X10P015>:RB,=5RCA;65<=>53,05,5=/!sH&P:15=21=5A'3!s7%CPBP>P:%K<P;g00=oR;1062R6'<R>%94,J61<;:%I2P1!u\7X07P>^07P2P<O1b2CH9E5BCBP@%D1E8175B,051A5BE8AF5<8,05AG5<8E81059105?'3eO4b2W0W6o"). Qed.

Lemma alu_srai : ltac2:(zQ "80!h9!jc!vd!kqe!kn4!ju1!kr9!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6g001:j11Tg002Dj1<Tg002bj12Tg001_j14Tg009>j37Tg007Ej20Tg018`j3BTg027Oj3;Tg01W[j3@Tg02Eij2?Tg01;]j2:Tg005Lj1>Tg01<Ej29Tg01^6j3=Tg00d[j26Tg00gXj25Tg003mj2FTg02>=j1ETg000\j68Tg01>_j2DTg02G0j3CTg02GYj3ATg006gR0f1R1f0R237p=3g004GR3#1#1#1#1#1#1#<R4#2%43R3#1#<R5#2g009XR6%22R7%21R8g00;Nf2R9#2?712f3R:/0910:1'3R;[10911092'3%2:?791[R<f4#2?7:9\;AB912P2n2001000000120000000W2W1W3P<^28^17^36P2P4g02HKA;541R67@9R71051R8,?9R<P01:49R;%43#4#4#4#>,94R39=46R6,04R='6,541:4:R:1059'6R>,94,04,32X00P016;8R;,54R?A;549==43,04,6:,54/32X00P0P816:2,54154>'3X001F0?P=%E1E8194;,041D4;E8AC496,04AA496E81047104<'3eO4b4W6W5o"). Qed.

Lemma alu_sll : ltac2:(zQ "60!h9!jc!vd!ko4!ju1!ks3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g001:j12Tg002Dj1ETg002bj11Tg009>j37Tg007Ej20Tg018`j3?Tg01W[j3>Tg02I7j2=Tg001_j15Tg005Lj1;Tg01<Ej28Tg01^6j3:Tg01BLj26Tg00gXj24Tg006Gj2<Tg003mj2DTg02J=j1CTg000\j69Tg01>_j2@Tg02?Ij3ATg02@1j3BTg006gR0f1R1f0R237p=3g004GR3#2#2#2#2#2#2R4#ER5#1R6g009XR7%12R8%11R9g00;Nf2R:#1?712f3R;/0:10;1'3R<[10:110:2'3%1;?7:1[R=f4#1?7;:\<A?:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5g02@b?>:1R71=:1R8P0105:R9%53#5#5#5#5#;,85R39:51R=,05R<'6,45105;R;%;4R4,<9'6R>,85,05,32X00P01051/<4R4,69R9,45R?A:5:3,05,6;,45/32X00P0P416;2,45145>'3X001D0?P<%C1E91859,051@59E9AA5:=,05AB5:=E910571058'3eO4b4X66W5o"). Qed.

Lemma alu_srl : ltac2:(zQ "60!h9!jc!vd!kp9!ju1!ksc>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##5Bh01zh11Hh27__arithh34__ffh44__p1h58__varmaph65__with74__x1h82b1h92b2h:1nh;6__sat0h<1ah=1bp;1p;3p;2p;4p;6p;7p;8g001:j12Tg002Dj1b!s/$bj13Tg009>j35Tg007Ej20Tg018`j3RTg01W[j3LTg02KKj2KTg001_j16Tg005Lj1<Tg01<Ej29Tg01^6j3ATg00d[j27Tg006Gj2;Tg00gXj2BTg01YJj1XTg00B2j1V!s/$Rj1UTg00IDj1QTg00CPj1N!s/$nj1MTg00DYj2?Tg00Jcj4>Tg00Fej2JTg003mj2HTg00GGj2GTg00H3j3F!s/$Rj4ITg00;2j2:Tg02LQj3E!s8$NR0j2@Tg02M8j2D!t<$2j2OTg00E<j2PTg00OQj6CTg00P5j7S!sA$_j1T!s8$Yj8aTg02BUj4`Tg01\nj3_Tg01]Zj4]Tg02J=j1\Tg000\j68Tg01>_j2YTg02Cdj3ZTg02DLj3[Tg00Nmj7WTg00:Vj2^!v[$gR1f1R2f0R335p=1P2g00QdR4g00RCR5P5g00RcR6P3g00SCFWp==g00=oR7/^3p=4g004GR8#2!s$,R9#bR:#3R;g009XR<%33R=%32R>P0f2R0#3?523f3R?/0010?2'1R@[10021003'1%3??502[RAf4RB#3?5?0\@AR023P3n20010!s#$12!s-%0W9W8W:PA^9>^8=^:<P3P:g02E=?L02R<1K02R=P110:0R>%68#6!s$&<,9:RA9A:2R@,0:RC'710:?RD%<9R9,;>'7RE,9:,0:,13X01!sk$2RF/;9RG,7>RH,B:RIAA:0A,0:,7D/!sN&PG17D31B:E'1!s7%IPHP>PG%X0g00TeRI#VRE%UIRI%Q1%N1RD%M1RAP11?17RJg00UQ1?19C>'=1JA6RKP3P0g004lRLg00:6RM'H1G30=5LMdAF172CIRMb3b5b61:79P3b29EF9%4G1:G9'@1D>9%4>%4910:B/;9RB#4[[p-0R>PEPI1O12PDPAP4P5P5P6!s0-1PJg00Q=1P18C>,=AR8!sD-?ECFS%T5P8GaPKP!tR&X71W4%43/@2%42[^71^4>P31:B9PBP0O3b2b;b1C`9_:HC]PC%\2E819:H,0:1Y:HE8AZ:0@,0:A[:0@E810:<10:='1eO4b1X=;W<o"). Qed.

Lemma alu_sra : ltac2:(zQ "60!h9!jc!vd!kqe!ju1!kt5>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g001:j12Tg002Dj1FTg002bj11Tg009>j37Tg007Ej20Tg018`j3CTg01W[j3@Tg02Mij2>Tg01;]j2;Tg001_j15Tg005Lj1:Tg01<Ej28Tg01^6j3=Tg00d[j26Tg00gXj24Tg006Gj2<Tg003mj2ETg02J=j1DTg000\j69Tg01>_j2BTg02G0j3ATg02GYj3?Tg006gR0f1R1f0R237p=3g004GR3#2#2#2#2#2#2R4#FR5#1R6g009XR7%12R8%11R9g00;Nf2R:#1?712f3R;/0:10;1'3R<[10:110:2'3%1;?7:1[R=f4#1?7;:\<AC:12P2n2001000000120000000W2W1W3P=^29^18^37P2P5g02HK?@:1R71>:1R8P01;5:R9%53#5#5#5#5#:,85R39=51R=,05R<'6,451;5;R;105:%:4R4'<'6R>,85,05,32X00P01051/<4R4,69R9,45R?A=5:3,05,6;,45/32X00P0P416;2,45145>'3X001E0?P<%D1E91859,051B59E9AA5:=,05A?5:=E910571058'3eO4b4X66W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma low32_unsigned : ltac2:(zQ "70!h9!hq7!vd!hga!kte!jc!hj6>1a@1$5@1$0#k0@3$2$3@2$1@1$0#i0@1$4^1@2$6@1$0#i0@2$1@1$0#k0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11ap;1p;2p;3p;6p;4g001:j10Tg002Dj16Tg002bj1;Tg007Ej21Tg01<kj1=Tg00d[j25Tg00gXj22Tg009>j33Tg003mj2:Tg01=Ij18Tg000\j64Tg019Dj47Tg01=mj49Tg02Noj1<Tg004G#0#0#0#0#0R0#0#6R1#;g006gR2%60R0f0R3,11R4g01A1R5#='5'2f1,11,20R69323X02P2P41203=326X021204R6,:2g00=o,54%84E4P1P5P0P3C7,10P1P5P0P3C9E4%<3,10=326eW1o"). Qed.

Lemma low32_signed : ltac2:(zQ "80!h9!vd!hga!kte!jc!hpb!hod!hq7>1a@1$4@1$0#k0@3$1$2@2$5@1$0#i0@1$3^1@2$6@1$0#i0@2$7@1$0#k0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh11ap;1p;2p;3p;6p;4g001:j10Tg002Dj17Tg002bj1;Tg007Ej23Tg01<kj1>Tg00d[j26Tg00l4j21Tg009>j32Tg003mj2:Tg01=Ij19Tg000\j65Tg019Dj48Tg01;]j24Tg02OWj4=Tg02Noj1<Tg004G#0#0#0#0#0R0#0#7R1#;g006gR2%70R0f0R3,31R4g01A1R5#>'6'1f1,31,10R69223X02P2P41103=226X021104R6,:2g00=o,64%94E5P1P5P0P3C8,40P1P5P0P3C=E5%<3,40=226eW1o"). Qed.

(* [comment removed for export] *)
Lemma shamt5_mask : ltac2:(zQ "80!h9!hq7!vd!hga!kn4!u7!jc!knb>1s@1$6@1$0#5@3$2$3@2$1@1$0#i0@3$7@1$0#i0@3$4@1$0#5@1$0#i0^1@2$5@1$0#i0+hf@2$1@1$0#5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h07__arithh14__ffh28__varmaph35__with41zh52Hah66__sat1h76__sat0h81sp;1p;3p;2p;4p;6p;7p;<g001:j12Tg001_j13Tg002Dj1=Tg002bj1CTg027Oj3`Tg007Ej21Tg005Lj16Tg01<Ej2GTg00>hj2:Tg009>j35Tg005jj2>Tg006Gj2ATg02PGj1@Tg029Cj3_Tg029fj1UTg00B2j1TTg00BRj1MTg00IDj1LTg00CPj1KTg00Cnj1JTg00DYj24Tg00Fej2FTg003mj28Tg00GGj2ETg00H3j3HTg00HRj4ITg00:VR0j20Tg02:Dj3DTg000\j69Tg00@Ej2BTg00;2j2<Tg00@mj3NTg00AQj2OTg00J@j3PTg00Jcj4?Tg00P5j7QTg00;Nj2RTg02:gj3STg02;Sj3^Tg01i4R1j2]Tg01Foj4VTg02<@j4WTg01^6j3XTg01^[j3YTg00Nmj7ZTg01J@l<[Tg006gR2f1R3g00Q=f0R4C?p=;P3g00QdR5g00RCR6P6g00RcR7P4g00SCFZp=7g009XP2P1g01<kP0g01l8f5f4f3f2R0P3P4M<[p=\g004GR1#2R8#3R9#=R:#CP2%28#2#2#2R;#=R<A`:<4R='1%31#3#3#3#6R1,G<R>,1<R?':R@11:3RA9524X42RBP211:4RC1:4?=52AX42P2P11:A4=52AX42P2%68R8%69R9'>RA,ACPB%@49_CA%U9,:Cg00TeRA#TRB%MARA%L2RD%K2RE%J2RFg00=oRG,42RH1429RI';'71FF7RJP4P0g004lRKg00:6RL'81E40=5KLdAH2G3CIRLb1b2b310G9P4b09DC9E9P?%6;R;,B81<G8R?10G;1>8;RK,<G[R0[10G8RMg00ScRNAN8;3UW510GK\N^5MP3g00T?1OG8'8P?eO1P0PBPAPDPEPFP5P6P6P71421R7,;H,7FP2P7g00UQ1428=P2<C?,7FFQPJPLb1b2b310G11<1K'RP4b0b6b7b69S<1E9A^:<4,1<P:P<P41]:<109;R1P:P91829P<P;182;E\PBPAPDPE142;,;I,7FPJPLb1b2b3P1P4b0CVCWE9A52@CeAX<=>,1<AY<=>E9W8o"). Qed.

Lemma regamt32_mask : ltac2:(zQ "90!h9!hq7!vd!hga!kte!hi5!u7!jc!knb>1b@1$7@1$0#k0@3$2$3@2$1@1$0#i0@3$8@1$0#i0@1$4^1@2$6@1$0#i0+hf@2$5@2$1@1$0#k0^1+i0").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##5Yh06__sat1h11zh22Hah37__arithh44__ffh58__varmaph65__with7!s\%0h81bp;1p;2p;3p;4p;6p;7g001:j10Tg002Dj1@!s/$bj1STg02Noj1ITg007Ej27Tg001_j11Tg005Lj16Tg01<Ej2RTg00>hj29Tg006Gj24Tg009>j33Tg00gXj2C!s\$jj2?Tg00@Ej2ETg00;2j2;!s8$mj3DTg00AQj2WTg003mj2>Tg00B2j1V!s/$Rj1UTg00IDj1TTg00CPj1Q!s/$nj1NTg00DYj2:Tg00J@j3ATg00Fej2LTg00GGj2KTg00H3j3J!s/$Rj4HTg00bmj2BTg02QPj4M!s/$jj6GTg01]Zj4OTg02RRj1PTg000\j68Tg029fj1F!t:$cj4=Tg02:Dj3`Tg00P5j7_!uW$Nj2^!sA$gj3]Tg02S`j1\Tg01^6j3Y!s/$[j3XTg00:Vj2ZTg00Nmj7[Tg00=oR0f0R1'Zp=2g006gR2f1R3g00UQP1C=p=<P3g00QdR4g00RCR5P5g00RcR6P1g00SCF[p=5g004GR7#0R8#0!s$%R9#0#@R:#SP2%@9R;%I1R<'7R=%17R7#1!s$$6R>,R;R?,7;R@'917:3RA%69R9'4RB9321X12RCP217:1R:,C;RD191@=32BX12P2P>1C;A/91!s8+%68RA%18R8#6RE'?RF,4DPCP21?A9RC,4:RG141F!sW+14:914GFPFPCP:1EAE1;0ARG%2ERB1;0FRH[RI[%2ARJg00ScRKADAE3UW2%2F\K^2J!vC$T?1W0A'>PGeO1RLPIg00TeRI#VRM%UIRI%T2RN%Q2RO%N2RP1:20RQ1:2ARR%@85A2'<'51LP6R8P1f2RSg004l!{f$:6RU'>1K1S=3TUdAJ203CHRUb4b5b6PHP1b3b0b7b01EA9RH%291;0CR0[RT\GRGADA93VKX2JR9%2C!u'$RJPLPTPMPIPNPOAA2R;RR,<Q,5PP8P!t%'0!t%,P21B1F932CX12%0!x2%6,?ARA1BAF,>2CMEGCOPD%P:E8%FE,9D!t-'P2PQg00Q=R:1:2EC=!t51BP1b39`DEE8P@PHPGP9P!tn0PPP4P5P5P6P2PQP:1:2>R2!sm$1<2R,5PF_!sv,%2>1;>C'^!u4,9];>E8P=%\1E8AY;<?,7;AX;<?E8W8o"). Qed.

(* [comment removed for export] *)
Lemma sext32_unsigned : ltac2:(zQ "80!h9!hq7!vd!hga!jj4!jc!hod!hj6>1v@1$5@1$0#i0@3$2$3@2$1@1$0#k0@3$4@1$0#i0@1$0#k0^1@2$7@1$0#k0@2$6@1$0#i0@2$1@1$0#i0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01vh11zp;1p;2p;3p;6g001:j10Tg002Dj15Tg002bj1<Tg01;]j26Tg00gXj22Tg007Ej21Tg00l4j24Tg009>j33Tg003mj2;Tg01?Nj3:Tg01@;j37Tg000\j68Tg019mj39Tg004G#0#0#0#0#0R0#5R1#<g006gR2%00#5R0f0R3,61'2f1,11,41,209323X121113,41,20R4,;2A:103,10A7103E8A9103,10=324eW0o"). Qed.

Lemma w_addiw : ltac2:(zQ "90!h9!jc!jj4!vd!jv3!ku6!kte!kue!hpb>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$3@1$1@1$0#k0@3$2@1$0#i0@1$0#k0@3$5$4@1$6^2@3$2@1$0#c@1$0#i0^1@2$7^2@2$8@1$0#c^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##1Ah01zh12b1h22b2h31nh41Hh51ah63immp;1p;3p;2p;8p;6g001:j15Tg002Dj1:!s/$bj17Tg001_j1BTg009>j38Tg007Ej20Tg018`j3JTg02Noj1<Tg019mj39Tg02Toj3=Tg01;]j2;Tg02UWj2@Tg00l4j21Tg00gXj22j1OTg00h>j26Tg01<Ej2?Tg003mj2>Tg02V_j3NTg00mdj3MTg02X4j2ITg01?Nj3HTg01@;j3ETg02S`j1DTg014Xj3FTg01Ucj3GTg00jIj8CTg01>_j2KTg02YCj1LTg000\j6ATg006gR0f1R1f0R238p=3P0f4R3f3R4f2R5P1P2EAp=4g004GR6#5!s$'R7#5#:R8#7%B!s=%:R6#7g009XR9%72R:%71R;g00;N%75?81210451041'3R<[10511052'3%74?851[R=%73?845\<AJ512P2n20010!s#$12!s-%0W2W1W3P=^2;^1:^39P2P8%:7R7g02ZSR9%<5R:A9671R;3=R=798R<1;61R3,@5R>107=,17R?,281084R@1;65'6,17RA,?8,08,32X001085RB/63,17RC,28%<4A9675R45=9,07,17,28/!sS$P0P0%O8R9P9P?PCP0\0/>9107:R9107;R?'6,271172/3AX00127BRD1074,62,27,17!s?+3R4127@/!s?26D4R@,17RE132AX00RA16B4,17R2PAPCPA1>0CP2AN7B3D4PEAM7B4D!sr$,171I7@D4AH671,07AE671D416D?!t3'CeP9%D5D4AF7:;,07AG7:;D4GC1?8C,081K8CD4108<R<%L=!s1$>,3<eO4b4W6W5o"). Qed.

Lemma w_slliw : ltac2:(zQ "a0!h9!jc!vd!ko4!jj4!kn4!ku6!kte!kv9!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##9Zh01zh11sh21Hh32Hah46__sat1h52b1h62b2h71nh87__arithh94__ffh:!sN%0h;8__varmaph<5__with=1ap;1p;3p;2p;4p;7p;6p;8g001:j16Tg002Dj1C!s/$bj15Tg001_j1<Tg009>j3:Tg007Ej20Tg018`j3XTg02Noj1GTg027Oj3FTg02Toj3DTg019mj3JTg02[?j2ITg00l4j24Tg00gXj21j1[Tg01BLj29Tg01<Ej2ATg003mj2@Tg005Lj1?Tg01^6j3Y!s8$jj2=Tg00bmj28Tg006Gj27Tg00@Ej2WTg00;2j2>Tg00:Vj2;!sA$mj3VTg00AQj2UTg00B2j1T!s/$Rj1NTg00IDj1LTg00CPj1K!s/$nj1MTg00DYj2ETg00J@j3O!s/$cj4PTg00Nmj7QTg02\Gj6RTg00Fej2STg00GGj2iTg00H3j3h!s/$Rj4g!sS$kj4fTg02RRj1BTg02PGj1cTg02]Tj3HTg02^=j4bTg02X4j2]Tg02S`j1\Tg02_Lj1^Tg02?Ij3_Tg02@1j3`Tg00jIj8aTg01>_j2ZTg02YCj1dTg000\j6e!vP$gR0f1R1f0R23:p=2P0f4R3f3R4f2R5P1P2Eep=3g004GR6#6R7#6!s$%R8#6#CR9#5%<7#CR:#5R;g009XR<%52R=%51R>g00;NR?%55?:1210451041'2R@[10511052'2%54?:51[RA%53?:45\@AX512P2n20010!s#$12!s-%0W6W5W7PA^6>^5=^7<P2P9%C8R<g02@bR=%G5R>AF:<1RA3DR@7J9R310:1RB,I5RC10<@,4<RD,191094RE10:5RF'9RG,4<RH,A9,09,22X001095RI/9BRJ,4<RK,19%G4R4AF:<55D=,0<,4<,19/!sU$P0P0%[9R=P=PDPKP0\0/@=10<>R=%<6#<!s$$?,A<9Y<ARA,0<R6'9,1<14<2/2HX00PB10<4/92,1<,4<!s;%11<IR4192F!s<094BRD,4<12!sa%<PDPJ%?7R7/=BRH,84RL11<2RM11<G'!uH$8IHRG11<E1=7FRF'8,1</2MX00%?8R8,=7RM,7L18EF,1<RN!v#&7IM182F/7M/2N!s7$GM17EM/8!s:%!uu$IPHPM1W78g00=oRH/>7RF1;H81>HM[RE[1;H7RNg00ScROAV781UW31;HM\O^3NP1g00T?1UH7'@PFeO1PEg00TeRE#T%NE%L0%K0%M0REg00QdRFg00RCRNPNg00RcROPEPFPNPNPOP01E07=O0<g00l[1E0HCPg00SCFQER1SEOP2P5g004lROg00:6RE'@1i25=:OEdAh0H1Cgb9b;b<A:0MHg02`X[P2b8b4b:b4Cf11<G%BGD3P4%BID311<L%BLD3PJP?10:2R:,;HR?1>:81;HB%c2P1!{:7X1;P?^1;P2P5O1b2R29HIBD3PDAH4B2D3Cb11<!xW$]<DD3P=%\5D3P6%^1D3A_<>A,0<A`<>AD3Ga1A9K,091Z9KD31093R3%d@!s1$C,23eO4b2W1W=o"). Qed.

Lemma w_srliw : ltac2:(zQ "a0!h9!jc!vd!kp9!jj4!kn4!ku6!kte!lg4!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;6p;8g001:j14Tg002Dj1:Tg002bj12Tg001_j15Tg009>j39Tg007Ej20Tg018`j3ETg02Noj1=Tg027Oj3>Tg02Toj3<Tg019mj3ATg02a5j2@Tg00l4j23Tg00gXj26j1LTg00d[j28Tg01<Ej2;Tg003mj2?Tg005Lj1KTg01^6j3JTg02S`j1ITg000\j67Tg02_Lj1DTg02Cdj3FTg02DLj3CTg00jIj8GTg01>_j2HTg02YCj1BTg006gR0f1R1f0R239p=1g004GR3#4R4#4#4#4#4R5#4#:R6#2%54#:R4#2g009XR7%22R8%21R9g00;Nf2R:#2?912f3R;/0:10;1'1R<[10:110:2'1%2;?9:1[R=f4#2?9;:\<AE:12P2n2001000000120000000W2W1W3P=^29^18^37P2P6%:5R5g02E=R7%=:R8A>451R93<R=7A6R<1041R>,@:R?P0105=,35R@,66106;,65104:RA'8,35RB,;6,06,12X00P0106:,65RC/8>,35RD,66%=;R;A>45:5<7,05,35,66/12X00P0P0%L6R7P7P@PDP0\0/?7P01058R7%53#5#5#5#K,;59J59R9,05R3'81352/1BX00P0P>105;/82,35/1BX00P0PC182A,35/1BX001?0DP7%I:E7P3%D1E7AF589,05AC589E7GG1;6D,061H6DE7106<R<%B=E7106?,1<eO4b4W6W5o"). Qed.

Lemma w_sraiw : ltac2:(zQ "a0!h9!jc!vd!kqe!jj4!kn4!ku6!kte!lgf!hq7>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61sp;1p;3p;2p;8p;6g001:j15Tg002Dj1:Tg002bj14Tg001_j18Tg009>j39Tg007Ej20Tg018`j3JTg02Noj1=Tg027Oj3?Tg02Toj3<Tg019mj3BTg02b=j2ATg00l4j21Tg00gXj23j1OTg00d[j27Tg01<Ej2;Tg003mj2@Tg01;]j2>Tg005Lj1NTg01^6j3MTg02X4j2ITg02cEj1HTg02_Lj1ETg02G0j3FTg02GYj3GTg00jIj8DTg01>_j2KTg02YCj1LTg000\j6CTg006gR0f1R1f0R239p=2P0f4R3f3R4f2R5P1P2ECp=6g004GR6#5R7#5#5#5#5R8#5#:R9#4%87#:R7#4g009XR:%42R;%41R<g00;N%45?91210451041'2R=[10511052'2%44?951[R>%43?945\=AJ512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P9%:8R8g02HKR:%=5R;A?781R<3<R>7B9R=1071R3,A5R?108>,18R@,391094,181075RA'7,18RB,;9,09,22X001095,18RC/73RD,18RE,39%=4R4A?7855<:,08,18,39/22X00P0P0%O9R:P:P@PEP0\0/@:1>8;R:%86#8#8#8#N,;89M8<R<,08R6'7,381182/2BX00P31>84/72,38,18/2BX00PC172A,38,18/2BX00PE122BX001@0E138D,181I8DD6P:%H5D6P6%E1D6AF8;<,08AG8;<D6GD1;9E,091K9ED6109=R=%L>D6109?,2=eO4b4W6W5o"). Qed.

Lemma w_addw : ltac2:(zQ "80!h9!jc!kte!vd!jv3!jj4!ku6!lha>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;8p;6g001:j16Tg002Dj1>Tg002bj17Tg009>j38Tg007Ej20Tg018`j3ITg02Noj19Tg02Toj3:Tg019mj3@Tg02dRj2?Tg00l4j22Tg00gXj21j1KTg00h>j25Tg01<Ej2=Tg003mj2;Tg02V_j3JTg00mdj3HTg02X4j2ETg02S`j1<Tg014Xj3CTg01Ucj3BTg00jIj8DTg01>_j2ATg02YCj1FTg000\j6GTg006gR0f1R1f0R238p=3P0f4R3f3R4f2R5P1P2EGp=4g004G#6#6#6#6#6R6#6#>R7#7R8g009XR9%72R:%71R;g00;N%75?81210451041'3R<[10511052'3%74?851[R=%73?845\<AI512P2n2001000000120000000W2W1W3P=^2;^1:^39P2P7%>6R6g02ZSR9%95R:%91R;3:R=7@7R<1?51R3106=,26R>,171074R?1075R@'5,26RA,=7,07,32X001071RB,5@,26RC,17%94=:9:,06,26,17/32X00P0P0%K7R9P9P>PCP0\0/;9106:R9106;R>'5,161262/3AX00116@R41529,16,26/3AX00116BRD116?/52,16,26/3AX00154DR4,26R?132AX00RA15@D,26R2PAPCPA1;0CP2AJ6@BD4P?AH6@DD41164,261E64D4P>%<1D4P9%<5D4AC6:;,06AB6:;D4GD1=7C,071A7CD4107<R<%F=D41073,3<eO4b4X68W5o"). Qed.

Lemma w_subw : ltac2:(zQ "80!h9!jc!kte!vd!kg7!jj4!ku6!li4>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##2Rh01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;4p;8p;6g001:j18Tg002Dj1A!s/$bj17Tg009>j39Tg007Ej20Tg018`j3NTg02Noj1;Tg02Toj3?Tg019mj3DTg02eYj2CTg00l4j26Tg00gXj23j1PTg00iIj25Tg01<Ej2@Tg003mj2=Tg005Lj1>!s/$jj2OTg006Gj24Tg02f`j3MTg02gHj3GTg02RRj1:Tg02^=j4FTg02X4j2ETg02S`j1<Tg02h0j3H!s/$Uj3ITg00jIj8JTg01>_j2KTg02YCj1BTg000\j6L!tC$gR0f1R1f0R239p=1P0f4R3f3R4f2R5P1P2ELp=2g004G#8R6#8!s$%R7#8#AR8#7R9g009XR:%72R;%71R<g00;N%75?91210451041'1R=[10511052'1%74?951[R>%73?945\=AN512P2n20010!s#$12!s-%0W2W1W3P>^2<^1;^3:P2P8%A7R:g02iCR;%;5R<%;1R>3?R=7D8R31C51R?10:=,6:R@,381084RA1085RB'5RC,6:RD,@8,08,12X001081RE,5BRF,6:RG,38%;4=?;<,0:,6:,38/!sO$P0P0%P8R;P;P@PGP0\0/=;10:<R;10:>R@'5,3:16:2/1DX0013:BR4152;,3:,6:!s<+ERH13:A/52!s?054HRI,6:112DX00P:PIPF%>6%>7'OR7,4I13:CR6!u-&4B7RD1524/47/16!s9$E7RJ14A7RA/52!s>-F7R615AD!s9$!sd$5BJ/47RA14C7!sw%R2P6P21=06PAAMBE7D215DJ/47AGBJ7D213:F%:FD2PH%:ED2P4%:B!s=$IRB%:ID2CF16:B1E:ID2P@%<1D2P;%<5D2AH:<>,0:AI:<>D2GJ1@8G,081K8GD21083R3%B=!s1$?,13eO4b4X69W5o"). Qed.

Lemma w_sllw : ltac2:(zQ "80!h9!jc!kte!vd!ko4!jj4!ku6!lie>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##<ch01zh17__arithh24__ffh38__varmaph45__with51Hh62Hah74__p1h86__sat0h9!s/%1h:4__x1h;2b1h<2b2h=1nh>!sD%2h?1ah@1bp;1p;3p;2p;4p;6p;7p;8g001:j18Tg002Dj1J!s/$bj1;Tg009>j39Tg007Ej20Tg018`j3ZTg02Noj1@Tg02Toj3HTg019mj3RTg02ioj2OTg00l4j25Tg00gXj21j1\Tg005Lj1FTg006Gj24Tg01BLj27Tg01<Ej2CTg003mj2ATg001_j1=Tg01^6j3XTg00B2j1W!s/$Rj1VTg00IDj1UTg00CPj1T!s/$nj1STg00DYj2DTg00Jcj4ETg00Fej2QTg00GGj2PTg00H3j3N!s/$Rj4MTg00;2j2<Tg02LQj3L!s8$NR0j2G!u5$jj2?Tg00bmj2:Tg02M8j2KTg00@Ej2r!s/$mj3qTg00AQj2p!tN$@j3oTg02\Gj6n!s/$kj4eTg02RRj1B!u+$2j2bTg00E<j2^Tg00OQj6]Tg00P5j7_!sA$_j1`!s8$Yj8aTg02]Tj3ITg02^=j4[Tg02X4j2cTg02S`j1dTg02k6j1YTg02?Ij3fTg02@1j3gTg00jIj8hTg01>_j2iTg02YCj1jTg00Nmj7kTg00:Vj2lTg000\j6m!x%$gR1f1R2f0R339p=2P2g00QdR4g00RCR5P5g00RcR6P3g00SCFkp=>g00=oR7/l3p=6P1f4R8f3R9f2R:P2P3Emp=3g004GR;#8R<#8!s$%R=#8#JR>#;R?g009XR@%;3RA%;2RBP0%;:?923109:1092'2R0[10:210:3'2%;9?9:2[RC%;8?99:\0AZ:23P3n20010!s#$12!s-%0W<W;W=PC^<B^;A^=@P3P>%J=R@g02@bRA%@:RB%@2RC3HR07R>RD1O:2RE10@0,5@RF,1>10>9RG10>:RH%F=R='4RI'7RJ,5@RK,C>,0>,23X0110>2RL/4=RM,7HRN,5@RO,1>%@9RP=HAB,0@,5@,1>/!sV$P1P1%\>RAPAPFPOP1\1/AA10@BRA%=;#=!s$$F,C@9X@CRC,0@RF'7,1@15@3/2KX01PM10@P/73,1@,5@!s;%11@HRP173I!s<07PMRP,5@123!sa$@PPPNg00TeRN#WRK%VNRN%U1RQ%T1RR%S1RSP11D17RTg00UQ1D1=CE'>1QS6RUP3P:g004lRVg00:6RW'A1P3:=9VWdAN172CMRWb2b3b41<7=P3b19LL=%6M1<M='G11@GRM%F<R</?IRL':RV11@3RX10>8R814G=RY!ug$'2X011:GLRZ11@81?<YRY':,1@/2XX011?<=RX,4V1:8Y,1@R[!wY&4GX1:3Y/4X/2[!s7$ZX148X/:!s:%!wN$GPLPX1KH=RL%6H%6=RH148=R8#6[[RY1r<=1<7<R[1<7X\HRH[%6<R\g00ScR]Aq<=2UW6%6X\]^6\!|L$T?1p7<'AP[eO1PHPKPNPQPRPSP4P5P5P6!vw$<=o1@g00l[PTCE,>SEnPUP!vR&A91X7g02`X[P3b1b9b8b9b>Ce11@Z%BZD3PM%BGD311@V%BVD3PJPLPYp-0RYPKPN1b12!tA0!tK-PTg00Q=1^1;!tG$R;!sD-9E]F_%`5P;Ga!t^,X:1W7%63/G2%62[^:1^7YP31<8=P8P:O3b1b8R89IGID317MIAIMI8D3b5C[11@!z8$c@PD3PA%d:D3PF%Y2D3Af@BC,0@Ag@BCD3Gh1C>O,0>1i>OD310>DRD%j0!s1$E,2DeO4b5X@?W?o"). Qed.

Lemma w_srlw : ltac2:(zQ "80!h9!jc!kte!vd!kp9!jj4!ku6!lj8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##/}h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6p;8g001:j13Tg002Dj1>!s/$bj14Tg009>j38Tg007Ej20Tg018`j3KTg02Noj1;Tg02Toj3=Tg019mj3BTg02lDj2ATg00l4j22Tg00gXj27j1LTg005Lj1@Tg006Gj2?Tg00d[j26Tg01<Ej2:Tg003mj2<Tg001_j19Tg01^6j3JTg02S`j1ITg000\j65Tg02k6j1ETg02Cdj3DTg02DLj3CTg00jIj8FTg01>_j2GTg02YCj1H!tL$gR0f1R1f0R238p=1g004GR3#!s$+R4#3#>R5#4R6g009XR7%42R8%41R9g00;Nf2R:#4?812f3R;/0:10;1'1R<[10:110:2'1%4;?8:1[R=f4#4?8;:\<AK:12P2n20010!s#$12!s-%0W2W1W3P=^29^18^37P2P5%>4R7g02E=R8%;:R9%;1R=3=R<7B5R>1A:1R?P0107<,27R@,75105;,77105:RA%@4R4'?RB'6,27RC,:5,05,12X00P0177ARA1051/?4R4!sJ%D,75%;;R;==89,07,27,75/!sY&P0%L5R8P8P@PDP0\0/<8!tN$9R8%93#9!s$$@,:79J7=R=,07R3'61272/1C!si%4107;/62,27!s:+A162B!s7+1<0DP8%I:E5P3%E1E5AD79=,07AC79=E5GF1:5D,051G5DE5105>R>%H<!s1$?,1>eO4b4X66W5o"). Qed.

Lemma w_sraw : ltac2:(zQ "80!h9!jc!kte!vd!kqe!jj4!ku6!lk2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;8p;6g001:j15Tg002Dj1=Tg002bj14Tg009>j38Tg007Ej20Tg018`j3NTg02Noj1:Tg02Toj3?Tg019mj3DTg02mKj2CTg00l4j21Tg00gXj23j1OTg005Lj1ATg006Gj2@Tg00d[j27Tg01<Ej2;Tg003mj2>Tg01;]j2<Tg001_j19Tg01^6j3MTg02X4j2GTg02cEj1FTg02k6j1ETg02G0j3HTg02GYj3ITg00jIj8JTg01>_j2KTg02YCj1LTg000\j6BTg006gR0f1R1f0R238p=2P0f4R3f3R4f2R5P1P2EBp=6g004GR6#5#5#5#5#5R7#5#=R8#4R9g009XR:%42R;%41R<g00;N%45?81210451041'2R=[10511052'2%44?851[R>%43?845\=AN512P2n2001000000120000000W2W1W3P>^2<^1;^3:P2P8%=7R:g02HKR;%:5R<%:1R>3?R=7D8R31C51R?10:=,1:R@,381084,1:1085RA%A7R7'@RB'7,1:RC,;8,08,22X0011:ARA1081/@7R7'7RD,1:RE,38%:4R4=?;<,0:,1:,38/22X00P0P0%O8R;P;P@PEP0\0/>;1<:<R;%96#9#9#9#A,;:9M:>R>,0:R6'7,3:11:2/2CX00P71<:4/72,3:,1:/2CX00PA172B,3:,1:/2CX00PE122CX001>0E13:D,1:1G:DD6P;%F5D6P6%E1D6AH:<>,0:AI:<>D6GJ1;8E,081K8ED61083R3%L=D6108?,23eO4b4X69W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_mul : ltac2:(zQ "60!h9!jc!vd!lkc!ll5!llf>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg02nRj21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulh : ltac2:(zQ "60!h9!jc!vd!lm8!ll5!ln2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg02oXj21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulhsu : ltac2:(zQ "60!h9!jc!vd!lnc!ll5!lo8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg030_j21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_mulhu : ltac2:(zQ "60!h9!jc!vd!lp4!ll5!lpf>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg031hj21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_div : ltac2:(zQ "60!h9!jc!vd!lqa!ll5!lr3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg0330j21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma m_rem : ltac2:(zQ "60!h9!jc!vd!lrc!ll5!ls5>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##$0h01ah11bp;1p;2g001:j10Tg002Dj14!s/$bj12Tg0346j21Tg003mj23Tg004G#0!s$-4#2R0f1f0'1,30X10W0o"). Qed.

Lemma w_mulw : ltac2:(zQ "80!h9!jc!kte!vd!lkc!jj4!ll5!lse>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##7~h01zh12Hah26__sat1h32b1h42b2h51nh61Hh77__arithh84__ffh9!sR%0h:8__varmaph;5__with<1ah=1bp;1p;3p;2p;4p;7p;6p;8g001:j19Tg002Dj1C!s/$bj17Tg009>j38Tg007Ej20Tg018`j3XTg02Noj1<Tg035<j4?Tg019mj3K!s8$fj2HTg00l4j26Tg00gXj23j1`Tg00bmj25Tg01<Ej2DTg003mj2:Tg005Lj1A!s/$jj2YTg006Gj24Tg00@Ej2WTg00;2j2@Tg00:Vj2=!sA$mj3VTg00AQj2UTg00B2j1R!s/$Rj1QTg00IDj1NTg00CPj1J!s/$nj1ITg00DYj2>Tg00J@j3G!s/$cj4LTg00Nmj7MTg02\Gj6FTg00Fej2OTg00GGj2PTg00H3j3E!s/$Rj4STg036mj4T!s\$kj4cTg02RRj1;Tg02^=j4bTg02X4j2aTg02S`j1BTg037Vj3_Tg038;j3]Tg00jIj8\Tg01>_j2[Tg02YCj1ZTg000\j6^!v>$gR0f1R1f0R238p=1P0f4R3f3R4f2R5P1P2E^p=2g004G#9R6#9!s$%R7#9#CR8#7R9g009XR:%72R;%71R<g00;N%75?81210451041'1R=[10511052'1%74?851[R>%73?845\=AX512P2n20010!s#$12!s-%0W4W3W5P>^4<^3;^5:P2P8%C7R:P:g038iR;%<5R<%<1R>C?R=7K8R31H51R?10:=,6:R@,381084RA1085RB'5RC,6:RD,D8,08,12X001081RE,5BRF,6:RG,38P:P;%<4P<C?,0:,6:,38/!sS$P0P0%`8R4P4P@PGP0\0/:410:<R410:>R@'5,3:16:2/1DX0013:BR;1524,3:,6:!s<+ERH13:A/52!s?05;HRI,6:112DX00P:PIPF%A6R6%A7R7'YRD,4I13:CRJ!u6&4BDRK152;/4D/1J!s9$EDRL14ADRA/52!s>-FDRJ15AK!s9$!sd$5BL/4DRA14CD!sw%RCPJPC1:0JPAPBPEPD1W67g00=oRA/@6RJ1=A71@AD[RC[1=A6RMg00ScRNAV671UW11=AD\N^1MP1g00T?1UA6':PJeO1PCg00TeRC#R%QC%N0%J0%I0RCg00QdRJg00RCRMPMg00RcRNPCPJPMPMPNP01>06=G0:g00l[1>0ACLg00SCFMEF1OCNP2P5g004lRNg00:6RC':1P25=8NCdAE0A1CSb8b:b;A80DAg02`X[P2b7b2b9b2R2CTD215KL/4DPBPLPDP2CcD213:F%;FD2PH%;ED2P;%;B!s=$IRB%;ID2Cb16:B1a:ID2P@%B1D2P4%B5D2A_:<>,0:A]:<>D2G\1D8G,081[8GD21083R3%Z=!s1$?,13eO4b6X=9W<o"). Qed.

(* [comment removed for export] *)
Lemma div0_32 : ltac2:(zQ "80!h9!il1!hq7!o7!vd!kte!jc!hj6>1b@1$6@1$0#k0@3$4$3@2$1@2$2@1$0#i0@1$5^1Z@2$1@2$7@1$0#i0@2$2@1$0#k0^1Z").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01bh11zp;1p;2p;3p;6g001:j10Tg002Dj13Tg002bj19Tg007Ej21Tg00gXj24Tg039Uj22Tg009>j3:Tg003mj28Tg02Noj17Tg02S`j16Tg000\j65Tg004G#0#0#0#0#0R0#0#3R1#9g006gR2%30R0f0R3,11'4R4g004lR5g00=oR6,23f1,11,40/263:X121246,85%73,10%63E5W0o"). Qed.

Lemma w_divw : ltac2:(zQ "80!h9!jc!kte!vd!lqa!jj4!ll5!lt8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##32p'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;8p;6p;4g001:j18Tg002Dj1B!s/$bj13Tg007Ej20Tg00gXj26j1LTg039Uj2=Tg03:2j1KTg01<Ej2:Tg02Noj1;!sA$Pj3<Tg019mj39Tg00l4j21Tg03;7j27Tg009>j34Tg018`j3MTg003mj2>Tg01;]j2ATg02cEj1?Tg02X4j2J!se$Uj3GTg00jIj8FTg01>_j2ETg02YCj1DTg03<Ej1HTg000\j6@Tg035<j4CTg03=Mj2ITg006gR0f1R1f0R234p=2P0f4R3f3R4f2R5P1P2E@p=5g004GR6#8!s$'R7#8#BR8#3R9g004lR:%B7R71082'6g00=oR;'=R<P:%37R=P2%K6R6,:7R>%;5R?%;1R@5<7n01101000200009978P:P91081RA,67/=;1:86R61085,17RB117A'7,17,:8n!s`$!sc'549X2:P<P:!s$$=P2P>%;4R==<7?R<!t89P2P61084,17R:/7B,17RA,:8RC!t'4P2g009XRD%32RE%31RFg00;N%35?41210451041'2RG[10511052'2%34?451[RH%33?445\GAM512P2n20!t1'1!t2$000W4W3W5RGPH^4F^3E^5DRDP2P8A978>!ty$6,>0O4b1PGP!s@+<RDPC107<RG,17R6,681083,17R>/7:,17RE,:8,08,22X00168A%;3=<7=,0!vk$68/!s@$P0P0%L8R3P3P6PAP0\0/>31A7=R31A7?R6'7RF,67RH1172/2EX00117F12!s1$P:1723,17!s@%PB17>2!s5+1>0AP6%?5D5P3%?4D5117H1J7FD5PGAG7=?D5GF108C1E8AD5108D%D<D5O4b1!x0$!wX'1b7%;2R<,07/=;%H2E@P7g03>TP@P<CC99781I12549eX29W6o"). Qed.

Lemma w_remw : ltac2:(zQ "80!h9!jc!kte!vd!lrc!jj4!ll5!lu2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##4Ip'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;8p;6p;4g001:j19Tg002Dj1E!s/$bj16Tg007Ej20Tg00gXj22j1KTg039Uj2=Tg02Noj1;Tg03?@j3<Tg019mj3:Tg00l4j21Tg01<Ej27!sJ$fj28Tg009>j35Tg018`j3MTg003mj2>Tg02X4j2CTg02S`j1LTg01>_j2BTg02YCj1ATg01;]j2@Tg02cEj1?Tg03@Cj3ITg00jIj8HTg03<Ej1GTg000\j6DTg035<j4FTg03A2j2JTg006gR0f1R1f0R235p=3P0f4R3f3R4f2R5P1P2EDp=4g004G#9!s$'R6#9#ER7#6R8g004lR9%E6R61072'2g00=oR:'=R;P9%66R<P2%;5R=%;1R>9<6=n01101000200009:67P9P81071R?,26/=:1075,16R@,77116?,8@,16,77n!s^$!sa'558X29P;P9!s$$!t7$4R<A<6<=R;!t59P21074R9,16R?,77RA18?@,16RB,77RC!t04P2g009XRD%62RE%61RFg00;N%65?51210451041'3RG[10511052'3%64?551[RH%63?545\GAM512P2n20!t1'1!t2$000W4W3W5RGPH^4F^3E^5DRDP2P7A:67<REPA106<RF,16,271073,16RH,77,07,32X00127?RI%;3R3,06!sO%/!s@&69RJ1162RK,27127HRL'3X00P?1272/3LX001>0I116J1C69D4PF%L4D4107A1B7?!s0$E%A<D4O4b1PGP!tl+;RDPC106;RG,16RE,2718H?,16RA!tn2BA<63<!tl2P0P0%K7R3P3PEPBP0\0/>31@6<R31@6=RE'8RF,26R913KAX00116F132A!u7%823,16/3!s5$@18H2!s5+1>0BPE%?5D4P3%?4D411691C6FD4PGAI6<=D4GH107C1B7B!u[$D%A;!u[%!yU$!xw%101b7%;2R;,06/=:%G2EDP6g03B9P>P;CF9:671J12558eX28W6o"). Qed.

Lemma w_divuw : ltac2:(zQ "80!h9!jc!kte!vd!luc!jj4!ll5!lv6>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##0op'0h01Hh11bi001bh22b1h32b2h41nh51zh61ah72b0i014div0p;1p;2p;3p;6p;4g001:j14Tg002Dj1>!s/$bj13Tg007Ej20Tg00gXj22Tg039Uj2<Tg03:2j1?Tg01<Ej27Tg02Noj16Tg03Bej3:Tg019mj35Tg00[Wj29Tg00l4j28Tg009>j31Tg018`j3ETg003mj2=Tg01>_j2DTg000\j6;Tg02YCj1CTg03<Ej1@Tg035<j4ATg03CKj2BTg004GR0#4!s$'R1#4#>R2#3R3g004lR4%>1R1f0R5,02'2g00=oR6'<R7P4%31R8P5%?0R0,71R9f2R:#6R;f1R<#6R=5:1n01101000200009512P4P3102<,21R>/<61720R0102:,21R?/9>,81,72n!s]$!s`'513X14P7P4!s$$8P5P9f3R8#6R7=:1;R;!t89P5P01028,21R4/9?,81R?,72R>!t-4P5g009XR@%35RA%3<RBg00;N%3:?1<5g006gRC108:108<31RD[10:<10:551C%38?1:<[REf4RF#3?18:\DAE:<5P5n20!t<'1!t=$000W3W2W4R:PE^3B^2A^4@R@P5P2A5129!u+$0,=CO4b0P:P!s@+;R@P>PC101;,81,22102F,21/94!vV%,0291C5X5CPC122?R4%6F=:17,01!sX%=!sE%1=C4102>1D2?E;102@%C;E;O4b0!vj$!v:'1b7%65R;,01/<6%@5E;P1g03DSP=P;CA95121B<5513eX13W6o"). Qed.

Lemma w_remuw : ltac2:(zQ "80!h9!jc!kte!vd!mg1!jj4!ll5!mgb>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##2Sp'0h01zh11Hh21bi001bh32b1h42b2h51nh61ah72b0i014div0p;1p;2p;3p;6p;4g001:j18Tg002Dj1B!s/$bj15Tg007Ej20Tg00gXj21Tg039Uj2<Tg02Noj1:Tg03E?j3=Tg019mj39Tg00l4j22Tg01<Ej26Tg006Gj2;Tg009>j34Tg018`j3HTg003mj2ATg02X4j2GTg02S`j1FTg01>_j2?Tg02YCj1>Tg03<Ej1ETg000\j6@Tg035<j4D!tU$ej2C!t:$gR0f1R1f0R234p=3P0f4R3f3R4f2R5P1P2E@p=7g004G#8!s$'R6#8#BR7#5R8g004lR9%B6R61072'1g00=oR:'<R;P9%56R<P2%:5R=%:1R>9=6=n01101000200009967P9P81071,16R?/<:1075R@,26,67116@R@/;?!s5%n!s`$!sc'548X29P;P9!s$$!t9$4R<A=6<=R!t7:P21074R9,26R;,67R?1169RA/;@,26R@,67RB!t54P2g009XRC%52RD%51REg00;N%55?41210451041'3RF[10511052'3%54?451[RG%53?445\FAH512P2n20!t1'1!t2$000W4W3W5R5PG^4E^3D^5CRCP2P7A967<RDP?106<RE,26,171073RG,26RF,67,07,32X00117;RH%:3R3,06!sQ%/!s@$PA1262,17117FRF'3X00P;1172/3FX001A0H126A1G69D7PE%F4D7107?1?7;!s0$D%><D7O4b1P5P!th+=RCPB106=!tf&16G/;A!wu%!te/@RAA=63<!te21A0A107B1?7@!t4$C%>=!t4%!x/$!wL%101b7%:2R=,06/<:%E2E@P6g03FmP>P=CD99671C12548eX28W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_swrap_hi : ltac2:(zQ "b0!vd!hp8!hga!mh6!mi3!jj0!hk0!hl4!hr5!mi9!hod>1n$1>1z$2>0@1$4@3$0$1^2$5>0@2$6@1$9^3^2>0@2$7^3@1$3^4@3$0$2@2$a^5^4@2$8^4@1$3^5").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##8,h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71zh81Hh93Hhih:3Hloh;2Hnh<4Hposh=3Htwh>1np;3p;1p;2p;4p;7p;6p;8g009>j3@Tg03GYj1hTg00h[j16Tg00:Vj2<Tg01C_j14Tg00;2j27Tg03H2j2X!sS$>j21!s8$fj1RTg00B2j1L!s/$Rj1KTg00C2j2ETg00W9j4g!s8$Pj1e!s/$nj1_Tg00E<j2BTg001:j1ZTg00ifj3A!s8$_j1WTg01KLj3?Tg005Lj1VTg00DYj2FTg00bJj3UTg00Fej2TTg003mj2STg00GGj2QTg00H3j3P!s/$Rj4M!t1$Ij20!se$mj2CTg006Gj2=Tg03:2j1NTg00]>j2OTg00^ij19Tg00_Hj28Tg03ISj3JTg00`Zj2ITg01ITj2fTg00aFj3H!uN$_j1dTg00Jcj4;Tg00P5j7^!vk$Nj2]Tg029Cj3\Tg000\j6GTg03J<j3[Tg00kXj6`Tg00l4j2aTg00Nmj7b!tC$1j3Y!sw$Yj8c!u3$gR0f1R1f0R23@p=2P0P1g00l[P2C;p=>!s4$QdR3g00RCR4P4g00RcR5P2g00SCFbp=3AY012p=5!sc&UQ!sc%Df3R6P3P4P4P5f2R7P1P2Gcp=:g009XR8g01A19@81#h%67/<1%46,77f4R8/X7%68R9/19%48R9'2f5R:#Rg00=oR;%4:'7g00TeR<#LR=%K<R>P01E07P11E06CgR?%e0R@%_0RAg004GRB,B0RC%Z!s-$D5A0RE%W!s3$F5?0RG%VBRH,F0=U0F5A0/>E'31TA5REP2P7g004lRIg00:6RJ'S1Q27=@IJdAP0;1CMRJb4b5b6X00X10X201121RI/07RK1CH7'1/2I^00^10^20P2f7RI#4RL%6IRMf6RNO3b3%6N,1:RO%4NRP'01CHP'1/2OP011NMRM/0LRO1CHL'1RPf8RQ#4RR,=2%6QRQ'010IRRS'2X70P01=OLRT102Q/2SX70RSP0POPSP=P>P?P@A?0GDA?0CF'>,3APEP!u840K11027'2!u--PRPQPIO3b3PT%NB,O0g00fMRB#9RT#9#9RK,80R15J0RS180TRT180BRB'5'5g00flRU'I%9!sL$K/5S151T,5K,5B/IU'f=H<=5H<!tr%PA1F0;R@/DF,3A%d4R?PAAA0DD/>F,3AP?PA1DC!s1'P0PDg00Q=RDPCC;!s<'!zA&P0P@PDPG!s?$1DGF,3AF^C:!s$%!uv77;71177/2617781<86118:/0NRJ,<;17JN'][[[[!v=4P7P6P8P:O7b39\OLEG1=PLA[OHLEGPMP2E`b8b<b=1a861069'2eW9W:W;X70W>o"). Qed.

Lemma b_lui : ltac2:(zQ "90!h9!jc!vd!jj4!mjb!ik7!u7!mk4!hpb>3imm@1$1@1$0#h4@3$2@1$1@1$0#k0@3$3@1$0#i0@1$0#k0@5$7@1$0#i0@1$0#h4@1$0#c^1@2$6@1$0#cZ@1$4@2$5@2$8@1$0#h4^1+c").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP1"] "##RYp'0h06__sat1h1!s/%3h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with91zh:4__p1h;!sM%5h<!s/%7h=!s/%2h>!s/%4h?!s/%6h@1HhA1xhB2H0hC2b1hD2b2hE1ni001nhF3HgehG3HlthH2HrhI1ehJ3immhK1ohL1yp%0p&0p;1p;3p;2p;5p;6p;4p;8p;7p;<g001:j1ETg001_j1<Tg002Dj1C!s/$bj1FTg009>j3=Tg007Ej20Tg018`j3uTg01<Ej2TTg03Jaj5XTg019mj3kTg01;]j2WTg005Lj1>Tg01BLj2BTg03KIk10!sx$l4j24Tg00gXj2Sk100Tg003mj2:!t,$kR0j1_Tg00V8j2Q!sl$lj2xTg01C_j1`Tg00;2j23!s/$NR1j2?!tC$jj2@Tg00bmj26Tg03LOj2oTg00:VR2j27Tg00?FR3j2mTg00@Ej2G!s/$mj3HTg00AQj2jTg00B2j1i!s/$Rj1hTg00C2j2g!s/$Pj1f!s/$nk10!tH$E<k20>Tg00DYj2UTg00J@j3L!sB$_k10!w+$OQk60;Tg03M4j2eTg00Fek20!v'$GGk20!uH$H3k302!s0$Rj4~!sV$Wj1bTg03N4j3VTg00_Hj2PTg00^ij1aTg00`1j3N!s/$Zj2OTg01ITj2zTg00\Uj2yTg00edj3^Tg00aFj3M!vI$Jj3]Tg00iIj2ITg01KLj3\!u8$cj4R!tC$aj2wTg03GYj1ZTg03O@j5cTg00IDj1vTg02]Tj3YTg01FQj1t!s/$oj4|Tg03PLj1}Tg02:gj3rTg000\j6d!sA$mk201Tg03QJj6qTg00jIj8pTg01>_k205Tg02YCk106Tg00Nmk70!x4$P5k708!s0$Yj8nTg00kXk609Tg01M7m<0!yc$J@l<lTf0R4#E#Ep=Ag006gR5f1R6;=4p=2g00=oR7/74p=11374p=DP5P6g00UQP4CRp=J!s4$QdR8g00RCR9P9g00RcR:P4g00SCK07p=5!s\&Q=!s\%;f2R;P8P9P9P:P6P4K08p=Kf3R<!s<+;P6P4Gnp=9P5f4R=P<!s9%Edp=8g009XR>P;P6g018Dg01A1R?P4J09p=[P>P5!s$$0P0f5R0P!sd+N<0:p={!sC$2P0P2P=P7P7!sE'M<lp=sg004GR2#ER@#<#ARA#CRB#F%F4RC%F6RDP1%F;?=6410<;10<6'2R1[10;610;4'2%F<?=;6[RE%F=?=<;\1Au;64P4n20010!s#$12!s-%0WDWCXE>PE^DD^CC^E>P4%E@RC#E#ARD#ERE#CR1%CDRFPFPB%<2RG#ARH#CRIP61TI7RJDXRK7k1S001WB6%>HRH'BRL$0=S0110FKS02,4FRM,S11WB;/BHRN,T1,01,24X951S1LPFPBPIP;PJDX,0F,4F,S1/!sE$P5P5&001ROPOPMPLP5\5/:O10B6RO%_IRM'BRP10IJS03'Q14F4RQ/2NX95RRP5P710B;RS/BMS04/Q4,4F!sD%PPPR1xB6%1O%`BS05,3O'?%>@R@/@MRO,6S10B<RR,4B/BH,2QX9514BSRQ1@@HRN'616RO!sv$4X95%<C#<RC#>RO,@@RT,oS13ST17TS'mP313RT17TR10B=RR/6N,4F14BR/6N'2P4!sE$0B0R0/6NR3f6,0BRU,4B/6N!vF%S06P016UNRU164NRV'2X951:5314B0S07%>ARA,G@RW%D@RX%1A1@@ARY#D[RZ[R[%1@R\g00ScR]AH@A6UW3RA%1Y\]^3\R^1G@OR_%1O%DT[R`\XRaAH@O6V]X3\RO%1T!sO%b!|a$T?1j7@':PXeRcO1RdP`P=PcO1R=PZp-0Reg00TeRf#iRg%hfRh1g56Ri%f5Rj&0?5Rk20>52R21U5@Rl%CC5L5RC'J,5kRm&0<9RnPk1U57Ro/;2,5kPk!}[+<J0;S085KkS09Pn1e5C!sJ%=KkmC9C9204k:R:P4P;g004lR<g00:6R9':2034;==<9dB02576C~R9b5b7b8X25W:134TR<%16/?;R8%bT/7;13;T'?[[^25^:eP4f<,0BRp/3YPpf7Rqf:RrO4b4b1b0b6b0b=b19VB0D814F3S0:1G@HRs%1HS0;%DNS0<[Rt\XRuAH@H!w$&v%1N!w$%wPWP[PAP^%<G#<#<RG#>Rx,G@S0=%1x1@@xRy#D[Rz\XS0>AH@x!sj%S0?%1y!sk$S0@P_PaPOPbP!wb%zPq!wf$xPZPr!s0$cPtg00fMR{,P5R|%a{S0A#a,P5R{9N5|g00flR}'O'zR~%AE#A#A#>,y5RE=^5{=N5|/O}=Mfg5MfPhPiPjPkPmPnPkQ09Pn%CG9L5lRG,e5AL5lIRm9]52R{';,5k1J{G,5k5KkC9C9P:P!wL,X:e%by16;NR;'713;y'?\8\<!wF+B,0BR</3YP<f=S09f@S0B!wH$<b;!wL/b>b;b?b<9VF3D8WGP4O117TR%`FRR,I3Q06Q05,I01IUR/2VX95PsPuPvPw%>DRD,G@RR%1D1@@DRU#D[R8\XRXAH@D!w}&D%1U!w}%\!w}'!w?2ZPxP8PcPtPg!vC&!v+$FR@9\5{g00l[AL5lBRl9\52=]5mCR,5k!v001IVU1I4Y/6N'2^25P4P<O1!uf=Q07PBP0A=>B?R0P>PeP4g02`XRVP]n01!#8Z$!#8c&XI>R]=[B4PV1wV4R;bBW@%Z0e!uH<!u@'k1;C2,5kRCPnPC!x5217T4R017T6[!u%%pPqO2!|51!t0EQ081J2l,5kRl5KkR2PnPl!yG5134Y,?6Rl136Y!}`+%1pPpPrO3!tD1DcD8Q0:PFP3A=>F?R?A[F]4PVP!uq&?e!xu'!to'Q0=Q0>Q0?Q!|h6xPZPcPtAMf~!u-+PCPn1;G{,5k!v6366NRN,7y\0!x9&Q09!v7$!x<:!tZ+RPXPDP!z#DQ0A,P59^5E!}Z-!tf+2Pn1J{@!tf5!vd$NU\l!v\,<P<Q0B!v]$!tj:DcD8WFP4O1!#?J,2!yw$!s'$bK1BQH!u$+d!xI%%v5RZPj1U5H,;o!{T0Q0;P4b4!t8%R^9YQHD8Q04%1M!sA$XA5RQ1764#tXL5XA51:57PMPHPQPQ%_4,:5XA>PIPH1:5HE{EsP^C|9YSMD8bH14FP/2Le1QP7%}PD8Q03!v}+d!}Z&ZPj1;oo,5k1Jom!#4S$!to,1777Q0<'?!tu,9rI7EdQ02PBPFPIP6PJ201BI,:>EqD8Gp1T1L,012051LD8Q00,01RL&06KD8Q0!#AD$LeO4b@WJo"). Qed.

Lemma b_auipc : ltac2:(zQ "a0!h9!jc!vd!jj4!ml0!ik7!u7!jq9!mk4!hpb>1p@1$1@1$0#k0>3imm@1$1@1$0#h4@3$2@1$1@1$0#k0@3$7@1$0#k0^2@3$3@1$0#i0@1$0#k0@5$8@1$0#i0@1$0#h4@1$0#c^1@2$6@1$0#cZ@2$4^2@2$5@2$9@1$0#h4^1+c").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP1"] "h01zh14__x1h24__x2h32b1h42b2h51nh61Hh77__arithh84__ffh98__varmaph:5__with;1bh<3immh=1pp;1p;2p;3p;4p;7p;8p;6p;5g001:j11Tg002Dj19Tg002bj15Tg001_j1ATg01;]j2<Tg005Lj1VTg01BLj2;Tg03KIj1?Tg014Xj3:Tg03R;j2GTg009>j36Tg007Ej20Tg018`j3YTg01<Ej28Tg00h>j22Tg00gXj23j1UTg003mj2BTg00B2j1STg00BRj1RTg00C2j2QTg00IDj1NTg00W9j4MTg00CPj1LTg00Cnj1HTg00E<j2=Tg00ifj3>Tg00Jcj4ITg00Nmj7JTg00Fej2KTg00GGj2FTg00H3j3ETg00HRj4OTg00jIj8DTg01U1j3PTg000\j67Tg01>_j2@Tg01Ucj3CTg03Jaj5TTg019mj3XTg03SCj1WTg006gR0f1R1f0R236p=4g004GR3#1R4#1#1#1#1R5#1#9R6#5R7%A4#1#1#9R8#5P71<82%A3#1#1R9#VR:';#?f2R;=:621<81/;:R<,G;R=567X;7g009XR7%52R>%51R?g00;N%5;?612f3R@/0;10@1'4RA[10;110;2'4%5@?6;1[RBf4#5?6@;\AAY;12P2n2001000000120000000W4W3W5PB^4?^3>^57P2P6%?<9:6;R7P=P0106;R>186<R?,06RB'2,361<8;/;:R:106@R@'2RA,86,06RC,42X00P0136<RD12@2,36/4CX00P012<>RC,36136:,2@,36/42X00P012><RE,36136A,42X00P0P0%U6RAPAPEPCP0\0/BAg00TeRA#S%RAP01Q0;P1%N0CM%L0%H0RAg00Qdg00RCREPEg00RcREP01=03R31=04R45>0g00l[A>043CIg00SCFJ1KAEP2P;g004lREg00:6RA'B1F2;=6EAdg00=oRA=E01COb8b9b:X10X2012211212'4^10^20P2P:P@O2b7GD12>D,36AP6><E7186C,061@6CE7PB1@6<E7A:6;?,06AC6;?E71067106='4eO4b6%95R5P5P8%99R9P2189ADT7X6%W2E7W<W=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP1.

Ltac step_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma step_opimm_gen : ltac2:(zQ "i11!h9!jc!in5!vd!o7!hga!mlb!is5!mm4!mmb!m7!mrb!hk6!ime!ms3!q2!ir3!msa!mt7!mu5!mv1!ng3!nj1!njf!nk8!q6!jj4!ju1!nl1!nl9!nm3!tb!u0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$hf@1$0#5ZKv$f@2$i0@1$0#5Z^c@3$hd^c^6@3$hb^7@2$hc^c^5@3$ha@1$0#c@1$0#k0^4@2$he^b+4^a^9").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##nep'0h01bi001bh11oh27Hdecodeh36Hecallh46Hfetchh53immh63memh72oph82pch92rdh:4regsh;3romh<2rsh=4segsh>1wi011wi021ci036c_fcsri047c_fregsi054c_pci066c_!s8%7!s0$svi081ii093iszi0:2m'i0;1pi0<1ri0=6reporti0>3st'i0?1xp%0p&0p;1p;2p;3p;4p;5p;8p;6g00BRk101Tg001:j1;!s/$_j1^Tg002Dj1G!s/$bj1LTg0000j2~Tg00oeR0j1STg03TIj2_Tg012Pj2JTg009>j32Tg03UKj1eTg03VKR1j2c!s1$kj1VTg03W\j4pTg005Lj1oTg03XHj4K!s/$hR2j1nTg03Z0j1mTg03[7j56Tg03\<j3\Tg03]Hj1QTg03^Fj3kTg03_Kj3jTg03`Qj3iTg00B2j1tTg03aVj1gTg03b^j1fTg03cfj2YTg0145j3XTg008Qj3PTg03e0j2dTg019mj3ATg01W[j34Tg03f5j39Tg01Sjj2OTg03g<j1MTg03h;j18Tg03i;j1NTg03j<k200Tg03k:j1UTg03l9j15Tg03m8j1TTg03n6j80Tg01<Ej2bTg03o=j51!s/$fj3aTg040Mj3`Tg041Xj2RTg042\j1}Tg043Ej1|!s/$oj1{Tg00E_j1zTg044Vj1xTg045?j1w!s/$hj2]Tg046oj1lTg003Ej1CTg047hj1vTg0490j1u!v6$Xj3BTg04:7j2E!s/$aj5<!s\$mj2[Tg04;Qj1s!y0$\j6>Tg04<Xj1hTg04=fj1rTg04>cj2qTg04?_j2yTg04@Bj3@Tg04AIj2DTf2R3g04BQR4f1R5f0R63@'Dp=F1D46p=Wf6R7f5R8f4R9f3R:?435P6D<p=:g04CXR;P:P3P5CK=@96,R8p==f7R<P!s>1]89@47'Dp=?1D469235p=3P;P7P8P9!sQ%D1P6CKp=7A@356,R:p=H!s1%]:9@49,D8p=IP<!sZ/P6G0,D4p=Zg016f$01g004GR=#;R>#^#GR?%;>R>#;R@#;#;RA#;#GRB#LRC'~RD%G@#L#S\CRE%GA#LRAg04DA%L?S00Q00%^=#;!sY$=#L%SARFf9RG/_<1JA932g004lRH%e8g00=ORI32g04DmRJg006gRK'cRL#SRM%V7PJPK!u/'Cp%o>R>CK,JL32PF1JA<%n4RNP0PA%m4RO#nRPP6f>RQp,2fxRRf=RSf<RTf;RUf:RVD6;\6RWP0PAPPPRPTPUPVPGD6RX#QRY=kSUP!sD&AjSYUPWP2P4PPAiSYUg04EY#tRW9FO6S01%gORZ%fOR[n10110?00031010>0000!s:,210101!s8I,Y4PRPHPDg00=oR\g018DS025X?R]9P?7PT1dT8AA=B9R^54<99T7R_n010!s#$200001OU>R`!uO%#WRa32X1FPHPIP2POPNPHPPP6%MX%8X%NX%^@#oQ!t1$-00X,JC%UX%5XPY%TXG0=FOWP0PLPPf8RY#VP1!wZ$PP6P21c;ER@#mS03PPf@RI1bB6S04PRf?RFPQPSPTD6Rb#M%8b%Nb%5b%UbD17a5%Qb3`P1P;PEPP1R@6S05%}5S06%|5S07%{5S08%zCRb%x5S09%w5S0:P6PRfBfAS0;PIPFD6#TG01]@3Rc5FOn20!vo'12010210:PZP!wf3=!wf$!sR%;!sR'8109RdPHPP%lY!s[$!vr0Re!ws/!s_%!sH011R46#WRf%g4Rg%f4Rh!sX%<!tE0=2NaX0HPM!vd$!}K&CpS0<P!{@%!wj&!w8$P6PdP!tG6PfPgP!t,=1MPH%C8S0=!ss&!w,&P@P@PEPHP;%C7RMPTPT%vRRaPUPbPb%uRRePVPGG0Rd#8S0>1bB>Ri9BBURj%5dRdPbD1S0?P?PCP7P<PHPCQ0=1bB\Rk1ET8Rl!vS1P^PTF:Q0>PjP!sc$!sE2VPWE=POP;PDP5P9n011!vj%50106104105103107S0@!sL&:!sL@AP;PCP5P3!sL@BPbP;%SCP5P6!sO@CP;PAP5P5!sL@DP6PUG0S0E!w$/YS0FPQPQPaPSPbPbPePTPUG0Rm#8RnABBSiRo%5mRmPbD1Rp!vt$YPGPHPC%C<S0GPk1EQ<S0H!vU1AA=B7RqPQF:PnPoPm!vx6TPWG?!{u01!{u&!yQ<RrPHPDP6PTP!#3V1PaP`!u8&!y5$53NX0HPH%C9S0I!s\$MPTPHPCP6PkP!xs2=4<^99T7!szA93NrX0HQ!sv$H!zv;Q0GPSPSPaPT!sc&UPVG0Rr#8R_ABBTiRs%5rRr!zh%J!vr$<!th'1ES7Rt!vk58Ru54YRvPSD<P_PsPr!vp6U!zj%Q0@Q0AQ0BPbQ0CQ!xj$TG0Rw!xi/GPFPFPaPQ!ts&S!sI$x#8RyABBQiRz%5xRx!ts%K!ts$GPV!tu$3Pk1EFYS0L!tv5<S0MPFF:PyPzPx!tr6S!xdUPHPD!vt$A9S<v!wj31OT>Rv!w1/53NP6PM!wk?P6P!{3&A4GkqR{PQD<S0N!zk,S0O!zn5!v|;SG0R|!t+-3PIPIPaPF!te&Q!sH$}#8R~ABBFiS0P%5}R}!t7%Q!tX$VPUPkAA=BYS0RPIF:S0SP~Q0PP}!ve6Q!veYP6PQA9QY{S0T!vg5S>R{!~e/!vg%CPv!ve8QPnP6PmPbPTF7PWCHPOP!u{'IP~P3P}PbPQF7PWEI!tyRQPaP!tY3X0C!|e$!xZ/ZS0U,[NPs%sTS0VE>!tx7Q0J!|%'P!{j&Q0K!zHWQ0U52NeS0U!v4;Q!yZ$!v5:Q0S!v6aQ0T!v79A4YkuS0T99S<!vA5S!vA$Q!v>;!z=$<Q0T!#3c-PU!u4+w!sM-GPVPkQ!~B1PS!uBYS52Nen0110001020101b0!}h<MQ!#=l&A4<k^S0SPTD<!#=OCQ!#;8-Q0FPpQ!~87!|[XMPTQ0S!#9/D53Ne!#4>JQ0H=4GqRq!#4@$H!#4@-S!#4@8P!#4%/Q!#3V+1EIGQ!#3S$Ro!#3R{qRq!uu4!#3M4Q!|B?H!|B=Po!|AaPq!|@<tuR{!|?7Rv!|>GP{!|=IQ0L!|>h=2Nv!|<Zl^Rl!|;\S!|;mA9T7l!|9E!u[3AP?9]%h9!wT:!ty$=PUPUPaPV!ss&GPYG0R`#8RlABBViRp%5`R`PbD1!v5$8P7!#J9$IPk1EU9!#@X4:R=PUF:PlPpP`!vQ6G!#>M<VG0!tj/GQ!#Cl'YPHPCPMPkP!#Cj1PuPSF:!#C`>!#AlX=PU1dU9=47=99U8R=!#>44V>R>!vT/53NeAP?8]R]%h8!w;+2Q03PPQ0<PR!#W8$PYD6Re#M%8e%Ne%5e%UeD15ai%QeRi5`T!wn'Q05Q06Q07Q08PbQ09Q!#S'$!#T'$PUD6Ra#TG0=FOc!#R}N!ur>R!z1$]PUP!ug3>!u/%#WR]52Ne%V<R7P6!u\+!#R2$7!#V@-!un&4%Ma%8a%Na%5a%Ua!#Uy%a5`F!u_CQ!#U`$PQ!#Ub$!u^S!#U]6!#U[$<!#U[4!#T8Q]e%e<P5E>A\Te<,Y4=2N]R<eP<e1_TVP3E>!#\Z$%reR3,_TA\SX6RX!s;%AkTi3P!s3'j!s3%!#\|%Ti3Q01!uJ6!#\i`!u&$1qTe!xR%Q021y?\d9X?\9P?8!x`=53NeW2W3W4W5W<W9W7W>X;EW6X8CW:W=o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_sltiu : ltac2:(zQ "i11!h9!jc!in5!vd!o7!hga!mlb!is5!mm4!mmb!m7!mrb!hk6!ime!ms3!q2!ir3!msa!mt7!mu5!mv1!ng3!nj1!ki4!njf!q6!nl1!nl9!nm3!nmd!tb!u0!hpb&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##1Ph01bh13immh21mh33memh42pch52rdh64regsh73romh82rsh94segsh:1wp;1p;2p;3p;4p;5p;6p;=g00BRj1PTg001:j10!s/$_j1;Tg002Dj12!s/$bj14Tg0000j2KTg00oej17Tg03TIj2ETg012Pj2:Tg009>j33Tg03UKj1CTg03VKj2A!s/$kj1@Tg03W\j4OTg005Lj1NTg03XHj4M!s/$hj1JTg0145j3HTg008Qj38Tg03e0j2<Tg019mj3GTg01W[j3FTg03f5j35Tg01Sjj2>Tg03[7j51Tg04AIj26Tg01;]j29Tg01n1j2=Tg003mj2DTg04F^j3I!uW$\j6?Tg04>cj2BTg04Ghl=LTg016f#Pg004GR0#0R1#;#2R2%01R1#0R3#0#0R4#0#2R5#4R6'KR7%23#4#7\6R3%24#4R4%42R8%;0#0!sP$0#4%74f8R9f6R:'Ef3R;,:433g004lR4f4R<#Cg00=O33g04DmR=g006gR>'AR?#7f5R@#@P=P>g01o9R>P<P;f2R=CO%N1R1CM,:?!sa$BQR?#JRAp,2fxRBP4P7g00=og018D5H2RC982@RDf:RE1<E<RFAG05;5F>R595E@n010!s#$20000f9RG/>1RHP9f7RID1,6?f0RJP!t#$A82:CRCf;R21<2@190<'=952:!sk11>E1R1PGP9!sf$RK53AX2AP6190;,=FRL!su%PCP2A52:J!se1P!sa,=3AKX06!sU&DPEA5E@L!sU2HP9P!tx%,DAP5AIF0;E?PBPEPG!sA&B2P2!s5'P:P>P@P<P;P=f1PJM=LE?UUUW1X88W5W:X73W3X46W6W9o"). Qed.

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

Lemma step_ecall : ltac2:(zQ "h91!h9!jc!in5!vd!is5!mmb!ire!o7!ime!nn8!q2!ir3!nnf!msa!mt7!mu5!mv1!ng3!m7!np7!nq1!nl1!mrb!tb!u0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$8$b>4regs@2$h2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>0@3$3@1$2@1$1@1$0#i0@2$e^6^4@2$4@1$1@1$0#i0^1>0@3$3$7@1$f^2$9@3$3@1$h0$5@2$h1^8@5$h6?2fx^7^6^5^4@2$d$5@8$c^7@1$h4?2fx^6@2$4@1$1@1$0#k0@2$h5^7@3$h7@1$0#5+h1Kv$a@2$h8@1$0#5+h1@1$6@1$1@1$0#k0@1$h3?2fx^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##;2p'0h06Hecallh16Hfetchh21bh33memh41oh52pch64regsh73romh84segsh91wi001wi011ci021ii033iszi042m'i051pi061ri076reporti083st'i091xp;1p;2p;3p;5p;8p;6g00BRj1iTg001:j14!s/$_j1JTg002Dj16!s/$bj1DTg0000j2[Tg00oeR0j1MTg03TIj2=Tg012Pj22Tg009>j31Tg03UKj1GTg03XhR1j1FTg03Z0j1ETg03[7j55Tg03\<j3?Tg03]Hj1>Tg03^Fj3PTg03_Kj3NTg03`Qj3RTg00B2j1WTg04@Bj37Tg04AIj20Tg03aVj1LTg03b^j1KTg03cfj29Tg047hj1VTg005Lj1UTg0145j3HTg03e0j2:Tg00E_j1TTg0490j1STg03n6j83Tg03g<j18Tg03h;j1CTg03i;j1ATg03j<j2OTg03k:j1<Tg03l9j1;Tg03m8j1BTg03VKR2j2I!s1$kj1hTg01<Ej2gTg03o=j5f!s/$fj3cTg040Mj3bTg041Xj2@Tg042\j1`Tg043Ej1_!s/$oj1\Tg044Vj1ZTg045?j1]!s/$hj2^Tg046oj1YTg003mj2a!x,$\j6QTg04=fj1XTg04>cj2dTg04?_j2eTg016f#ig004G#4R3#J#6R4%43!s3$4#4R5#4#6R6#DR7'[%63#D#M\7R8%65#DR5%M5R9f5R:f3R;'=f0R<,2531g004lR=f1R>#Gg00:6R?31P9f2R@,25g04BQRA#FRBP0P5%EARC#FRDP<f9REp,2fxRFf8RGf7RHf6RIP:D5;?<RJP0P5PDPFPHPIP:f4RKD5RL#>RM=PGIP!sF&ANGMIPJP1PAPDARGMIg04EY#WRJ97A<,0CRN%LCRO%KCRPn1011090003101080000!s:,2101!s8K,9APH%VFRQPI%J3#UR3g018DRR5H4RS,:H,27%T7RT%SFRUP:PKG3,0ARV31X49P=P?P1PCPBP=PDP<%8L%CL%AL1OLS,27%<L%;LPM%BLG3=7AJ,0CP0g04DmRMg006gR?'IPD%h;P2PMP?PDP<P1g04CXR?/I8RM#EPDf;R91g6<PFf:R6PEPGPHD5RE#8%CE%AE%;E%<EDf7c>%>E3bP2P?P8PD1@M<%`>%_>%\>PT%Z>%]>P<PFf=f<P9P6D5#BG31^M@57A,0Cn20!v@'120!vL$4POP!w737!vk$!sR%5!sR'2103P=PD%Y;!sY$!w#%002!w@3!s[%!sF011@A<,0A%LA%KA!sS%6!t<0=1BVX2=PIPQP:1:IS,27PTPUPKP;!wX%=,aBPFPIP:PKP;D5RF#8%CF%AF1OF!wS%F%;F%>FRS%BF!wV&@A,0A=1B=e%G@P<EQA?HF@,9!s:$R@eP@e1=H:P>EQ!zh%%XFR>,=HA?GL<RL!z}&PHS>P!s3'N!s3%!{2&HS>PN!vc6!zta!u%$1dHF!v0%PR1e43d9H43,:I!v:351BeW0W1W9X78W3X57W6W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_signed_small : ltac2:(zQ "80!h9!hq7!vd!hga!hl4!hif!jc!hpb>1x@1$6@1$0#k0>0@2$4@2$1@1$0#k0^1@2$5+2+jf@3$2$3@2$7@1$0#k0^2@2$1@1$0#k0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP2"] "##2lh02Hah14__p1h26__sat1h3!s/%3h44__x1h51Hh62Hxh77__arithh84__ffh9!sP%0h:!s/%2h;8__varmaph<5__with=1xp;1p;2p;3p;4p;6p;7p;8g001:j12Tg002Dj1B!s/$bj1MTg007Ej26Tg005Lj18Tg001_j13!s8$jj2<Tg00;2j20Tg01YJj1J!s8$Nj27Tg00@Ej2>!s/$mj3=Tg00AQj2YTg003mj2ATg00B2j1V!s/$Rj1UTg00C2j2T!s/$Pj1Q!s/$nj1OTg00DYj29Tg00E<j2NTg00Jcj45Tg00OQj6L!sA$_j1I!sA$@j3HTg03M4j2GTg00Fej2KTg00GGj2FTg009>j3@Tg00H3j3E!s/$Rj4D!s\$Wj1PTg00:Vj2?Tg03N4j3CTg01;]j2RTg00Nmj7STg00P5j7X!s/$Yj8WTg00=oR0f0R1'?p=1f1R2g00QdR3g00RCR4P4g00RcR5P1g00SCFSp=4f2R6P3P4P4P5P2P1FXp=:f3R7!s;+6P2P1GWp=;g004GR8#2R9#2!s$'R:#BR;#M16;1%89R9%38#3!s$%R<#8R='<R>'016;2R?%J2%1?%8:R:,<9R@,0?'71>9=1009RA%1=100>[RB[%19RCg00ScRDA=9=2UW0%1>\D^0C1>9:%1:100@[R=\AA=9:2VDX0C%1@!sH$P2g00T?1Y09'APAeRAO1P=f4PAO1PBp-0RBg006gRAg00TeR=#V%U=1TA2%QA%OAR=PA19A0g00Q=RC1NA8R8C5,4=P=!v8+7EL5:=%I4R4P=PAP8g00UQ19A9%B<5HAR<!sX$R9P4PA1GA<PCP!sk%=:=9C;C;1K=5P1P6g004lR=g00:6R5'A1F16=@=5dAEA02CDb8b;b<W4W1%11/72102>%P>/?6106>'7[[^4A^1BP1f9,6;R1/0@P1f7f8O4b7b3b2b9b2b:b3b55C;1R;2=@A?eW6W=o"). Qed.

Lemma bv_signed_hi : ltac2:(zQ "90!h9!hif!hq7!vd!hga!hk0!hr5!jc!hpb>1x@1$7@1$0#k0>0@2$5@2$1+2+jf@2$2@1$0#k0^1@3$3$4@2$8@1$0#k0^2@2$6@2$2@1$0#k0^2@2$1+2+k0").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP2"] "p'0h01xh11Hh22Hah36__sat1h44__x1h52H0h62Hxh77__arithh84__ffh96__sat0h:8__varmaph;5__with<1eh=1zi001np;1p;2p;3p;6p;4p;7p;8p;5g001:j11Tg002Dj1:Tg002bj1BTg005Lj16Tg001_j12Tg005jj29Tg007Ej23Tg00:Vj20Tg01C_j1@Tg00iIj27Tg009>j34Tg003mj28Tg00l4j2;Tg00kXj6WTg03Naj2VTg03GYj1UTg00@Ej2OTg00;2j25Tg00@mj3NTg00AQj2LTg00B2j1KTg00BRj1HTg00C2j2ATg00CPj1CTg00Cnj1DTg00DYj2ETg00J@j3FTg00E<j2GTg00Jcj4?Tg00Nmj7ITg00E_j1JTg00PYj8>Tg00Fej2=Tg00GGj2MTg00H3j3<Tg00HRj4PTg01YJj1QTg03O@j5RTg000\j6STg01;]j2TTg004GR0#1R1#1#1#1#1#1R2#:R3#BR4%61R1%20#2#2#2#2R5#6R6'9R7f0R8,33R9'0g006gR:f1R;,33R<%@3'7f2R=,33%62,91R2'794:8X=:17<2R>,8:1;3<P3P<g009XR?g01A1R@743RAP?P3P?p-0P8g02`XRBg00ScRCn0110000020010000X<?g018DP@P8EWPB1VB8b5W1%UAe1O16g00=oRA/51RB10A615A7[R@[10A1R?AN16;VCW210A7\C^2?P;g00T?1LA1'8PBeO1P@g00TeR@#K%H@1A:;%C:%D:R@g00QdRBg00RCR?P?g00RcRCP@PBP?P?PCP:1E:1%:55F:g00Q=1G:0C?g00SCFIR0%J?P0G>1=@CP8P=g004lRCg00:6R@'81M8==4C@dA<:A;CPb8b:b;X4:1078107;[^4:P8f5,33f4O2b7b3b9b3g00;N10A91592R915<2%Q8P8n2001000000120000000X04P9^04P8P=O1b1DRES1T3;=4:>eW6W0o"). Qed.

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
End WithFP2.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_wrap8_mod : ltac2:(zQ "60!hga!vd!h9!hi5!hif!hj6>1z$0@3$1$0@2$5@1$2#8^1@2$3^1@2$4+2+8").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01zp;1p;2g001:j10Tg005Lj11Tg005jj23Tg006Gj22Tg003mj24Tg006gR0f0g004G#0R1#1%01#0#1'3'2,40W0o"). Qed.

Lemma bytes_le_Z_to_le : ltac2:(zQ "a0!hga!jh2!vd!nqc!jnf!hk0!hi5!hrc!jp9!hif>1k$1>1z$0>0@2$5Z^1@3$2$0@1$4@2$3^3^2@2$6^2@2$9+2@2$7+8@1$8^3").
Proof.
ltac2:(KReplay.run1z (kr_t_PropExec ()) ["WithFP3"] "##Pbh04__x1h17__arithh24__ffh38__varmaph45__with54__x2h61bh71zh81xh91Hh:1kh;1nh<3Hi8h=3Hikh>2Hzh?1ah@1ohA2HihB2IHhC4cstrhD1ihE1mhF1yp&0p;2p;1p;3p;6p;4p;<p;8p;Bp;7g04I7j2NTg01AOj1JTg001:j1YTg005Lj1ZTg009>j3Fj1xTg003mj2>Tg006Gj2BTg04J4j1kTg000\j6DTg00d[j25Tg01F1R0j1ATg00bmR1j21Tg002Dk10=Tg01<Ej2eTg007Ej2dTg01BLj2LTg00V8j2GTg00^iR2j1HTg00gXk20!si$5jj2STg00h>j20!t9$Qj1vTg01LTj4uTg01J@l<pTg01Hoj1gTg00B2j1l!s/$Rj1jTg00C2j2]!s/$Pj1i!s/$nj1hTg00DYj2QTg00E<j2\!u9$Jj3[Tg00ifj3PTg00Jcj4OTg00Fek20BTg00GGk20!uh$H3k30@!s0$Rk40?!tt$ok40!v]$;ij23j1wTg00WWj2C!t#$Ij2@Tg03LOj2c!sM$2j26Tg00:Vj29Tg00?FR3j2b!w@$Uk10<!tr$_k10;Tg01KLj3aTg04K4k30:Tg00_Hj2VTg00\Uk200Tg00edj3~Tg00`1j3U!s/$Zj2`Tg00aFj3_Tg00IDj1}!tm$9j4y!sy$[j4MTg00jIj8zTg04LFj4{Tg01ITj2|!u#$NR4j2T!sC$kj4WTg04MWk102!tl$oj4sTg00X4k303Tg04N6k304Tg00kXk605!s:$Yk106Tg01>_k207Tg04Ofk208Tg016Ek409Tg01M7l<^!s/$\lBoTg00Nmj7fTg00PYj8n!s/$5j7mTg00=oR5f0R6'9p=4f1R7%A6'1p==f2R81S76'Bp=:g006gR9?F76p=8g017eR:P:P9P9P2P0P0f3R2g01NfP8P7P6M<^p=t!sG&9!sG$5R0f4R;P2!sH-r!sF&!s$%1P6P7P8P1P2P;P0f6R1f7R<f8R=f9R>MBop=qP7g00QdR?g00RCR@P@g00RcRAP6g00SCRBFfp=E1S87,B2/36p=7g004lRC!u4%;1B87!s>$XP9!st$UQP6COp=KP2P?P@P@PA!tr%Gnp=2PCg00=ORD!u0'EDp=IP8!sQ+!sk%Q=P6COP!tL$<PCP;!sU/?!sU-7P6Fmp=R%46R?1N87#Jg004GRB#YRE#ZRF%YE#YRG#ZRH/=85:7'8[^79RIX::P9P5AF956X791>95%ZBRJ,B7%k7EDg00fMRK/N7#J1=HK9:7F'8eX>?X79P9157HRL%A2RM,1HRN7:F&0=GRG1eG8'd1L6H'G%H;,=HRO9:8FRP'8!s`$201G7RQ158H%A;RR,1HRS7:F/LH,G6/8PX79RPP91SFHRT,B7PP10NHRN%H2RP#ARU,1HRV'8RW10MJRX,1HRY,8NP9P9%x9RZP6X89R[PZ1876#vXF9X89PNPN1>9NPVPYP[!s$$9P9g01NB1176Cu,>9XE9X;9PHPH1>9HPUPXP[P[%A6,>9X8:PPPX106JRXX89P2PM1>9MCtErM:qM<p%g2%4Mg00TeRM#lR[%jMRU1]97RY%i9RN%h9RZP91Q9HR\1\9BRB5[9R]=P9\R^g00l[R_1Q9J9P9B9[9\CO'E20BZARAP6P8g00:6RJ,>C20A68=FCJdB0@957H0?RJb2b3b4X0911H6/0HR`11HX'8^09P6%A0RXO1b1bCH0>PWP910SH1B2T152H11HXRX!wK%'GRSA:2F6!wv$%g;%4R10XH9:2F1B0TRX/37150H1=H<7:FRR/LHRW/37Ra'CP1PF1=H=/0HP8C7Rb,;6X6C1@7HRc,3RAX1T8/C6/;bX6C1c7H167HRb19H7Rd'bP3168H19H8AX<T215<H!sw$>Re1@2HRfC7'CP<PF10eHP2C7';P6162H13=;Re15>HPFf;Rg#ARh,1HRi1@0HC7Rj,C6P>PF10iHRiP0C7Rk';X6CRlPe13>0Rm/Cj/!t|%Cm6/;mX6C&0<e15=Hf:Re,=HRm7:FRj1@;HRn'3RoP[PUPYPNPZ1KB\,EZRp&0;@R@Aa9B\Rq1Q95Rr'K,EZC2PAP!wk-66HRs16c5[!wg$P0P7O2R5b1:0:jnCIP=PF10mHRmP;C7P=PmP;%HKRn#H,V9Rj2009H1V9n5~91V9KRK5U95U9g00flRn'`=_M[PUP91]98P7%}9CyRtPNPZPpP@PZ1\9ERE9<ZrP@A[9\ERu=P9\,KB,EZRvC2!u#2X59%48Rw11H2/0H,68[\s^09^59P6PhP0P7P1O4b1CMD?AX=T;RTP=PHP;!vC,!tH$p!t#2Pb!sn$P5!sa%W<P6O119H2PlPo1;6k!y?$;m16;m19m;!y;%0i19i015eHPFf<Ri,=HR01@1HC7PePF100HR0P1!y7'1015gHRe1@<HR3'3RmPiPFf>#ARk,1H/0HP=C7!zk%Rl103HRs,3gPl13g<1@=H/0H,3i!y6%P9PC%wgRiPiPsP<PC\9/>i!u]+9AP9q\P_PBCO,EZ!xe1@6H/0H/86!xd%=O1b1GzPgPFf=,=HR_/0HRiP<C7RsPgPiP<!s~$!x#%vP@Pv!w^511H7!wY$6Rb11H8Rp/0HRh,67[!wg+kP=P7O3Rx!w+%PmPgPHP3!wb,A<Z\BRmP@A<Zrq!zl39H6Ry%4c!zk&=P;O2b1C{D?PePFP_P3C7RzPeP_!sz&!u#+1Kqu!{e5X5916cp\b!to&!te&W=!xk%01PlAFCD!}D$>CDP!v&&AU9Kj/`n,|K=_M[RM!t8'A<Z^ERKP@!s1$rBRB!u?%^=RZK!{2719`7R`%47R^%4h19h2'T[!vM,=PkP7P>O4R>b1CWCIP!uS'!tA+P!t<$P!t7&]Aa9E\9<Z]5RZ!|K9p19pf'T\^\`!t6&!t&&!ul%n20010!s#$211000!s'$b@1CDo&02oD?P!|_5!wv&\=RZm!tB2%4H/Td\y!|j'WCI!|j%!t7;PaPRPHP7!t,-BP@PB!s~2RJP^\?^09!#:4$P7!xx$sD?1GXW/37B03XW7D?XA?XD9604Sb9POP6J05b9PQ&067ED1eG7,dG207G7ED1N2L#JP8PLP41576#4Pw[1587#4\^R^1528#4\w20876P6!u6-12!s-%0X;9X?9P^^;9^?9!tf$HPJPAP6P2P8O2b1O3b9O2ED1NP7#JA:7FV!#@^'XBIX::P6H09X::o"). Qed.

Lemma bytes_le_N : ltac2:(zQ "c0!h9!jh2!vd!hga!jnf!nrd!hi5!hrc!jp9!hif!jc!hq7>1k$1>1v@1$a@1$0#k0@3$2$3@1$4@2$5^2^1@2$6@2$b@1$0#k0^1@2$9+2@2$7+8@1$8^2").
Proof.
ltac2:(KReplay.run1 (kr_t_PropExec ()) ["WithFP3"] "h01xh11Hh21kh31vp;1p;2p;3g001:j10Tg002Dj1?Tg002bj1;Tg007Ej23Tg00:Vj24Tg005Lj11Tg005jj22Tg00;2j2:Tg01YJj17Tg04PMj36Tg04Q^j25Tg01AOj18Tg01F1j19Tg00bmj2>Tg006Gj2=Tg009>j3<Tg017eg004G#0R0#0#0R1#0#0#0R2#?R3#;R4f1R5f0R6,33R7g00;Ng00=oR8/47R9%10R0%12'2,:71335,48%76P5n2001000000120000000X04P9^04P6P5O1b136g006g1556#8%11%95'>,20,=73<eW3W2o"). Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithFP3.
(* [comment removed for export] *)
