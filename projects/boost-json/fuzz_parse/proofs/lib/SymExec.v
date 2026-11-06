(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Footprint.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_SymExec () := KReplay.lz_vm "#$2UI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C!sc@;bv_unsigned!sPA5bv_eqK!t6+7Numbers7BinNums8positive02!sK=1N02!t5A7bv_wrapC56Stdlib6ZArith6BinInt1Z3ad!txB7Z_to_bv!tU>Z02!t/=pow!sC<6moduloC4!sF14ZdivAZplus_mod_idemp_lC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec=!uy&64!sr#C13~~~C!xN78eq_ind_r!v-A@!v-&!xW+I!v7?0I!x+?!z#93and00!y2G3!vXIrc!vXO7Sym!vW#!u_'64!v^$_l!vZ&!wLX6v_addi!si%!t]X:!sh%_lit!sl^!uK3r!uK_7v_auipc!sj%!|/@3!{j<4landK!#3w:1!thY8jalr_tgt!{V'!{8?9bv_!#4b%!ts;>pow_pos_nonneg!sN<2lt!sB>e!sB<:!t-#!t&%!v%29Datatypes4list01I!sFA0K!{y'9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr01!sIE7K!t?L1C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!u~<4find!sqAC!sq0_soun!yQ=3mul!{E:x!uL-!s]&:Znumtheory<Zmod_div!#7^#!sh76!#7X$!#8f`32!#8f+K!w&<G!wN'4!wN<5eKind!z]=uni!z]9!se%4kind!yK#!sf@1!#3l?1!#9F74True!{C8!xB-;!wF%!v]$!tt8!zV13Op205!uc=bool!#:b-!sF81!#4F@:bv_extrac!#3[<4of_N!#?F<shift!#;EX!y6'_32_64!#6F%!#4n;!t7%_0!#>|BC!uJ,!#DX,ELinuxProcessSemantics5Riscv3Sem5low3!#D7@1!slA7Prelude4sext!v-X9!tR$!#<m+!t>Jzext!}WY5!#>/#!w?B7testbi!y7=3ltb!y6=ltb_lt!#9%?2!#7mD2!{N<6op!xe#!#GF=;!yP&spec!tV@!#?$<Amod_pow2_bits_low!u%E3!v2Ag!#=A<B!t<1high!sR<9!sI$inj'!#6XE8!sJF5!#4GH3!#4#A!ww=3na!xa9!t415Psatz!sOM6K!#6{L2!#A8A2!#J8F1!vkF3!u|A1!u&N1!ye=of_nat!#34:?!s<26BvBase=!#Hu#le_bytes!#<a5;ZifyClasses!#>E#ff!#O;8iff_refl!sjB3inj!sIB5mkre!snC9and_morp!{{44Znat5Nat2Z9is!#Fk'!w%L3!~3E5!tkB;rew_!v/%v!#8RW<!~Z+low!#7@%3!#;5$7tac!x?#<f_equal_help!#NaX!#5h$8_!t;'!#Tb7!zk,7nat_!#F28!x,2app!yaC!sK$2I!|#@0!xI>8inj_succ!t768!t7#Inst7Inj_Z_Z!#4{H1!vdXA!|P0!#XI-!}?I>!#=]#!sE+@word!}J1!#>=F5bvmapI!#;eB0!tdZ:fetch_!tj#!#<qC1!t2Z8is_ecall!#Fk<prod!u:=!v0&DecodeC:d!s-$_anyK!sW@5!y@#r5i!s+#07K!tKA!#U}Y4getr!y-`8store_okI!sfY>machine_resul!#T1#!snX=ac!s?#_repor!}Y#!v-Ymkst!v-`D!xM&exec_!tb%!|:=!srB6ms_mem!sdZ=!|&,_ov!skZ>!sk%tail!zp#!tYafailureK!y@i2!snj3!uKZBdrop_!z50!z3P7Cat!#dH#w!#6N$!z4_7m!tQ#g!z#[8ms_f!sf^9ms_pc_valK!#pjC1!{s^reg!v?`sv!se^fcsr!u2_om!zoZ=!zo'stat!#IP#!sm9!#V,+4core!#UhB!sO$exec!uKZCinterp_eff!#5?b<!|T&value!u+E6c!{S@!sO,7c!{=A!vP/_pc!tHJ!y\=!sO0!yF^?!vn&d_rang!#BJC!#?@%Bis_!|{$ed_illegal!twE5is_x0!viFreg_get!#]t@6b!#ZR$!#p\Xfp!xF%!#sm^fp_!w>#!#6K^<write_to_mem!#9[i!#`+I6!#~T#b!#iG\eqb0_!xA%!vd_b_npc!#cz%!#KDW>!#ac%!#JK&!t[U!#;e&C!wT/_w!su[!uR+9b!z`#sex!#Cn`5!#;9#!scZ4step!#8\Z!#Fg01!#GVZ!#9K0!#HE;!#9K2!#HnK<MemImageType7Segment!t6C!#Lb/0!#M6Gmsize!#CK[=memory!#:_%!#tU7!#pL$1".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd4Npos35stdpp9bitvectorbdefinitionsjd2bvhd1Z46Stdlib6ZArith6BinInt1Zm33addjd7Z_to_bv37Corelib4Init5Logicob2eqjd7bv_wrap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~qe6v_addiqe4btgtqe7v_auipcqe8jalr_tgtm34land3h5LinuxProcessSemantics5Riscv3Semhh55low32qe5v_addjdbbv_unsigned3h5LinuxProcessSemantics5Riscv7Preludehl65bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SymExec4FPX1~~~~~~ho53envqe4getrm36of_natm36modulom33powm36shiftrm32leob3and3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehvedZ_to_le_bytes04listm33mul3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsikah0word_to_le_bytes06option3h5LinuxProcessSemantics5Riscv5Instripe5instr04Some04bool04prodikadmachine_stateqe4mkstjd9bv_signed05false04pair04true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejh47Segmentika9MachineOkikaafetch_wordika8is_ecallikaemachine_resultika4stepika8store_ok3h5LinuxProcessSemantics5Riscv7DecodeCjq1adecode_anyipe3SZ4ipe5Store69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ju56wbytes" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Inductive expr : Type :=
| ELit  (z : Z)
| EVar  (n : nat)
| EAlu  (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)   (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr).  (* [comment removed for export] *)

Definition env : ltac2:(zQ "00S") := ltac2:(zQ "30!h8!j6!la>0$0@1$2@1$1#k0").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv64_wrap_l : ltac2:(zQ "70!j6!lf!nb!o1!pf!la!q4>1a$1>1b$1@3$4@1$5@1$0#k0@2$3@1$0#k0@2$2@2$6@1$0#k0^2^1@2$3@1$0#k0@2$2^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##,Dh01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g0000j16Tg000Sj38!s/$mj20Tg001Wj3@Tg002;j15!s/$`j1>Tg003>j23!s/$dj24Tg004Aj29!s/$gj1;Tg005Ej2=!s/$bj22Tg006Bj3?!s/$ij1:Tg0083j67!s/$Qj2<Tg009@R0f1R1f0R238p=1g009^R3%62R4%61R5g00:<f2R6#6?812f3R7/061071'1R8[10611062'1%67?861[R9f4#6?876\8A@612P2n20010!s#$12!s-%0W2W1W3P9^25^14^33P2g00:W#5R3#5!s$'R4#>R51356R9/41R8,95R:1461R;,95R<P01358R=1476R>,95,05,12X00!s@$;R?1357/46,35/!s>&%;3%;4'=R4,28135>R>!sY+2641426/24/1>!s9&;41274/4!s<%2X00A?614P?%:;E7P9%:6E7P=%:8E7105<1<5;!s0$:1<58E7O4b4X60X50o"). Qed.

Lemma Z_to_bv64_wrap_r : ltac2:(zQ "70!j6!lf!nb!o1!pf!la!q4>1a$1>1b$1@3$4@1$5@1$0#k0@2$3@1$0#k0@2$2^2@2$6@1$0#k0^1@2$3@1$0#k0@2$2^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##,Dh01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g0000j16Tg000Sj38!s/$mj20Tg001Wj3@Tg002;j15!s/$`j1>Tg003>j23!s/$dj24Tg004Aj29!s/$gj1;Tg005Ej2=!s/$bj22Tg00;<j3?Tg006ij1:Tg0083j67!s/$Qj2<Tg009@R0f1R1f0R238p=1g009^R3%62R4%61R5g00:<f2R6#6?812f3R7/061071'1R8[10611062'1%67?861[R9f4#6?876\8A@612P2n20010!s#$12!s-%0W2W1W3P9^25^14^33P2g00:W#5R3#5!s$'R4#>R51351R9,46R8,95R:1461R;,95R<P01358R=1476R>,95,05,12X00!s@$;R?1356,47,35/!s>&%;3%;4'=R4,28135>R>!sY+2141472/24/1>!s9&;41264,47!s<$2X00A?164P?%:;E7P9%:1E7P=%:8E7105<1<5;!s0$:1<58E7O4b4X60X50o"). Qed.

(* [comment removed for export] *)
Lemma v_addi_lit : ltac2:(zQ "70!j6!lf!o1!pf!u9!nb!la>1p$1>1i$1@3$3@1$6@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##%ch01ih11ph21zp;1p;2p;3p;6g002;j10Tg002`j1;Tg003>j2:Tg0000j14!s8$dj22Tg004Aj21!sA$Sj33Tg00;cj29!s8$mj25Tg008Qj26!s/$3j67Tg00<oj28Tg009@R0P0g00:W#0!s$-;R1f1R2':%41R3f0R4/22,11f2!s-%33X2019241112R5,511612E718541224,11533eX00W1o"). Qed.

Lemma btgt_lit : ltac2:(zQ "70!j6!lf!o1!pf!v2!nb!la>1p$1>1i$1@3$3@1$6@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_SymExec ()) ["FPX1"] "h01ih11pp;2g00>2j20Tg009@R0f1f0'0X00W1o"). Qed.

Lemma v_auipc_lit : ltac2:(zQ "70!j6!lf!o1!pf!v9!nb!la>1p$1>1i$1@3$3@1$6@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$5^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##%ch01ih11ph21zp;1p;2p;3p;6g002;j10Tg002`j1;Tg003>j2:Tg0000j14!s8$dj22Tg004Aj21!sA$Sj33Tg00?8j29!s8$mj25Tg008Qj26!s/$3j67Tg00@Dj28Tg009@R0P0g00:W#0!s$-;R1f1R2':%41R3f0R4,22,11f2!s-%33X2019421112R5,511612E718541242,11533eX00W1o"). Qed.

Lemma jalr_tgt_lit : ltac2:(zQ "90!j6!lf!o1!pf!hg3!nb!hge!la!q4>1z$1>1i$1@3$3@1$7@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$6@2$5@2$8@1$0#k0^2^1-2").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##&/h01zh11ip;1p;2p;3p;6g002;j10Tg002`j1=Tg003>j25Tg0000j16!s8$dj23Tg00AHj1;!s/$fj22Tg004Aj21!sS$Sj34Tg00BDj27!s8$mj28Tg008Qj29!s/$3j6:!sJ$^j2<Tg009@R0P0g00:W#0R1#0!s$+=R2f1R3'5R4%62R5f0R6/33%;1R1'2,12f2,52/33/21,1234X001346!s5%R1,751123R4,821923E:1<46=451eX10W0o"). Qed.

(* [comment removed for export] *)
Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##$Dh01bh11np;1p;2g0000j11Tg002;j10!s/$`j13Tg00Ccj22Tg004Aj25Tg00BDj24Tg009^f0R0#1g00:W#0!s$-3R1#1f1/20,51'4W0W1o"). Qed.

Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##$Dh01bh11np;1p;2g0000j11Tg002;j10!s/$`j13Tg000mj22Tg004Aj25Tg00BDj24Tg009^f0R0#1g00:W#0!s$-3R1#1f1/20,51'4W0W1o"). Qed.

Lemma bv_wrap_32_64 : ltac2:(zQ "40!j6!q4!lf!pf>1z$2@3$3$2@2$1@1$0#i0@2$1@1$0#k0^1@2$1@1$0#i0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##0zh01zh12Hah27__arithh34__ffh46__sat0h5!s/%1h68__varmaph75__witp;1p;2p;3p;4p;6p;7g002;j11Tg002`j1ATg003>j24Tg004gj18Tg005Ej2B!s/$bj20Tg000Sj32Tg00BDj25Tg00DKj2<Tg00E3j26!s/$Oj23!s/$kj3:Tg00FOj1C!s/$oj1PTg00GOj1O!s/$mj1NTg00HKj1MTg00I6j2>!s/$Yj3?Tg00J<j4=!s/$gj2LTg00KIj2KTg00L5j3J!s/$Tj4ITg00MFj2;!s/$cj4GTg00N=j6H!s/$ej6FTg00OAj1@Tg0083j67Tg006ij1ETg00PKj7DTf1R0g00Pog00QNR1P1g00QnR1f0R2g00RNFDp=9g009@R3P3g00:W#1R4#1!s$%R5#1R6#AR7/42R8%84R4%85R9'BR:'0%A5R5/40R;9232X03P3%86R6,B4R<,02R=102:R>=23;!sD$P>100</0:=!sV'!s8$:!se&153>10=:P:P<P21<49g00RnR=/64R>13=916=:R;[[13=4R?g00SLR@A:490UW113=:\@^1!s>$hR9#CRA%P9R9%O3RB%N3RC%M3RDP31>3=REg00TTRF1>34RG=?35C='91LD1R1P2f2RHg00U;RIg00U[RJ'51K2H=2IJdAJ3=0CIRJb3b6b7P;P2b2b4b51<4613=616=<R;[\>A:460V@X1?13=<!tl$PAP9PBPCP3PEPFA?3G7C=,9DP1P!sv4P31;2:923<X03P:1;::,53CGEHEF1452%@2E7P8%E2E71458%@8E7W0o"). Qed.

Lemma low32_lit : ltac2:(zQ "60!j6!o1!pf!lf!hj7!la>1z$3@3$2@1$5@1$0#i0@1$4@2$1@1$0#k0^1@2$1@1$0#i0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_SymExec ()) ["FPX1"] "h01zh12b1h22b2h31nh41Hp;1p;3p;2p;4p;6g0000j12Tg000Sj30Tg000mj21Tg001Wj3;Tg002;j13Tg002`j19Tg004Aj25Tg00V;j4=Tg00Vdj1<Tg00WBj28Tg003>j24Tg00Wbj1:Tg008Qj27Tg0083j66Tg00Xkj1@Tg00YOj4?Tg00ZAj1>Tg009@R0g009^R1f0R2#2R3f1R4#2R5g00:<f2R6#2?042f3R7/161174500R8[11641162500%27?064[R9f4#2?076\8A;642P2n2001000000120000000W2W1W3P9^25^13^31P2g00:W#3#3#3#3#3R1#9R3%31#9R1g00ZiR5P31514R9C=R81534R7P01119R:%<5'8,431536,13R;9002X00P0P:1432=00;X00R;P01414P;P014341416,43=002X00%:411371734E6P:1714E6g00Rn,8:%@:E61138P1P5P3P9C?E6O4b4%231512#>153230eW0o"). Qed.

Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof.
ltac2:(KReplay.run1 (kr_t_SymExec ()) ["FPX1"] "h01bh11np;1p;2p;3p;6g0000j11Tg002;j10Tg002`j12Tg00Ccj24Tg004Aj23Tg00[Gj3:Tg000Sj39Tg00BDj25Tg00ZAj16Tg00\2j17Tg0083j68Tg009^f0R0#1g00:W#0#0#0#0#0R1#2R2#1R3f1R4/40R5,32R6f2?:24=930X031536%01#2/35#6%75E8W0W1o"). Qed.

Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof.
ltac2:(KReplay.run1 (kr_t_SymExec ()) ["FPX1"] "h01bh11np;1p;2p;3p;6g0000j11Tg002;j10Tg002`j12Tg000mj24Tg004Aj23Tg00]7j3:Tg000Sj39Tg00BDj25Tg00ZAj16Tg00\2j17Tg0083j68Tg009^f0R0#1g00:W#0#0#0#0#0R1#2R2#1R3f1R4/40R5,32R6f2?:24=930X031536%01#2/35#6%75E8W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_add_lit : ltac2:(zQ "80!j6!o1!la!pf!lf!hk0!nb!hk8>1u@1$2@1$0#k0>1x$4@3$3@1$2@1$0#k0@2$5^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6@2$7@1$0#k0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##%mh01uh11xh21zp;1p;2p;3p;6g002;j10Tg002`j1;Tg0000j1:Tg003>j25!s8$mj23!s8$dj22Tg004Aj21!sA$Sj34Tg00?8j29Tg008Qj26!s/$3j67Tg00]bj28Tg00:W#0!s$-;R0#:R1g009@R2P2f0R3,50f2,30R4/23,10f1R5,24,10541X221305R2/931103R4,301603E7185412!sY$541eW1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sbase : Type :=
| SBLit
| SBVar (n : nat).

Record saddr : Type := SA { a_base : sbase; a_off : Z }.

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sym_state : Type := SS {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;
  s_next : nat
}.

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

Definition E0 : ltac2:(zQ "40!j6!hnc!hs4!la>4regs@2$1@1$0#5@1$3@1$0#k0$2") := ltac2:(zQ "70!j6!h8!hnc!hsb!ht2!o1!la\4regs@2$2@1$0#5@1$6@1$0#k0\1n$1@2$3^2@2$5@1$0#5@1$4^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : nat)
| SCDisjoint (a1 : saddr) (n1 : nat) (a2 : saddr) (n2 : nat)
| SCStoreOk  (a : saddr) (n : nat)
| SCReadBase (a : saddr) (n : nat) (e : expr).

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
Lemma shiftr8_mod_pow2 : ltac2:(zQ "70!lf!htb!hu4!hua!pf!nb!hv3>1k$0>1z$0>0@2$6Z^2@3$4$0@2$3@2$1^2@2$2+2@2$5^3+8+8@2$1@2$3^2+8@2$2+2^3").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##:Xp'0h04__x1h14__x2h23Hlth37__arithh44__ffh58__varmaph65__with71bi001bh81Hh91mh:1nh;1xh<1yh=2Hih>2Hkh?1ih@1khA1zp;2p;1p;3p;4p;6p;7p;8g00EOj23Tg002;j1ATg004gj1ETg003dj21Tg00WBj24Tg00^dj20Tg00_Ej2:Tg00BDj2;Tg00E3j25!sA$bj2LTg00FOj1^!s/$oj1[Tg00`Bj2JTg00Gmj1VTg00HKj1UTg00I6j2H!sJ$`j2FTg00aCj1TTg00Jgj2STg00KIj2RTg00L5j3Q!s/$Tj4P!sS$ej4CTg0083j67!t1$Oj1OTg00bJj4N!sn$<j4?!s8$hj4BTg00cSj3DTg00d6j2MTg000Sj3=Tg00:<R0j2G!sC$Vj4KTg00eBj3]Tg005Ej2\!s/$bj2ZTg00PKj7Y!sJ$ej8XTg00fIj7WTf2R1f1R2f0R3'\'Zp=2g00U;R4?=23p=9g00U[R59=43p=<g009@R6P2g00fmP3C?p=>!s4$PoR7g00QNR8P8g00QnR9P3g00RNFYp=8f3R:P7P8P8P9P1P2P3GXp=6g00gTR;!t,%@P1!sI+2P3FWp=Ig00RnR7/32R<g00:WR=#AR>#ER?%A>#A#ER@,11RA522/4@142@?2?11373RBP4f4RC/1@92:?RD112@RE'014C@f5RF72?/01,93X741:2CP41;431:1F/93P4f7RG,:C/93f8!sl&G?11F@'014G@?2?C/0F'9]2P2f6RH,::RI#<P01:23RJ#<1512[RK15231:12RL#<RM[15:1\M1L23P2n20010!s#$12!s-%0X96X:6PK^96^:6P3PFPCP2O3RK15FCP411H@RM,0CRNf9RO/4@f:RP!uB$G!uB%RQP414C@RR/0HRS11G@,0O/!sB%TP4PNPT1;4NPSPCP@PHg00ShRS#^RN%[SRS1J62%V6RT%U6RU1H67RV1F6=R='>,8URW%T8R8PWC61SU9R9P3P11;451R31#<dAQ672CPR5b4b5b6X06RXP<\B^06RBP3PGPHO2b3CCE7A2R?O/0HRYPRPOPHPNPSP61J61P2%O6CNRZPTPUP6P=g00TTR[1F6>R>C?,8UR\P8P\C6P9P!t9,X161532R]1521[^06^16P3PPPG!vb$^b3CBE711O@R_92C?/0MR?PCP_PM!tK$!t>%\P8P61H6@R\9D6=R`P[AD6>\R\!tH$!tB7EA\]!t=&!t3&b2b8W2%@IP0%@J1321[RJ1332R0%@LRL[131:RI\L1M!xz<<6X;6PJ^<6^;6PK13CFP4P;PQP4P;A=4;!zz$;4;P!v`/!u;$1>=!wt$>P8PUPWP8AIUW>C6!u36371/GI\<\0!vO+GPPP2PCO4RPb3CKE7P!vD5!t$+1>V`,8U1>`\,8U5IU!t4:A11:@,3A'G!t:-!t-&!vL%n01!uz%20101P3O1b2b714D@/02PDP@P2PXPBP3P1P2!y\'W=X?63]W>XA6X@6o"). Qed.

Lemma mod_pow2_low : ltac2:(zQ "60!lf!htb!hu4!hv3!hv8!pf>1z$0>1k$0>1m$0>0@2$4@2$3Z^1@2$3^1^2@3$5$0@2$1@2$1^4@2$2+2^3@2$2+2^2@2$1^4@2$2+2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##9xp'0h03Hlth14__x1h24__x2h34__p1h41bi001bh57__arithh64__ffh78__varmaph85__with91mh:1Hh;4__x3h<1nh=1xh>1yh?2Hih@2HmhA1ihB1khC1zp;2p;1p;3p;4p;6p;7p;8g00EOj21Tg00:<R0j2<Tg002;j1TTg004gj1LTg005Ej28!s/$bj20Tg00_Ej25Tg00BDj2;Tg000Sj32Tg00^dj23Tg00E3j24!sS$bj2JTg00FOj1`!s/$oj1]Tg00`Bj2HTg00GOj1WTg00bJj4G!s8$mj1VTg00HKj1U!sS$`j2@Tg00J<j4=Tg00aCj1S!s8$gj2RTg00KIj2QTg00L5j3N!s/$Tj4M!t$$hj4?Tg0083j66Tg00h4j1D!s/$Sj2>Tg00i<j3E!s/$ej2KTg00jQj3OTg00k1j1PTg00d6j2_Tg00I6j2^!s8$Vj4ITg00eBj3\Tg00PKj7Y!s8$ej8X!se$Vj6ZTg00fIj7[Tg00U;R1f0R2g00U[R332p=:f1R4g00PoR5g00QNR6P6g00QnR7P2g00RNFYp=7f3R8P5P6P6P7f2R9P4P2GXp=9P4!s='P2EZp=Fg009@R:P4g00fmP2C=p=BP9!sL+4P2F[p=Ag00gTR59212p=Cg00RnR;/12R<1124R='<g00:WR>#TR?#LR@/89,0818@4RA'0108A1548P11;12f4RA,59=212P1f6RB,5A=212f9RCf8RD,8@RE'0f7RF,8@RG'0f5RH'310CG/3H521]0P4158HRG#:P01542RI#:1494[RJ14421594RK#:RL[1489\L1J42P4n20010!s#$12!s-%0X9:X<:PJ^9:^<:P2PHPFP4O3RJ14HFP1f:RL18@CR@'0RM/3BRNf;RO/0@/3F9212X41R@P113LBRPP@P1PP13OF=!sA%1;1P10LE/3BRPPLPDPBg00ShRO#`RQ%]ORRP:1H:9RSP4%W:CGRT%V:RU%U:RVP:1@:>RWg00TTRX1@:?R?C=,7VRY%S6R6PYC91RV7R7P2P91;131Q29#:dAN:;4CMR3b6b7b8X1:X2:14241449[^1:^2:P2PC!uc%b5RZC?E6PNPLPCPBp-0RNg00l:R[#DR\#D,>:1>:\1>:[5E:5E:g00lY'K=OOQPRP:PSP41H:8CGPUPVP:PWPX%P>,@:R>!u#$P6PV1FVH1B>?,7V5AVP!u4$C9P7P!tt0X;:W314291189,<A1498[!u%&^;:^3NP211;CPCPLPFP4PDO6b5C?E610M!w/$EPMPDPBP!uJ$b0b:W0%CGP0%CI1149[RI%CKRK\=1198R0\K1_!y5<>:X=:PI^>:^=:PJ11FHP1P5!xW$5A215!xT&5P!xM&PQPRPTPUPV1BW?,7VR?!ur$^:;/BW,7VRW1FVA!uw$AAVW?!uz83N11;4/<811;9/<0[\=!ux&!uu%CLPFPC!us$5b5R4CIE6P!un'!s4$!un%n01!uI%20101P2O1b0b4X?<XA:3\W@X9:XB:XC:o"). Qed.

Lemma Z_to_le_bytes_mod : ltac2:(zQ "b0!iid!ije!h8!pf!j6!lf!htb!ik4!ht2!hu4!la>1n$2>1z$5@3$3@1$1@1$a@1$4#8@2$0^2@2$6^1@2$9+2@2$7+8@1$8^2@2$0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##>yh01zh14__x1h21nh31xh47__arithh54__ffh68__varmaph75__with84cstrh91Hh:2b1h;2b2h<1yh=2IHh>1mp;1p;2p;3p;4p;<p;6p;7p;8p;Bg002;j1CTg002`j1uTg0000j1<Tg00Foj1JTg004gj1GTg00mER0j12Tg00MFR1j20Tg005Ej29!s/$bj26!sN$ej21!sr$Sj33j1eTg00BDj2?Tg00h4R2j1>!t$$Aj2@Tg00jQj2Xj1oj3YTg00WBj2;!sg$mj27Tg001Wj3fTg003>j2FTg00EOR3j25Tg00:<R4j2D!sE$dj28Tg00nbj3`Tg00oHj1N!s/$fj4_Tg010Il<I!s/$nj6^Tg011Wj1O!tj$Sj2HTg00i<j3]!s/$ej2\Tg012<j2[!v6$Oj1ZTg00`Bj2tTg00Gmj1sTg00HKj1rTg00I6j2B!sJ$`j2qTg00aCj1pTg00cSj3U!sw$hj3TTg00fIj7nTg00Jgj2lTg00KIj2kTg00L5j3i!s/$Tj4hTg013Kj4QTg0146j4gTg008Qj2P!s/$3j6ETg015>j8V!sw$<j4R!s8$[j3jTg00Nej6dTg016gj4mTg017Hl<W!s/$mlBcTg00PKj7bTg00eej8aTg009@R5f1R6f0R733p=41?57p=:g018SR8P8P5P5P2P0P0f3R2g0192f2R9P6P7M<Wp=M!sI&5!sI$5R0f4R:P2P!sH,L!sF&!s$%1P7P6P9P1P2P:P0f6f7f8f9MBcp=KP5P6g00fmP7CRp=A!s4$PoR1g00QNR;P;g00QnR<P7g00RNFbp==P2P1P;P;P<!tC%Gap=Sg00:WR=#CR>#C#CR?#uR@#<RA#JRB%G>R>%G?R?%26'0'9,67,16116733^05RCX28g00l:RD/17,?BX05PBPB%>9RE#2RF,0?RG,9>,67RH,@@RI,XA1@@7RJ,XA1;H?,191;7?,19PAPB\BRK%oARLPLPIPJPK\A/?Lg009^RL%<7RA%<6RKP4%<9?36717291726'4R4[17961797'4%<2?396[RJ%<:?329\4Af967P7n20010!s#$12!s-%0W;W:W2PJ^;K^:A^2LP7P@%>2RL#2RA,0?RK!u9$6RJ,@@R41@@6RIP51F@JRM1@@9,7@,47X05!s;$6RN%>:#2,0?!s^$9,F@/!sE%6PKP?g00RnRO/5?RP15?KRQ'D%22RR%G=RS'8RT,0?RU,5?RV,DPPPPQPPPVp-0/?P9`PP!y7$3P7X35RVP31567#NX<5X35P?P?%:?R3PKPUPV!s$$5P5g019V1067C_#:X>5X25RUP?P?P3PAPTPVPV%27#:X38RAPLPT187SRTX35RLP2PR%:RCMELM:KM<IE^%O2R215ORRQg00ShRW1H5DRX%>D#>,H59]5Xg00lY'\'[%ZWRX3YRD%JWRW1t56RY%s5RZ%r5R[1B5OR\1q5=R='A,=[R]%p;R^P[!zl'1B5?R;,A\,=[1B5S9U5=9T5;R1,A;,=[FnCS1l[<R<P7P9g00U;R_g00U[R`'?1k79=3_`dAi5O6ChR`b5b6b7X1515O7R_186S,0?,5?,DP[^15P7%20P6O2R0b4b8CQCg14MNe17@I1P@6EE17@41P@JEEO4b9GV%29RJ,0?/8?R@/4GR418JSRS,0?RI,4@P5P5%e5RNPVPN14!wt-@P@%:@PGPI!wr&!w['FPS!s6$APEPSPLP9PJ%:J!wJ,%O915OJPXPWPYPZP5AT5;=R==U5;g01::P1CR,=[P<P!ug-0?7/8?10?T'4!u`&:O1!u\%P4P510?RRR/8?R419>7,69/;?,1:1;9?,1:RT53!~A$51;6?R119>R'611:7=3BTX05P9P1O119>4,66/;?P2PQPD!tq&[P]P^1A\=,=[CS!tg36,5O\_^15P!w<$9jR6EEPKP7Edb9GV11EH11E753BeX05X=CX28P7CmX28o"). Qed.

Lemma low32_le_bytes : ltac2:(zQ "80!j6!la!ije!pf!iid!io1!hj7!hk8>1v@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$4N4@2$7@1$0#i0@1$6^1@2$5N4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_SymExec ()) ["FPX1"] "h01zh11vp;1p;2p;3p;6p;4g002;j10Tg002`j15Tg0000j16Tg000mj23Tg00Vdj1ATg00WBj28Tg003>j27Tg00Foj1<Tg00h4j12Tg00mej21Tg000Sj34Tg01:aj2;Tg00Xkj1:Tg0083j69Tg00V;j4@Tg00YOj4?Tg00ZAj1=Tg01;nj2>Tg00:W#0#0#0R0#0#0R1#0#5R2#6g009@R3%51R1f0R4,32R5g00ZiR6#A'8'7%50#6#<R0g00l:#2#2#2#2R7/14f1,32,17R834X03P3P51714,17=408X031;75g00Rn,85%:5E9P2P6P1P4C@,31P2P6P1P4C?E9%=4,31,171>74540eW1o"). Qed.

(* [comment removed for export] *)
Lemma step_sw_val : ltac2:(zQ "hf1!j6!la!pf!ip6!lf!is2!hsb!u9!isb!it1!it7!itd!iue!iv5!jg1!ije!jg8!jge!jk9!jl4!jm1!jmf!jnb!jod!jp5!io1!js7!jt5!jtc!hnc!khf&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h2>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h4^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h5^5$e>0@3$2@1$3@2$a$5$4@1$ha^6@2$8@2$a$5$4@4$h0$5$4@4$hc$hb^5^4^3+4>0@3$2$9@4$h8^c^9@2$7@2$6^b^6@2$d@1$0#c^4N4$h1@3$2@1$h6$b@2$h7^d@5$c?2fx^c^b^a^9@2$h3$b@5$c?2fx^c@2$7^b+4@3$he^a@2$7@2$6^c^7@2$d@1$0#c^5@2$h9N4@2$6^c^6^9").
Proof.
ltac2:(KReplay.run1z (kr_t_SymExec ()) ["FPX1"] "##bBp'0h01bh11oh23Hokh37Hdecodeh46Hecallh56Hfetchh63immh71lh83memh92pch:4regsh;3romh<3rs1h=3rs2h>4segsh?1wi001wi011ci026c_fcsri037c_fregsi044c_pci056c_!s8%6!s0$svi071ii083iszi092m'i0:1pi0;1ri0<6reporti0=3st'i0>1xp%0p&0p;1p;2p;3p;4p;5p;8p;6g00Foj1nTg002;j1=Tg00k1j1a!s8$`j1JTg0000j1ITg01=6k206!s0$bR0j1UTg01>Dj2\Tg01?Fj2K!sV$Sj30!s8$hj1fTg01@hR1j2ZTg01AHj1XTg01B9j4qTg004gj1o!s8$ej4STg01CEj2LTg00Ccj2FTg00<oj23Tg00h4j1QTg01DFj4ATg01EFR2j1]Tg01FNj1jTg01GUj5<Tg01HVj3_Tg01Ibj1RTg01J`j3mTg01Kej3hTg01Lkj3gTg00FOj1sTg01N0j1[Tg01O8j1eTg01P@j2YTg01;nj2?Tg01QJj3!v%$RLj1MTg01SKj1;Tg01TKj1WTg01ULj3r!s/$ok207Tg01Vmj1TTg01Wlj1:Tg01Xkj1OTg01Yij81!v/$Aj2dTg01[0j58!s/$Yj3cTg01\@j3bTg01]Kj2CTg01^Ok105Tg01_8k104!s0$bk10!vM$aCk102Tg01`Ik101Tg01a2j1}!s/$[j2GTg01bbj1lTg01c[j1HTg01dCj27Tg00[Gj3k!s8$mj3BTg01eRj1{Tg01fVj1zTg00ZAj1N!xg$mj2VTg00mej2PTg01gYj3DTg01h]j2ETg01iej3iTg01jRj1pTg00Nej6yTg00BDj2xTg01k\j1wTg0083j69Tg01l_j1vTg01mij3|Tg01o8j3uTg020>j1~Tg021;k200Tg0227j3`Tg00jQj3tTg00U;R3f0R4g00U[R530p=^f2R6g023>R7f1R8;`4'Ep=41E74p=>f4R9g024ER:f3R;P6P8CS;`4p=2P6g018SR<P8P4CSp=@f6R=f5R>/C91G849t;63`p=5g024n#ng00:WR?#=R@#a#JRA%=@R@#=RB#=#=RC#=#JRD#IRE+06RF%JB#IRG#U\ERH%JCRC#IRI%IAS00Q00%a?#=!sY$?#I%UIRJf8RK/\=1KI;30%f9g00gTRL503g025mRMg009@RN'ZRO#URP%X>PMPNg026YRQP9P;P6Cq%o@R@CS,KO30f;RRPKf:RS/L>1F?;'3g00l:#Q!s$%RTCA#^PJf7RU,KI%]7RVP0PI%j7RW#]RXP4f>RYp,2fxRZf=R[f<R\PRPSD<;_4R]P0PIPXPZP!s;$f9R^D<R_#RR`=m[RP!sF&Ah[`RP]P2P7PXAg[`Rg027E#sR]94W4S01%[WRa%eWRbn10110>00031010=0000!s:,2101!s8K,Y7PZP\13R@Rc1L\U1F?>Rd'31L\=,?T56SP^D<#>Re30X1JP3PLP2PWPVP3PXP4%M_%;_%W_%aB#og028JRB5rA-07_,KE%T_%:_P`%O_G1=4W]P0POPX%XKP1PMPNPXP4P21Z:HR`#jRLPXf@S021dD4S03PZf?RJPYP[P\D<Rf#M%;f%Wf%:f%TfD87c8%Rf3bP1P:PHPX1C`4Rf&058S04&048S05&038S06&02ERg&018S07%}8S08P4PZfBfAS09Q02PJD<#OG11G`6Rh54Wn20!vK'120!vW$9PaP!wB3<!vv$!sR%:!sR'7108RiP3PX%lK!s[$!w4%0020000Rj!wO/!s_%!sH011C74#>Rk%[7Rl%e7Rm!sX%;!tE0=0VeX03PP!vi$QP=P>P9CqS0:P!{C%!wp&!w:$P4PiP!tG6PkPlP!t,=1PP3%H=RP!sr&2PLPXP3%]LReP[PSP3PE%HURjg00RnRi,dDRQ17\URn!uk2oAk?D>5BDRpPTCAP`!s$$HP\P\%{ZRqPRPgPg%zZRrPSP^G1Rs#;1dD@Rt9BDRS0;%:sPgD8S0<P3PEPPPQ17\=Rs!t72u#N,VC,PTRv9DSpP]D2Rw1ZE<R<A@EpTP`PwF5,EL%[LRw!sc-100!ya'PfP:PFP8P9n01!|:%150105103104102106Rx!sK&;!sK?FP:PEP8P6!sK?yPgP:%UEP8P4!sN?zP:PIP8P8!sK?{P4P\G1R|=4Wh!{-O!xz=R}P\PqPcPgPgPr!wE$4PQP!xR2/3dRnP3PEArAiBRi9iA=S0=PQP!wj2!#3`&G1#>50VX03P3%H>S0>!t5/13odRd!t;+!sj>90V}!sk$Q0=!zT$nPTCA#^X03P4PP%p=S0?EyP\P^!yQ,R=!yO2P1F?9S0@'3!sd%PEPd!{]1PePYPRP4!{#0[P[PqP\!v9&RPSG1Rn#;S0AABD\t%:nS0BPgD8!v:%PjPQ17[U!~r3!zt+}9DR4!zt$sP<A@E4TP`Ps!zp$P!zm=xPFPyPgPzP{P4P[G1!xk;Rs!xmUP[Pq13\@!xm,%HKS0C!u@$K!u@11F?='3RB1?Tj56RS0DPSG1#>Rj!xX$EP3P5!vt44!vl+nADRB}!uu$}!uu$BTR5P`P}!uw9!uCV=0VjX03PHA6Sdv!tY&!vg'!tU+P!wI+P5!wF&C`!sE+JPJPqPY!v-&[!|}$s#;S0EABDYt%:sS0F!#4[$GP6!sp+!vW$SPQ17JS!vT4K'3R}=@ETR~!t?&G`94W|!x301!}x&!uTA1H%nGRG1?TuRs!uX;A6RB!u[%B!u[&B!u[0Q0GA6[}6!sI+~!sI&!te\7GPEPc!t^:[Q0AP4Q!|9%Q0D!tE$G!th&G!wE2Q0EP6Q!w%%!vt%^RG!vv$^!#3+396[!yf+!u:$}!u:_0E!#4Q-A6Sds!#42$Rs,xVQ0;%wRE9Pv%vuE9ADSdvRuA|vSdE9!uo9Q0<Pu!tn$u!{V$dTP`Pu!uf%!~31RG1R{!uz+YPYPqP[!zA&\!sD$z#;ABD[t%:z!v8'P!v5$Y^!z,4U'3RGP3PEQ!}~%Y!}~2!#4>&5D\!tl$z!tl$GTP`Pz!v_$!#A[2!v^Gs!#>s$dPTCAP4E9PpAuo?>E9b2AiA>i%p>E9Q0=Q0?!vN+!#3++\P^Ak?D99BDPRP!#7'/RPRPqPS!v+&^PKG1R?!v+$St%:?!v+'Q0>PQ17R>!ub99D^P!uc$]!uc$PTP`P]!#6xAA4W{!#<TiPRPq13S@R!#6g%1LR=Q0@'31LR>,?T56^RTPK!#;|%e!v>/Q0:PZPRPSP^PKD<R^#M%;^%W^%:^%T^D85ct%R^Rt5b\!u2,Q04Q05Q06PgQ07Q!#G;$!#H?$PRD<R>#O!#9?<!uVVZPRP@PTPKD<#>RK50Ve%XURTP8!x\+!#F'$T!#J>-!uV%3%M>%;>%W>%:>%T>!#Iv%>5bJ!uGBQ!#IX%PY!#IZ$!uGS!#IU6!#IS$U!#IS4!#H0QKe%fUP6E9A_\^U,Y7=0VKRUePUe1\\SP;E9!#P-$%~^R;,\\A_[_4R_!s;%Am\t;P!s3'h!s3%!#PP%\t;Q01!uJ6!#P=`!u&$200\^!s0$W2W3W4W5W6W=W<W?X;HW8X9EW:W>o"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : list Segment.

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

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
