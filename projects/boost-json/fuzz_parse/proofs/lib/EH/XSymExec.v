(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Footprint.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_XSymExec () := KReplay.lz_vm "##]|I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C!sc@;bv_unsigned!sPA5bv_eqK!t6+7Numbers7BinNums8positive02!sK=1N02!t5A7bv_wrapC56Stdlib6ZArith6BinInt1Z3ad!txB7Z_to_bv!tU>Z02!t/=pow!sC<6moduloC4!sF14ZdivAZplus_mod_idemp_lC89OSSVerify6Proofs:boost_json:fuzz_parse3lib2EH9XPropExec=!u}&64!sv#C13~~~C!xR78eq_ind_r!v2A@!v2&!x[+I!v;?0I!x0?!z'93and00!y6G3!v\Irc!v\R8XSym!v[#!uc'64!vb$_l!v^&!wT\6v_addi!sm%!te\:!sl%_lit!spb!uW3r!uWc7v_auipc!sn%!|G@3!|&<4landK!#47:1!tl]8jalr_tgt!{n'!{P?9bv_!#4~%!tw;>pow_pos_nonneg!sN<2lt!sB>e!sB<:!t-#!t&%!v,29Datatypes4list01I!sFA0K!|9'9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr01!sIE7K!t?L1C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!u~<4find!sqAC!sq0_soun!yQ=3mul!{I:x!uL-!s]&:Znumtheory<Zmod_div!#7v#!sh76!#7p$!#9&d32!#9&+K!w-<G!wR'4!wR<5eKind!za=uni!za9!se%4kind!yO#!sf@1!#3t?1!#9b74True!{G8!xF-;!wJ%!va$!tt8!zZ13Op205!uc=bool!#:~-!sF81!#4J@:bv_extrac!#3_<4of_N!#?f<shift!#;a\!y:'_32_64!#6N%!#4v;!t;%_0!#?DBC!uN,!#D|,ELinuxProcessSemantics5Riscv3Sem5low3!#D[@1!slA7Prelude4sext!v2\9!tV$!#=,+!tBJzext!}c]5!#>K#!wGB7testbi!yC=3ltb!yB=ltb_lt!#99?2!#7}D2!{Z<6op!xm#!#Gr=;!yX&spec!tV@!#?<<Amod_pow2_bits_low!u%E3!v2Ag!#=Q<B!t<1high!sR<9!sI$inj'!#6dE8!sJF5!#4SH3!#43A!ww=3na!xa9!t415Psatz!sOM6K!#7/L2!#AHA2!#J`F1!vkF3!u|A1!u&N1!ye=of_nat!#38:?!s<26BvBase=!#I5#le_bytes!#<m5;ZifyClasses!#>U#ff!#Oc8iff_refl!sjB3inj!sIB5mkre!snC9and_morp!{{44Znat5Nat2Z9is!#F{'!w%L3!~3E5!tkB;rew_!v/%v!#8Z[<!~^+low!#7D%3!#;A$7tac!xC#<f_equal_help!#O%\!#5p$8_!t?'!#U:7!zs,7nat_!#FJ8!x52app!yiC!sK$2I!|/@0!xQ>8inj_succ!t768!t7#Inst7Inj_Z_Z!#5'H1".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd4Npos35stdpp9bitvectorbdefinitionsjd2bvhd1Z46Stdlib6ZArith6BinInt1Zm33addjd7Z_to_bv37Corelib4Init5Logicob2eqjd7bv_wrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~qe6v_addiqe4btgtqe7v_auipcqe8jalr_tgtm34land3h5LinuxProcessSemantics5Riscv3Semhh95low32qe5v_addjdbbv_unsigned3h5LinuxProcessSemantics5Riscv7Preludehla5bvmap89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XSymExec7WithFP1~~~~~~ho93envqe4getrm36of_natm36modulom33powm36shiftrm32leob3and3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseig9dZ_to_le_bytes04listm33mul" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##,Dh01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g0000j16Tg000Sj38!s/$mj20Tg001Wj3@Tg002;j15!s/$`j1>Tg003>j23!s/$dj24Tg004Aj29!s/$gj1;Tg005Ej2=!s/$bj22Tg006Bj3?!s/$ij1:Tg0087j67!s/$Uj2<Tg009DR0f1R1f0R238p=1g009bR3%62R4%61R5g00:@f2R6#6?812f3R7/061071'1R8[10611062'1%67?861[R9f4#6?876\8A@612P2n20010!s#$12!s-%0W2W1W3P9^25^14^33P2g00:[#5R3#5!s$'R4#>R51356R9/41R8,95R:1461R;,95R<P01358R=1476R>,95,05,12X00!s@$;R?1357/46,35/!s>&%;3%;4'=R4,28135>R>!sY+2641426/24/1>!s9&;41274/4!s<%2X00A?614P?%:;E7P9%:6E7P=%:8E7105<1<5;!s0$:1<58E7O4b4X60X50o"). Qed.

Lemma Z_to_bv64_wrap_r : ltac2:(zQ "70!j6!lf!nb!o1!pf!la!q4>1a$1>1b$1@3$4@1$5@1$0#k0@2$3@1$0#k0@2$2^2@2$6@1$0#k0^1@2$3@1$0#k0@2$2^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##,Dh01zh12b1h22b2h31nh41Hh51ah61bp;1p;3p;2p;6g0000j16Tg000Sj38!s/$mj20Tg001Wj3@Tg002;j15!s/$`j1>Tg003>j23!s/$dj24Tg004Aj29!s/$gj1;Tg005Ej2=!s/$bj22Tg00;@j3?Tg006ij1:Tg0087j67!s/$Uj2<Tg009DR0f1R1f0R238p=1g009bR3%62R4%61R5g00:@f2R6#6?812f3R7/061071'1R8[10611062'1%67?861[R9f4#6?876\8A@612P2n20010!s#$12!s-%0W2W1W3P9^25^14^33P2g00:[#5R3#5!s$'R4#>R51351R9,46R8,95R:1461R;,95R<P01358R=1476R>,95,05,12X00!s@$;R?1356,47,35/!s>&%;3%;4'=R4,28135>R>!sY+2141472/24/1>!s9&;41264,47!s<$2X00A?164P?%:;E7P9%:1E7P=%:8E7105<1<5;!s0$:1<58E7O4b4X60X50o"). Qed.

(* [comment removed for export] *)
Lemma v_addi_lit : ltac2:(zQ "70!j6!lf!o1!pf!ud!nb!la>1p$1>1i$1@3$3@1$6@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##%ch01ih11ph21zp;1p;2p;3p;6g002;j10Tg002`j1;Tg003>j2:Tg0000j14!s8$dj22Tg004Aj21!sA$Sj33Tg00;gj29!s8$mj25Tg008Uj26!s/$7j67Tg00=7j28Tg009DR0P0g00:[#0!s$-;R1f1R2':%41R3f0R4/22,11f2!s-%33X2019241112R5,511612E718541224,11533eX00W1o"). Qed.

Lemma btgt_lit : ltac2:(zQ "70!j6!lf!o1!pf!v6!nb!la>1p$1>1i$1@3$3@1$6@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$5^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XSymExec ()) ["WithFP1"] "h01ih11pp;2g00>>j20Tg009DR0f1f0'0X00W1o"). Qed.

Lemma v_auipc_lit : ltac2:(zQ "70!j6!lf!o1!pf!vd!nb!la>1p$1>1i$1@3$3@1$6@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$5^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##%ch01ih11ph21zp;1p;2p;3p;6g002;j10Tg002`j1;Tg003>j2:Tg0000j14!s8$dj22Tg004Aj21!sA$Sj33Tg00?Hj29!s8$mj25Tg008Uj26!s/$7j67Tg00@Xj28Tg009DR0P0g00:[#0!s$-;R1f1R2':%41R3f0R4,22,11f2!s-%33X2019421112R5,511612E718541242,11533eX00W1o"). Qed.

Lemma jalr_tgt_lit : ltac2:(zQ "90!j6!lf!o1!pf!hg7!nb!hh2!la!q4>1z$1>1i$1@3$3@1$7@1$0#k0@2$4@2$2@1$0#k0^2^1@2$2@1$0#k0@2$6@2$5@2$8@1$0#k0^2^1-2").
Proof.
ltac2:(KReplay.run1 (kr_t_XSymExec ()) ["WithFP1"] "h01zh11ip;1p;2p;3p;6g002;j10Tg002`j1=Tg003>j25Tg0000j16Tg003dj23Tg00A`j1;Tg00B>j22Tg004Aj21Tg000Sj34Tg00B\j27Tg000mj28Tg008Uj29Tg0087j6:Tg00C6j2<Tg009DR0P0g00:[#0R1#0#0#0#0#0#=R2f1R3'5R4%62R5f0R6/33%;1R1'2,12f2,52/33/21,1234X001346/21,12R1,751123R4,821923E:1<46=451eX10W0o"). Qed.

(* [comment removed for export] *)
Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##$Dh01bh11np;1p;2g0000j11Tg002;j10!s/$`j13Tg00D?j22Tg004Aj25Tg00B\j24Tg009bf0R0#1g00:[#0!s$-3R1#1f1/20,51'4W0W1o"). Qed.

Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##$Dh01bh11np;1p;2g0000j11Tg002;j10!s/$`j13Tg000mj22Tg004Aj25Tg00B\j24Tg009bf0R0#1g00:[#0!s$-3R1#1f1/20,51'4W0W1o"). Qed.

Lemma bv_wrap_32_64 : ltac2:(zQ "40!j6!q4!lf!pf>1z$2@3$3$2@2$1@1$0#i0@2$1@1$0#k0^1@2$1@1$0#i0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##0zh01zh12Hah27__arithh34__ffh46__sat0h5!s/%1h68__varmaph75__witp;1p;2p;3p;4p;6p;7g002;j11Tg002`j1ATg003>j24Tg004gj18Tg005Ej2B!s/$bj20Tg000Sj32Tg00B\j25Tg00Dgj2<Tg00EOj26!s/$kj23Tg00FGj3:!s/$kj1CTg00GKj1P!s/$kj1OTg00HIj1N!s/$gj1MTg00IRj2>Tg00J5j3?!s/$Xj4=Tg00KCj2L!s/$ej2KTg00LQj3JTg00M0j4I!s/$bj2;Tg00N?j4G!s/$Yj6HTg00OAj6F!s/$]j1@Tg0087j67Tg006ij1ETg00Pkj7DTf1R0g00QOg00QnR1P1g00RNR1f0R2g00RnFDp=9g009DR3P3g00:[#1R4#1!s$%R5#1R6#AR7/42R8%84R4%85R9'BR:'0%A5R5/40R;9232X03P3%86R6,B4R<,02R=102:R>=23;!sD$P>100</0:=!sV'!s8$:!se&153>10=:P:P<P21<49g00SNR=/64R>13=916=:R;[[13=4R?g00SlR@A:490UW113=:\@^1?g00THR9#CRA%P9R9%O3RB%N3RC%M3RDP31>3=REg00U4RF1>34RG=?35C='91LD1R1P2f2RHg00U[RIg00V;RJ'51K2H=2IJdAJ3=0CIRJb3b6b7P;P2b2b4b51<4613=616=<R;[\>A:460V@X1?13=<!tl$PAP9PBPCP3PEPFA?3G7C=,9DP1P!sv4P31;2:923<X03P:1;::,53CGEHEF1452%@2E7P8%E2E71458%@8E7W0o"). Qed.

Lemma low32_lit : ltac2:(zQ "60!j6!o1!pf!lf!hjb!la>1z$3@3$2@1$5@1$0#i0@1$4@2$1@1$0#k0^1@2$1@1$0#i0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XSymExec ()) ["WithFP1"] "h01zh12b1h22b2h31nh41Hp;1p;3p;2p;4p;6g0000j12Tg000Sj30Tg000mj21Tg001Wj3;Tg002;j13Tg002`j19Tg004Aj25Tg00V[j4=Tg00WDj1<Tg00Wbj28Tg003>j24Tg00XBj1:Tg008Uj27Tg0087j66Tg00YOj1@Tg00Z3j4?Tg00Zej1>Tg009DR0g009bR1f0R2#2R3f1R4#2R5g00:@f2R6#2?042f3R7/161174500R8[11641162500%27?064[R9f4#2?076\8A;642P2n2001000000120000000W2W1W3P9^25^13^31P2g00:[#3#3#3#3#3R1#9R3%31#9R1g00[MR5P31514R9C=R81534R7P01119R:%<5'8,431536,13R;9002X00P0P:1432=00;X00R;P01414P;P014341416,43=002X00%:411371734E6P:1714E6g00SN,8:%@:E61138P1P5P3P9C?E6O4b4%231512#>153230eW0o"). Qed.

Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof.
ltac2:(KReplay.run1 (kr_t_XSymExec ()) ["WithFP1"] "h01bh11np;1p;2p;3p;6g0000j11Tg002;j10Tg002`j12Tg00D?j24Tg004Aj23Tg00[kj3:Tg000Sj39Tg00B\j25Tg00Zej16Tg00\Vj17Tg0087j68Tg009bf0R0#1g00:[#0#0#0#0#0R1#2R2#1R3f1R4/40R5,32R6f2?:24=930X031536%01#2/35#6%75E8W0W1o"). Qed.

Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof.
ltac2:(KReplay.run1 (kr_t_XSymExec ()) ["WithFP1"] "h01bh11np;1p;2p;3p;6g0000j11Tg002;j10Tg002`j12Tg000mj24Tg004Aj23Tg00]_j3:Tg000Sj39Tg00B\j25Tg00Zej16Tg00\Vj17Tg0087j68Tg009bf0R0#1g00:[#0#0#0#0#0R1#2R2#1R3f1R4/40R5,32R6f2?:24=930X031536%01#2/35#6%75E8W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_add_lit : ltac2:(zQ "80!j6!o1!la!pf!lf!hk4!nb!hkc>1u@1$2@1$0#k0>1x$4@3$3@1$2@1$0#k0@2$5^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6@2$7@1$0#k0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##%mh01uh11xh21zp;1p;2p;3p;6g002;j10Tg002`j1;Tg0000j1:Tg003>j25!s8$mj23!s8$dj22Tg004Aj21!sA$Sj34Tg00?Hj29Tg008Uj26!s/$7j67Tg00^Jj28Tg00:[#0!s$-;R0#:R1g009DR2P2f0R3,50f2,30R4/23,10f1R5,24,10541X221305R2/931103R4,301603E7185412!sY$541eW1W0o"). Qed.

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

Definition E0 : ltac2:(zQ "40!j6!ho0!hsf!la>4regs@2$1@1$0#5@1$3@1$0#k0$2") := ltac2:(zQ "70!j6!h8!ho0!ht6!htd!o1!la\4regs@2$2@1$0#5@1$6@1$0#k0\1n$1@2$3^2@2$5@1$0#5@1$4^1").

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
Lemma shiftr8_mod_pow2 : ltac2:(zQ "70!lf!hu6!huf!hv5!pf!nb!hve>1k$0>1z$0>0@2$6Z^2@3$4$0@2$3@2$1^2@2$2+2@2$5^3+8+8@2$1@2$3^2+8@2$2+2^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##:Xp'0h04__x1h14__x2h23Hlth37__arithh44__ffh58__varmaph65__with71bi001bh81Hh91mh:1nh;1xh<1yh=2Hih>2Hkh?1ih@1khA1zp;2p;1p;3p;4p;6p;7p;8g00Ekj23Tg002;j1ATg004gj1ETg003dj21Tg00Wbj24Tg00_Pj20Tg00`1j2:Tg00B\j2;Tg00EOj25!sA$Nj2LTg00Fkj1^Tg00GKj1[!sA$nj2JTg00HIj1V!s/$gj1UTg00IRj2HTg00aLj2F!s/$oj1TTg00KCj2S!s/$ej2RTg00LQj3QTg00M0j4PTg00bQj4CTg0087j67!tC$kj1OTg00c6j4NTg00JXj4?!s8$Tj4BTg00d?j3D!s/$bj2MTg000Sj3=Tg00:@R0j2GTg00eBj4K!s/$nj3]Tg005Ej2\!s/$bj2ZTg00Pkj7YTg00fQj8XTg00g5j7WTf2R1f1R2f0R3'\'Zp=2g00U[R4?=23p=9g00V;R59=43p=<g009DR6P2g00gYP3C?p=>!s4$QOR7g00QnR8P8g00RNR9P3g00RnFYp=8f3R:P7P8P8P9P1P2P3GXp=6g00h@R;!t,%@P1!sI+2P3FWp=Ig00SNR7/32R<g00:[R=#AR>#ER?%A>#A#ER@,11RA522/4@142@?2?11373RBP4f4RC/1@92:?RD112@RE'014C@f5RF72?/01,93X741:2CP41;431:1F/93P4f7RG,:C/93f8!sl&G?11F@'014G@?2?C/0F'9]2P2f6RH,::RI#<P01:23RJ#<1512[RK15231:12RL#<RM[15:1\M1L23P2n20010!s#$12!s-%0X96X:6PK^96^:6P3PFPCP2O3RK15FCP411H@RM,0CRNf9RO/4@f:RP!uB$G!uB%RQP414C@RR/0HRS11G@,0O/!sB%TP4PNPT1;4NPSPCP@PHg00THRS#^RN%[SRS1J62%V6RT%U6RU1H67RV1F6=R='>,8URW%T8R8PWC61SU9R9P3P11;451R31#<dAQ672CPR5b4b5b6X06RXP<\B^06RBP3PGPHO2b3CCE7A2R?O/0HRYPRPOPHPNPSP61J61P2%O6CNRZPTPUP6P=g00U4R[1F6>R>C?,8UR\P8P\C6P9P!t9,X161532R]1521[^06^16P3PPPG!vb$^b3CBE711O@R_92C?/0MR?PCP_PM!tK$!t>%\P8P61H6@R\9D6=R`P[AD6>\R\!tH$!tB7EA\]!t=&!t3&b2b8W2%@IP0%@J1321[RJ1332R0%@LRL[131:RI\L1M!xz<<6X;6PJ^<6^;6PK13CFP4P;PQP4P;A=4;!zz$;4;P!v`/!u;$1>=!wt$>P8PUPWP8AIUW>C6!u36371/GI\<\0!vO+GPPP2PCO4RPb3CKE7P!vD5!t$+1>V`,8U1>`\,8U5IU!t4:A11:@,3A'G!t:-!t-&!vL%n01!uz%20101P3O1b2b714D@/02PDP@P2PXPBP3P1P2!y\'W=X?63]W>XA6X@6o"). Qed.

Lemma mod_pow2_low : ltac2:(zQ "60!lf!hu6!huf!hve!ig3!pf>1z$0>1k$0>1m$0>0@2$4@2$3Z^1@2$3^1^2@3$5$0@2$1@2$1^4@2$2+2^3@2$2+2^2@2$1^4@2$2+2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##9xp'0h03Hlth14__x1h24__x2h34__p1h41bi001bh57__arithh64__ffh78__varmaph85__with91mh:1Hh;4__x3h<1nh=1xh>1yh?2Hih@2HmhA1ihB1khC1zp;2p;1p;3p;4p;6p;7p;8g00Ekj21Tg00:@R0j2<Tg002;j1TTg004gj1LTg005Ej28!s/$bj20Tg00`1j25Tg00B\j2;Tg000Sj32Tg00_Pj23Tg00EOj24!sS$Nj2JTg00Fkj1`Tg00GKj1]!sA$nj2H!s8$kj1WTg00c6j4GTg00HIj1V!s/$gj1UTg00aLj2@Tg00JXj4=!s8$oj1STg00KCj2R!s/$ej2QTg00LQj3NTg00M0j4M!t$$Tj4?Tg0087j66Tg00h`j1DTg00i?j2>!s/$hj3ETg00jQj2KTg00k=j3O!s/$]j1PTg00dbj2_Tg00IRj2^Tg00eBj4I!s/$nj3\Tg00Pkj7YTg00fQj8XTg00lBj6ZTg00g5j7[Tg00U[R1f0R2g00V;R332p=:f1R4g00QOR5g00QnR6P6g00RNR7P2g00RnFYp=7f3R8P5P6P6P7f2R9P4P2GXp=9P4!s='P2EZp=Fg009DR:P4g00gYP2C=p=BP9!sL+4P2F[p=Ag00h@R59212p=Cg00SNR;/12R<1124R='<g00:[R>#TR?#LR@/89,0818@4RA'0108A1548P11;12f4RA,59=212P1f6RB,5A=212f9RCf8RD,8@RE'0f7RF,8@RG'0f5RH'310CG/3H521]0P4158HRG#:P01542RI#:1494[RJ14421594RK#:RL[1489\L1J42P4n20010!s#$12!s-%0X9:X<:PJ^9:^<:P2PHPFP4O3RJ14HFP1f:RL18@CR@'0RM/3BRNf;RO/0@/3F9212X41R@P113LBRPP@P1PP13OF=!sA%1;1P10LE/3BRPPLPDPBg00THRO#`RQ%]ORRP:1H:9RSP4%W:CGRT%V:RU%U:RVP:1@:>RWg00U4RX1@:?R?C=,7VRY%S6R6PYC91RV7R7P2P91;131Q29#:dAN:;4CMR3b6b7b8X1:X2:14241449[^1:^2:P2PC!uc%b5RZC?E6PNPLPCPBp-0RNg00lfR[#DR\#D,>:1>:\1>:[5E:5E:g00mE'K=OOQPRP:PSP41H:8CGPUPVP:PWPX%P>,@:R>!u#$P6PV1FVH1B>?,7V5AVP!u4$C9P7P!tt0X;:W314291189,<A1498[!u%&^;:^3NP211;CPCPLPFP4PDO6b5C?E610M!w/$EPMPDPBP!uJ$b0b:W0%CGP0%CI1149[RI%CKRK\=1198R0\K1_!y5<>:X=:PI^>:^=:PJ11FHP1P5!xW$5A215!xT&5P!xM&PQPRPTPUPV1BW?,7VR?!ur$^:;/BW,7VRW1FVA!uw$AAVW?!uz83N11;4/<811;9/<0[\=!ux&!uu%CLPFPC!us$5b5R4CIE6P!un'!s4$!un%n01!uI%20101P2O1b0b4X?<XA:3\W@X9:XB:XC:o"). Qed.

Lemma Z_to_le_bytes_mod : ltac2:(zQ "b0!ij8!ik9!h8!pf!j6!lf!hu6!ikf!htd!huf!la>1n$2>1z$5@3$3@1$1@1$a@1$4#8@2$0^2@2$6^1@2$9+2@2$7+8@1$8^2@2$0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XSymExec ()) ["WithFP1"] "##>yh01zh14__x1h21nh31xh47__arithh54__ffh68__varmaph75__with84cstrh91Hh:2b1h;2b2h<1yh=2IHh>1mp;1p;2p;3p;4p;<p;6p;7p;8p;Bg002;j1CTg002`j1uTg0000j1<Tg00GKj1JTg004gj1GTg00n1R0j12Tg00MbR1j20Tg005Ej29!s/$bj26!sN$Qj21!sr$Sj33j1eTg00B\j2?Tg00h`R2j1>!t$$Aj2@Tg00k=j2Xj1oj3YTg00Wbj2;!sg$mj27Tg001Wj3fTg003>j2FTg00EkR3j25Tg00:@R4j2D!sE$dj28Tg00oNj3`Tg0104j1N!s/$Rj4_Tg0115l<I!s/$Zj6^Tg012Cj1OTg00i?j2H!s/$hj3]Tg00jQj2\!sJ$hj2[Tg00Fkj1ZTg00`nj2tTg00HIj1s!s/$gj1rTg00IRj2BTg00aLj2q!s/$oj1pTg00d?j3UTg013Tj3TTg00g5j7nTg00KCj2l!s/$ej2kTg00LQj3i!w6$0j4hTg0147j4Q!s/$bj4gTg008Uj2P!s/$7j6ETg015nj8VTg00JXj4RTg016Kj3jTg00OAj6dTg017[j4mTg018<l<W!s/$alBcTg00Pkj7bTg00fQj8aTg009DR5f1R6f0R733p=41?57p=:g019GR8P8P5P5P2P0P0f3R2g019ff2R9P6P7M<Wp=M!sI&5!sI$5R0f4R:P2P!sH,L!sF&!s$%1P7P6P9P1P2P:P0f6f7f8f9MBcp=KP5P6g00gYP7CRp=A!s4$QOR1g00QnR;P;g00RNR<P7g00RnFbp==P2P1P;P;P<!tC%Gap=Sg00:[R=#CR>#C#CR?#uR@#<RA#JRB%G>R>%G?R?%26'0'9,67,16116733^05RCX28g00lfRD/17,?BX05PBPB%>9RE#2RF,0?RG,9>,67RH,@@RI,XA1@@7RJ,XA1;H?,191;7?,19PAPB\BRK%oARLPLPIPJPK\A/?Lg009bRL%<7RA%<6RKP4%<9?36717291726'4R4[17961797'4%<2?396[RJ%<:?329\4Af967P7n20010!s#$12!s-%0W;W:W2PJ^;K^:A^2LP7P@%>2RL#2RA,0?RK!u9$6RJ,@@R41@@6RIP51F@JRM1@@9,7@,47X05!s;$6RN%>:#2,0?!s^$9,F@/!sE%6PKP?g00SNRO/5?RP15?KRQ'D%22RR%G=RS'8RT,0?RU,5?RV,DPPPPQPPPVp-0/?P9`PP!y7$3P7X35RVP31567#NX<5X35P?P?%:?R3PKPUPV!s$$5P5g01:J1067C_#:X>5X25RUP?P?P3PAPTPVPV%27#:X38RAPLPT187SRTX35RLP2PR%:RCMELM:KM<IE^%O2R215ORRQg00THRW1H5DRX%>D#>,H59]5Xg00mE'\'[%ZWRX3YRD%JWRW1t56RY%s5RZ%r5R[1B5OR\1q5=R='A,=[R]%p;R^P[!zl'1B5?R;,A\,=[1B5S9U5=9T5;R1,A;,=[FnCS1l[<R<P7P9g00U[R_g00V;R`'?1k79=3_`dAi5O6ChR`b5b6b7X1515O7R_186S,0?,5?,DP[^15P7%20P6O2R0b4b8CQCg14MNe17@I1P@6EE17@41P@JEEO4b9GV%29RJ,0?/8?R@/4GR418JSRS,0?RI,4@P5P5%e5RNPVPN14!wt-@P@%:@PGPI!wr&!w['FPS!s6$APEPSPLP9PJ%:J!wJ,%O915OJPXPWPYPZP5AT5;=R==U5;g01:nP1CR,=[P<P!ug-0?7/8?10?T'4!u`&:O1!u\%P4P510?RRR/8?R419>7,69/;?,1:1;9?,1:RT53!~A$51;6?R119>R'611:7=3BTX05P9P1O119>4,66/;?P2PQPD!tq&[P]P^1A\=,=[CS!tg36,5O\_^15P!w<$9jR6EEPKP7Edb9GV11EH11E753BeX05X=CX28P7CmX28o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
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
End WithFP1.
(* [comment removed for export] *)
