(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv F_memset AllocWalkKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AW_Leaves AW_PoisonShadow AW_SysconfPg AllocTacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AW_PoisonRemap1 () := KReplay.lz_vm "##9`K47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!sg+4Init9Datatypes6op!sL#!sH>4list00i89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As?AW_PoisonRemap14RENV00C13~~~C!ssO3Lib5Frame5munch!siawmono!si%!wAG1!t6Z=disjoint_from!t>C1Z02C!sD+5Lists7!s+#Def3map!tST4TacX2wz!tG3!xJ81!t,Zb8!t,&!vATCells4cell04!sj%k!yuh1!t_f1!yvZ4Step8rw_!sl#s!w?H2C!twY:!t1$_size!t{&56Stdlib6ZArith6BinInt1Z6of_nat!{'ZB!uD'_transport!v;V2As5ASegs5aseg!v8&I!wi_!#3L%I!|^?0!~<G3!u?S8AsShadow3mem!#47_3ivl!vkY8AllocRep9AGOT_VALS!#3fE1".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~0ddisjoint_from37Corelib7Numbers7BinNumskb4Npos35stdpp9bitvectorbdefinitionsmb2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_PoisonRemap1~~~~~~od4RENV37Corelib4Init9Datatypest94listt96option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hg15asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hk53mem03ivl05munch05wmono" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Record RENV (g : word) (b244 : byte) (m : mem) : Prop := mkRENV {
  re_got  : rw_cells asegs m 1791352 (map (fun v => C8 (wz v)) AGOT_VALS);                       (* [comment removed for export] *)
  re_shb  : rw_cells asegs m 1835576 [C8 (wz 2147450880)];                                      (* [comment removed for export] *)
  re_hme  : rw_cells asegs m 1838880 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];           (* [comment removed for export] *)
  re_thresh : rw_cells asegs m 2432480 [C8 (wz 0xffffffffffffffff)];                                       (* [comment removed for export] *)
  re_mlim : rw_cells asegs m 2432504 [C8 (wz 0)];                                               (* [comment removed for export] *)
  re_dd   : rw_cells asegs m 2432579 [C1 (b8 1)];                                               (* [comment removed for export] *)
  re_madv : rw_cells asegs m 2432604 [C1 b244];                                                 (* [comment removed for export] *)
  re_rms  : rw_cells asegs m 1799584 [C8 (wz 1727016)];                                         (* [comment removed for export] *)
  re_psc  : rw_cells asegs m 2424032 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_lpg  : rw_cells asegs m 7423640 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_ssp  : rw_cells asegs m 1794856 [C8 (wz 7423000)];                                         (* [comment removed for export] *)
  re_grd  : rw_cells asegs m 7423000 [C8 g]                                                     (* [comment removed for export] *)
}.

End HCW.

(* [comment removed for export] *)

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma renv_transport : ltac2:(zQ "b0!jc!m4!o8!t2!v1!v8!hjc!ho3!hoa!hof!hp6>1g@1$2@1$1#k0>1b@1$2@1$1#8>1m$7>2m'>0@1$2@1$1#k0@1$5@1$2@1$1#8>1W@1$4$8>0@3$3^5^4^3>0@3$9^2^4^3>0@3$a$6^5^4>0@3$0^4+hrlln8+n8>0@3$0^5+hsgij8+8>0@3$0^6+hsgvi0+h8>0@3$0^7+ilhtu0+8>0@3$0^8+ilhtv8+8>0@3$0^9+ilhuk3+1>0@3$0^a+ilhulc+1>0@3$0^b+hrnlq0+8>0@3$0^c+ikvsu0+8>0@3$0^d+nhkmp8+8>0@3$0^e+hrmji8+8>0@3$0^f+nhkkh8+8@3$3^h4^h3^h1").
Proof.
ltac2:(KReplay.run1z (kr_t_AW_PoisonRemap1 ()) ["HCW2"] "##>ep'0h01Eh12MUh21Wh32WMh41bh51gh61mh72m'h86re_dd0h97re_got0h:!s0$rd0h;7re_hme0h<7re_lpg0h=8re_madv0h>!s1$lim0h?7re_psc0h@7re_rms0hA7re_shb0hB!s0$sp0hC:re_thresh0hD1vi005!tO$i016!tO%i02!s0$rdi036!tO%i046!tO%i057!tO&i067!tO&i076!tO%i0!uH$rmsi096!tO%i0:!s0$spi0;9!tO+p;1p;3p;4p;?p;:g0000j11Tg000Uj1KTg0013j1H!s/$Vj1XTg0028j1V!s/$XR0j3OTg003ej3UTg004hj3TTg005kj10Tg006Pj37Tg007[j1<Tg0089j4L!s/$Uj1=Tg009Tj1JTg00:4j1STg00;3j1ETg00<7l?PTg00=Dj1ITg00>Hj4RTg00?Mj3B!s/$mj1GTg00A5j1M!s/$Ul:WTf0R1#1#1p=2%11#0p=4%0!s6$3%01#0#0#0p=C%1!sL$#<p=6!s>$p=5%1!s6$F!sB'1p=@%=1#Ip=Ng00BeR2f2R3f1R4P1CRp=9!sx+!s$'p=?g00CgR5%I4;B1p=;AB541p=Ag00DkR6%<!s>%>AB6419B63p=D%G1#M9734p=:P2P1P4P3f3R7f4R8f5R9f6R:f7R;f8R<M:Wp=8!sX$p=Qg00EIR=#2R>#1R?#1#2R@#K#HRA%K?#HRBg00En%XB\Ag00G1#VAO873AU473AT287%0=R2#1RA#0RB#0RC#4RD#1#3!s$$C#6RE%02R2#0RF#6577%12#2R2!t9$G#1#4#2#4#5#6RH%<?R?578%0G#5#3#4RG#1RI#1#6RJ%1A#F579%3>R>#0!s\%RA#4RK#0#5RL#2#6RM=7:?%5L#6RL=7;?%0A#2#3RA#1#2#5#<RN%<=R=57<f9RO%5A#3#FRA;7=f:RP%0DRD!u0$5RQ#1RR!t7$6RS;7?f;RT%1>#5#C#2#5!tS&6RU;7?f<%02!uA%R2#0!s0$5#6RV;7?f=%2D#4#3#4#4#6RD;7?f>RW%12#@!sL$2;7?P0fCR0fBfAR?fD?O0?PWfMRWP6P5%N1XD6R?g00H2CLR079EfNRX%CF#?RF#@!s$$6#=%J5RY';RZ79HfOR[%0F!t}$?#?!sO$<#=g00I;#NR\1A\YR\'A';R]79JfPR^%0F!sQ$<#=/;YRF79MfQR_?9L\fRR`%S=#E/AYRa79NfSRbfTRc!s8$79A%2B#3#5!x=&4#6!sj%B99cSfURd%1@#2!s<'@79UfV?9V@fWRe%=2/;YRf79DfXRgfZRh/;Y792f[RiPhPgPefYRjPgPEP0PTPdPcPbP6P5P?%0QRQ#4R?#0#6%4KRK!x'$2%5C!w8$3!wN$3#2%0I#6%0G#@%4R!s7$@?%3Q!s0$1K!sJ$F%4>!s6$J6'>5D='>'>'>9DJS'>5DH'>'>5DUCL9:eEeA:eE0eM98PePjPgPHPZPP!th$`A:eHZRZePZ!sF-JP]PO!sF$_A:eJ]R]eP]!sF-MPFP<!sF$^A:eMFRFePF!sF-LP\P;!sF$[A:eL\R\eP\!sF-NPaP:!sF$XA:eNaRaePa!sF-A%Eh/AYRhP9!sL$WA:eAhRhePh!sL-SPBP8PdPcfLA:eSBRBePB!sF-UP@P7!sF$K%Q@RB97eURUePU!sJ-VP@P3!sJ$JA7eV!sj4DPfP4!sF$IA:eDfRfePf!sF-21;iYRiP1!sJ$HA:e2iRiePieM98M?PW:WBW<W?W@W=W8W>WCW;WAW9PTPPPOP<P;P:P9P8P7P3P4P1O<n300010!s#$1<110110910310;10610010510810710410:102U!s#-W3W1W0W2W7W6W4W5o"). Qed.

End HCW2.

Ltac renv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with RENV ?g ?b m =>
      region_table; region_hull_memo W;   (* [comment removed for export] *)
      assert (E' : RENV g b m');
      [ apply (renv_transport g b m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)

End HCW3.
(* [comment removed for export] *)
