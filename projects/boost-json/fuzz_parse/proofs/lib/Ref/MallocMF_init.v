(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes SysStep Exec Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv AllocTop MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMallocRep MallocMF_klink MallocMF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MallocMF_init () := KReplay.lz_vm "##6?K47Corelib7Numbers7BinNums8positive01!sKG2!sK=1Z!sD/4Init5Logic2eq01C4ELinuxProcessSemantics?!s<23RunAsegments_reserved!sdK5State<!s]'_topI!ta;0I!uA?0!v+G3C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Ref5RSegs5rsegsC13~~~!vo>N02I45stdpp9bitvector;definitions2bv!u=/!uW$9Datatypes4prod!sF?list!u_/!sf81K!sfA!sFC2C!sF;3fst!sC=snd!v|P4Spec4KInv4went!v{%!t,,5Lists7!s+#Def3mapC!vy@DZ_to_bv_obliga!s:#_1K!wTD1c!y$S=MallocMF_!sn#<ref_!{e'!u:&!u|UProg9!{k'Z!v%'!|QO:!t[#_model!s_Q8with_ti!}iR9m_vm_lazy!s^QA!s^$materialized!#4173and01I!taQ!s7#Input00".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib7Numbers7BinNumsh81Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runj5h1segments_reserved3h5LinuxProcessSemanticsfLinuxProcessSem5Staten6creserved_top79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~r35rsegs37Corelib4Init9Datatypesv74listv74prodv74consv74pairv73nilh84Npos35stdpp9bitvectorbdefinitionshj82bvv73fstv73snd37Corelib5Lists7ListDefhm73map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefdMallocMF_init~~~~~~ho5cref_segments79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~ht94went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ihd9reservedZn69ProcInputn6ainit_modeln68with_tid79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~ioa5mminv" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma reserved_top_ref : ltac2:(zQ "50!h4!j1!m1!q4!uf@3$0$1@1$3@1$2$4+hitgg0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_init ()) [] "##$[p;1p;2p;3g0000j12Tg000Uj11Tg001:j13!s/$Xj27Tg0022j16Tg0030j15!s/$kj34Tf0#1#1p=0g004ER!s,$c#0#2#1#2!s+&0!s$-3R1'7g005H#6#5=401do"). Qed.

(* [comment removed for export] *)
Definition ref_segments : ltac2:(zQ "30!j1!hgf!hh6@1$1@2$2$0$0") := ltac2:(zQ "50!j1!hh6!hhd!hi4!hib@3$2@2$1$0$0@4$3$0$0+hggg0+jngg0@3$2@2$1$0$0@4$3$0$0+kngg0+qqgg0@3$2@2$1$0$0@4$3$0$0+vhgg0+ogg0@3$2@2$1$0$0@4$3$0$0+vpgg0+jkgg0@1$4@2$1$0$0").
Lemma segments_reserved_ref : ltac2:(zQ "d1!j1!hh6!hj1!hl5!hlb!hgf!hm1!h4!hne!m1!hs9!uf!ih5&@2$1@1$3@1$2#k0@1$3@1$2#k0@3$7@1$5~0@1$9$b@4$8@2$1$0$0~0\1p@2$1$0$0@2$c@3$4$0$0^1@3$6$0$0^1$a").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_init ()) [] "##,Hh01pp;1p;2p;4p;3g000Uj10Tg006Kj1=!s/$ij1;Tg007Lj2:!s/$lj1ETg001:j12Tg0000j11Tg008Lj47!s/$lj1GTg009Lj38!sS$Xj2FTg0022j1D!sA$lj3BTg00:Ij3?!s/$fj2>Tg00;hj4@Tg003kj3ATg00<Dj2<Tg00=7j3CTf0R0#0#0p=6%0!s0$!s$,p=4f3f2f1/<03Cp=3!sH+p=5%1!s-$9g004cR1#0R2#6R3#0#6R4#=R5#;R6/:6R7#ER8P6P6P5%04#4R4#0#2R9P5P9C3P5%11R1#0#1R9#1#1#5#4#2R:P5P:C3C7!s`&13!sC-3P5P3!sb$92#9#9!s=&2P5P2!sZ/1#!t%%6!s`+!sI&P5%24R4P5P4!sV1!sP,1P5P1!sP$6!t-'!u%&C7%G758!s%,'Fg005H#Dg004ER9/:9R5P7AB990A?990'>X05g00=ZC@5A8do"). Qed.
Lemma reservedZ_segments : ltac2:(zQ "70!j1!hgf!hh6!h4!hs9!uf!il9@3$3@1$1@2$2$0$0@1$6$5$4").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_init ()) [] "##&{p;2p;1p;3p;4g007Lj2?Tg007lj1>Tg000Uj10Tg001:j12!s8$0j11Tg008lj19Tg009Lj37!sJ$Xj2:Tg00>lj1=Tg003kj3<!sS$Lj4;Tf0R0#0#0p=5%0!s0$#0p=4!s2+!s$'p=3g004ER1P1f1P0C;p=6%1!s@$81?11R1#>R0g004cR2#0R3#5R4#4#3R5#0#2%12R2#0#1R6#1#1#4#3#2'6%14!s5,%83#8#8!sB,2#1!s[$5!sH+25!s>%!s8,56!sV+9157!s%,':g005H#=g00=Z5<0do"). Qed.

Lemma mminv_init : ltac2:(zQ "90!hj1!hl5!j1!m1!im6!in2!inf!uf!is9>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>2sp@1$1@1$0#k0>3lim$2>3inp$4@1$8@2$6^6@6$5@1$3$7^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocMF_init ()) [] "h03brkh13inph23limh35mbaseh42sph53tidp;1p;2p;6p;3p;4g000Uj10Tg006Kj1=Tg006ij18Tg007Lj25Tg007lj14Tg0022j1;Tg00@3j6:Tg00@lj27Tg00Acj16Tg008lj12Tg003kj33Tg00B[j19Tg001Xj21Tg00C[j4<Tg004c#0#0#0#0#0#0#=#8R0g004Eg00D61500R1#4R2f5g005H#;f4f3f2f1f0E:'7R3#6%21R133%40R4%93%20R33311211143C<W1W2X40X30X00W5o"). Qed.

Section HC.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

End HC.
(* [comment removed for export] *)
