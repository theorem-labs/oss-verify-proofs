(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes SysStep Exec Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv AllocTop MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMallocRep MallocMF_klink MallocMF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MallocMF_init () := KReplay.lz_vm "##6AK47Corelib7Numbers7BinNums8positive01!sKG2!sK=1Z!sD/4Init5Logic2eq01C4ELinuxProcessSemantics?!s<23RunAsegments_reserved!sdK5State<!s]'_topI!ta;0I!uA?0!v+G3C89OSSVerify6Proofs:boost_json:fuzz_parse3!tN#RefU5RSegs5rsegsC13~~~!vp>N02I45stdpp9bitvector;definitions2bv!u>/!uX$9Datatypes4prod!sF?list!u`/!sf81K!sfA!sFC2C!sF;3fst!sC=snd!v}QSpec4KInv4went!v{%!t,,5Lists7!s+#Def3mapC!vy@DZ_to_bv_obliga!s:#_1K!wTD1c!y%T=MallocMF_!so#<ref_!{g'!u;&!u}UProg9!{m'Z!v&'!|SO:!t[#_model!s_Q8with_ti!}kR9m_vm_lazy!s^QA!s^$materialized!#4373and01I!taQ!s7#Input00".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib7Numbers7BinNumsh81Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runj5h1segments_reserved3h5LinuxProcessSemanticsfLinuxProcessSem5Staten6creserved_top79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~r35rsegs37Corelib4Init9Datatypesv84listv84prodv84consv84pairv83nilh84Npos35stdpp9bitvectorbdefinitionshj92bvv83fstv83snd37Corelib5Lists7ListDefhm83map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdMallocMF_init~~~~~~ho6cref_segments79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~htb4went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ihf9reservedZn69ProcInputn6ainit_modeln68with_tid79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~ioc5mminv" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma reserved_top_ref : ltac2:(zQ "50!h4!j1!m1!q4!v0@3$0$1@1$3@1$2$4+hjhgg0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_init ()) [] "##$Yp;1p;2p;3g0000j12Tg000Uj11Tg001:j13!s/$Xj27Tg0022j16Tg0030j15!s/$kj34Tf0#1#1p=0g004ER!s,$c#0#2#2#1!s-$0!s$-3R1'7g005H#6#5=401do"). Qed.

(* [comment removed for export] *)
Definition ref_segments : ltac2:(zQ "30!j1!hh0!hh7@1$1@2$2$0$0") := ltac2:(zQ "50!j1!hh7!hhe!hi5!hic@3$2@2$1$0$0@4$3$0$0+hggg0+jmgg0@3$2@2$1$0$0@4$3$0$0+kmgg0+qugg0@3$2@2$1$0$0@4$3$0$0+vkgg0+ogg0@3$2@2$1$0$0@4$3$0$0+vsgg0+jlgg0@1$4@2$1$0$0").
Lemma segments_reserved_ref : ltac2:(zQ "d1!j1!hh7!hj2!hl6!hlc!hh0!hm2!h4!hnf!m1!hsb!v0!ih7&@2$1@1$3@1$2#k0@1$3@1$2#k0@3$7@1$5~0@1$9$b@4$8@2$1$0$0~0\1p@2$1$0$0@2$c@3$4$0$0^1@3$6$0$0^1$a").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_init ()) [] "##,Hh01pp;1p;2p;4p;3g000Uj10Tg006Lj1=!s/$jj1;Tg007Mj29!s/$mj1DTg001:j13Tg0000j11Tg008Mj46!s/$mj1:Tg009Mj38!sS$Xj2FTg0022j1E!sA$mj3CTg00:Jj3B!s/$gj2?Tg00;ij4>Tg003kj3@Tg00<Ej2ATg00=8j3<Tf0R0#0#0p=7%0!s0$!s$,p=4f3f2f1/A03<p=2!sH+p=5g004cR1#0R2#7R3#0#7R4#=R5#;R6/96R7#DR8P6P6P5%04#4R4#0#3R9P5P9C2P5%11R1#0#1R9#1#0#5#4#3R:P5P:C2C6!s`&13!sC-3P5P3!sb%2#0#1!s$$!sC'2P5P2!s`/1#!t/&#7!sI1P5%34R4P5P4!sV2!sP+1P5P1!sP$09#1!s;&!u1&C6%:758!s%,'Fg005H#Eg004ER9/99R5P7AC990AB990'?X05g00=[C>5@8do"). Qed.
Lemma reservedZ_segments : ltac2:(zQ "70!j1!hh0!hh7!h4!hsb!v0!ilb@3$3@1$1@2$2$0$0@1$6$5$4").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_init ()) [] "##&{p;2p;1p;3p;4g007Mj2>Tg007mj1=Tg000Uj10Tg001:j12!s8$0j11Tg008mj19Tg009Mj36!sJ$Xj28Tg00>nj1:Tg003kj3<!sS$Mj4;Tf0R0#0#0p=7%0!s0$#0p=4!s2+!s$'p=3g004ER1P1f1P0C;p=51>11R1#=R0g004cR2#0R3#7R4#4#3R5#0#2%12R2#0#1R6#1#0#4#3#2'5%14!s5,%13#0#1!s$$!sH-2#1!sa%#7!sN&25!s>&!s8+06#1!sX+9156!s%,'8g005H#:g00=[5<0do"). Qed.

Lemma mminv_init : ltac2:(zQ "90!hj2!hl6!j1!m1!im8!in4!io1!v0!isb>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>2sp@1$1@1$0#k0>3lim$2>3inp$4@1$8@2$6^6@6$5@1$3$7^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocMF_init ()) [] "h03brkh13inph23limh35mbaseh42sph53tidp;1p;2p;6p;3p;4g000Uj10Tg006Lj1=Tg006jj18Tg007Mj25Tg007mj14Tg0022j1;Tg00@5j6:Tg00@nj27Tg00Aej16Tg008mj12Tg003kj33Tg00B]j19Tg001Xj21Tg00C]j4<Tg004c#0#0#0#0#0#0#=#8R0g004Eg00D81500R1#4R2f5g005H#;f4f3f2f1f0E:'7R3#6%21R133%40R4%93%20R33311211143C<W1W2X40X30X00W5o"). Qed.

Section HC.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

End HC.
(* [comment removed for export] *)
