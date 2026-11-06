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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj63addj62lej62lthc2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~m36RERRNOm38RGOT_SSPm3aRSSP_GUARDm34RCTXm35RLIBC37Corelib4Init9Datatypest44list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~v35block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hk03mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hoa6PState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ht06mstatehc2exhc2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocHINV~~~~~~ii29HINV_fromm3cref_reservedm35rmrepht05striphoa6ps_brkhoa4ps_m36Stdlib7SortingbPermutationiq4bPermutation89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefdRMalloc_iface3HCW~~~~~~isf5RHEAPhc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface~~~~~~ji68in_blockisfdralloc_static04Npos35stdpp9bitvectorbdefinitionsjoe2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jr12wat46optiont44None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskg15wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~kk15rsegsisfcrclient_addrj63powisfarheap_pres36Stdlib5Lists4Listkqa2Inv38blk_addrv38blk_sizeisfdrclient_rangejr18bytes_att46lengthj66of_natjr15wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lh18rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ll84cellll8acells_size69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lqa5hceilj66modulot44prodt43fstt43sndht0eMMAP_THRESHOLDhoa7ps_inithoa9reservedZkg1dmachine_state3h5LinuxProcessSemantics5Riscv7Preludemk55bvmaphoa4bptrt44consjoebbv_unsignedt43nilt44pairhoa5ps_fahoa5ps_sojoe7Z_to_bvt44unitll82C4ll82CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~msf3mkRmsf3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~nh92MSnh96ret_pcjr17mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nn17seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~nrb8rauxv_okisfdraddr_exposedisfcrblock_rangehoa8ptr_addrj66to_natm34RATPisfdRMALLOC_STACKisfbRMALLOC_SYMisfcrmalloc_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~on65implMhoaaraw_mallocj63subji69lb_removeisfbRFREE_STACKisf9RFREE_SYMisfarfree_posthoa8raw_free" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition RMALLOC_SYM : Z := 0xdc75c.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0xdc61c.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "b0!j0!ke!l4!l9!le!q4!qd!r8!h9!s5!sc\1a$8@2$4@2$0@2$2$a^1@2$3^1@2$1$9+jq0@2$4@2$0@2$2$5^1@2$3^1@2$1$5+4@2$4@2$0@2$2$7^1@2$3^1@2$1$7+8@2$4@2$0@2$2$6^1@2$3^1@2$1$6+8@2$0@2$2+hisqv0^1@2$3^1@2$1+hisqv0+4").   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP : ltac2:(zQ "40!uc!hj8!ho3!hs6>1s$3>2LB@1$0$1>1m$2P") := ltac2:(zQ "f0!hj8!uc!j0!ige!ih8!ihd!im5!ho3!in2!io1!io9!hs6!ip2!ipc!is0\1s$b\2LB@1$1$0\1m$7@2$4$3\2st$3@2$4@1$1$0\3LB0@1$1$0@2$2@3$e$0^1^4@2$2@3$5$3@1$a^2@1$d^5@2$2@4$9?5HCEIL?4HSEC^2^3@5$6?4HSEC@1$8?5HCEIL^2@1$c^5^1").

Lemma RHEAP_perm : ltac2:(zQ "60!hj8!uc!jh7!ho3!hs6!is0>1s$4>2LB@1$1$0>3LB'@1$1$0>1m$3>0@3$2^4^3^1>0@3$5$0^4^3@3$2^6^4^3").
Proof. try hcb. try hsb.
  (intros s LB LB' m nd_i2 P; ndestruct nd_i2 as (st & LB0 & HP & H1 & H2 & H3)). exists st, LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr : ltac2:(zQ "30!h9!uc!hj8>2LB@1$1$2>2SP$0>1a$0P") := ltac2:(zQ "a0!j0!le!h9!l4!uc!ji0!hj8!jmb!jn7!l9\2LB@1$4$6\2SP$2\1a$2@2$1@2$3^2^1@2$1@2$0@2$0@2$3+vhgg0^1@2$9^1+hitgg0@1$5@1$8^1@2$7^3^1").

Definition rheap_pres : ltac2:(zQ "40!ho3!uc!h9!hj8>2LB@1$1$3>2SP$2>1m$0>2m'$0P") := ltac2:(zQ "h20!jo8!jqb!jub!jv1!ihd!jva!j0!ji0!h9!kj8!ho3!knd!uc!hj8!ko6!l4!l9!kp6\2LB@1$c$d\2SP$8\1m$a\2m'$a>1a$8>0@2$6@2$fZ^1@2$h0^1@2$h1+2+k0>0@3$e^6^5^2@2$6@3$4@1$3@1$1@1$0#8@1^4@1$2^3@1^5@1$2^3>0@1$7@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^3@1$5@1$1@1$0#8@1$7@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^4@1$5@1$1@1$0#8").

Lemma rheap_pres_trans : ltac2:(zQ "50!ho3!kpc!uc!h9!hj8>2LB@1$2$4>2SP$3>2m1$0>2m2$0>2m3$0>0@4$1^5^4^3^2>0@4$1^6^5^3^2@4$1^7^6^5^3").
Proof. try hcb. try hsb.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : ltac2:(zQ "70!hj8!uc!h9!ho3!kpc!krd!l4>2LB@1$1$0>3LB'@1$1$0>2SP$2>3SP'$2>1m$3>2m'$3>0@4$4^6^4^2^1>0@2$6^5^4>0>1b$0>0@3$5$0^1^8@3$5$0^2^a@4$4^8^6^5^4").
Proof. try hcb. try hsb.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range : ltac2:(zQ "30!h9!uc!hj8>2LB@1$1$2>2SP$0>1A$0>1n$0P") := ltac2:(zQ "h00!l4!ke!j0!le!hj8!h9!ks3!q4!qd!r8!uc!ih8!kse!s5!sc!krd\2LB@1$a$4\2SP$5\1A$5\1n$5@2$3@2$0^3^2@2$3@2$2@2$0+vhgg0^2@2$2@2$0@2$1^2^1+hitgg0@2$2@2$3@2$0@2$1^2^1$e@2$0@2$1$d+jq0^2@2$2@2$3@2$0@2$1^2^1$7@2$0@2$1$7+4^2@2$2@2$3@2$0@2$1^2^1$9@2$0@2$1$9+8^2@2$2@2$3@2$0@2$1^2^1$8@2$0@2$1$8+8^2@2$3@2$0@2$1^2^1+hisqv0@2$0@2$1+hisqv0+4^2@2$b$4\1b$4@2$2@3$f$4^1^5@2$2@2$0@1$6^1^3@2$0@2$1^3^2@2$1@1$6^1@1$c^1").

Lemma rclient_range_addr : ltac2:(zQ "90!h9!uc!j0!hj8!ko6!kt9!ke!l4!l9>2LB@1$1$3>2SP$0>1A$0>1n$0>1a$0>0@4$5^5^4^3^2>0@2$2@2$7^4^2@2$8^2@2$6^4^3@3$4^7^6^3").
Proof. try hcb. try hsb.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Lemma rheap_pres_bytes_at : ltac2:(zQ "c0!uc!jo8!h9!ho3!kua!knd!jqb!kv6!hj8!kt9!kpc!kvf>2LB@1$0$8>2SP$2>1m$3>2m'$3>1A$2>2bs@1$0@1$6@1$1#8>0@4$a^6^5^4^3>0@4$4$5^5^3^2>0@4$9^8^7^4@1$b@2$7@1$6@1$1#8^3@4$4$5^6^5^4").
Proof. try hcb. try hsb.
  (intros LB SP m m' A bs HP nd_i3 HR; ndestruct nd_i3 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : ltac2:(zQ "80!h9!ho3!lg8!knd!uc!hj8!kt9!kpc>2LB@1$4$5>2SP$0>1m$1>2m'$1>1A$0>1n$0>0@4$7^6^5^4^3>0@4$2$3^5^3^2>0@4$6^8^7^4^3@4$2$3^6^5^4").
Proof. try hcb. try hsb.
  (intros LB SP m m' A n HP nd_i4 HR; ndestruct nd_i4 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : ltac2:(zQ "b0!uc!h9!ho3!lkc!knd!hj8!lp4!lpc!kt9!kpc!kvf>2LB@1$0$5>2SP$1>1m$2>2m'$2>1A$1>2cs@1$0$6>0@4$9^6^5^4^3>0@4$3$4^5^3^2>0@4$8^8^7^4@1$a@1$7^3@4$3$4^6^5^4").
Proof. try hcb. try hsb.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range : ltac2:(zQ "10!h9>1A$0>1n$0P") := ltac2:(zQ "90!j0!l4!h9!ke!ihd!le!lu5!l9!lue\1A$2\1n$2@2$0@2$7Z^2@2$0@3$4$2@2$8^2+h0Z@2$0@2$1Z^1@2$0@2$1@2$3^2^1@1$6?5HCEIL@2$5@2$1@2$3^2^1+hggg0@2$1+hitgg0^2").

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok : ltac2:(zQ "40!h9!uc!lv7!hj8>2LB@1$1$3>2iv@2$2$0$0P") := ltac2:(zQ "h30!h9!l4!lve!j0!mg4!le!ke!hj8!ks3!qd!r8!uc!lv7!ih8!kse!lu5!s5!sc!krd\2LB@1$b$7\2iv@2$c$0$0@2$5@2$1@1$f?5HCEIL@3$2$0$0^1@2$5@2$3@2$1+vhgg0@3$2$0$0^1@2$3@2$1@3$4$0$0^1+hitgg0@2$3@2$5@2$1@3$4$0$0^1$h1@2$1@2$6$h0+jq0@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$a@2$1@2$6$a+8@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$9@2$1@2$6$9+8@3$2$0$0^1@2$5@2$1@3$4$0$0^1+hisqv0@2$1@2$6+hisqv0+4@3$2$0$0^1@2$d$7\1b$7@2$3@3$h2$7^1^3@2$3@2$1@1$8^1@3$2$0$0^2@2$1@3$4$0$0^2@2$6@1$8^1@1$e^1").


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed : ltac2:(zQ "20!h9!hs6>1s$1>1n$0P") := ltac2:(zQ "b0!ipc!ihd!le!h9!knd!mga!ige!hs6!mhc!mi7!l4\1s$7\1n$3@2$2@2$a$5^1@3$1$6@1$0^2@1$0@3$8?5HCEIL?4HSEC@1$9$4").


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post : ltac2:(zQ "b0!jo8!jqb!h9!hs6!uc!jv1!mj4!mmb!hj8!ho3!mn4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1n$2>2lo$2>1B$2>1m$9>1r@1$5$a>2s'$3>0$6P") := ltac2:(zQ "ib1!jo8!jqb!ih8!j0!h9!ihd!mn4!jv1!knd!lv7!lp4!mnc!uc!mo3!mp2!mp8!mj4!lkc!jh7!hs6!mpf!mq8!mr1!jva!mrc!mmb!hj8!ho3!ms3!ms9!ngb!nh2!nl6!nlc!nm6!nr0!nvd!og9!oha!kpc!oia!ke!oj6&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$h3\2LB@1$c$ha\1n$4\2lo$4\1B$4\1m$hb\1r@1$7$6\2s'$h3\3ms'$h0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$3@3$5$h0^h2@7$i0@hf$he^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$i1^ic^hb@1$h7@1$1@1$0#k0^2@1$i3$8@2$3@2$i2$8^2@2$3@4$hf$8^2^h7@2$d@1$0#k0^ib@2$3@4$h1$8^2@2$i9@2$d@1$0#k0^i9-q4@3$b$a@1$hc^1@1$e$a@2$3@4$i4?5HCEIL?4HSEC^2^h6@2$3@4$i7^h9@2$d@1$0#k0^ib^h5^2@2$3@3$5@2$9$4$4@1$h4^h3@1$h4^ha@2$3@3$5$h8@1$h5^h3@1$h5^haM7\1r@1$7$6P^h4\1p$6@2$2$4\1A$4@2$2@1$c@1$1@1$0#8\4junk@1$c@1$1@1$0#8@2$3@3$5@1$1@1$0#k0^h1@2$h6@1$0#k0^2@2$3@2$i6^2^hb@2$3@3$h2^h6@3$b@2$9@2$9$6$4$4@4$f@2$9$6$4$4@4$f$6$4^3^2^hb^hc^5@2$3@4$h1$8^5^2@3$b$a@2$hd@1$ia^hb^1@1$e$a>0@2$i5^hd^hb@3$5$4^3@2$i8^h7^4@2$3@3$5@1$1@1$0#k0^e@2$h6@1$0#k0Z@3$h2^h3^h9^2").

Definition rmalloc_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i80!jo8!jqb!knd!l4!mo3!h9!mr1!ihd!lp4!hs6!jva!mnc!uc!mp2!jv1!j0!mmb!hj8!ho3!lu5!ms3!ngb!nh2!nl6!nm6!nr0!lkc!ojf!nvd!jh7!ok6!ol7!om6!or3!mn4!orc!ke!l9!kp6!osa>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h2>1s$9>2LB@1$c$h1>1n$5>2lo$5>1B$5>4errv@1$1@1$0#k0>0@3$hd^6^5^7>0@4$hc?5HCEIL?4HSEC^8^3>0@2$3@2$4@1$0#k0^i9^4>0@4$h6$2^a^6@2$4@1$0#k0^ia>0@2$3@1$h3?5HCEIL^7>0@2$3^8@2$i7@2$4@1$0#k0^ic$he>0@4$ha$2^d@2$i4@2$4@1$0#k0^ib-q4@3$b$8@1$h4^7@1$d$8>0@2$h8$2^e>0@3$7@1$1@1$0#k0^id@2$6@1$0#k0$hb>0@3$7@1$1@1$0#k0^i8@2$6@1$0#k0^d>0@2$f@2$3Z^e@2$i5^e@2$i6+2+i0@7$i1$9$2@1$e$i2@2$i3?5HCEIL^f^h1@h8$i0^j3^j2^j1^j0^ic^ib^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h4^h3^h1^h0^f^e^d^h2@7$h7@hf$h5^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4@2$6@1$0#k0$hf^h3@1$a@1$1@1$0#k0^h2@1$h9$2").

Definition rfree_post : ltac2:(zQ "b0!jo8!jqb!h9!hs6!uc!mrc!mj4!mmb!hj8!ho3!mn4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1p$a>2lo$2>1B$2>4errv@1$1@1$0#k0>1m$9>1r$5>2s'$3>0$6P") := ltac2:(zQ "i51!jo8!jqb!ih8!j0!h9!knd!ihd!mo3!jv1!mrc!mj4!ot0!lp4!hs6!mpf!mq8!jva!mnc!uc!mp2!lv7!mmb!hj8!ho3!ms3!ngb!nh2!nl6!nlc!nm6!nr0!lkc!nvd!jh7!kpc!mn4!ke&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$d\2LB@1$h2$h6\1p$i3\2lo$4\1B$4\4errv@1$1@1$0#k0\1m$h7\1r$9\2s'$d\3ms'$a@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$3@3$6$a^h1@7$hb@hf$h9^ic^ib^ia^i9^h0^f^e^i8^i7^d^c^b^a^9^8^7^6^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^5^4^3^2^hc@1$hc^ic^hb@1$h0@1$1@1$0#k0^1@1$he$5@2$3@2$hd$5^1@2$3@4$ha$5^1^h7@2$7@1$0#k0^ib@2$3@4$hf$5^1@2$i4@2$7@1$0#k0^i9-q4@3$h1$c@1$h8^h5@1$h3$c@2$3@4$i0?5HCEIL?4HSEC^1^h6@2$3@4$i2@2$b^h8^h9@2$7@1$0#k0^ib^h4^1@2$3@3$6@2$h4$4$4@1$e^h2@1$e^ha@2$3@3$6$9@1$f^h2@1$f^ha@3$i1^h2@2$b^h8^h9^1").

Definition rfree_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i80!jo8!jqb!h9!knd!mn4!mo3!lv7!l4!mr1!mp8!ihd!lp4!hs6!jva!mnc!uc!mp2!mrc!mmb!hj8!ho3!lu5!ms3!ngb!nh2!nl6!nm6!nr0!lkc!ojf!nvd!otd!ouc!jh7!ov9!or3!pg7!krd!ke!osa>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h4>1s$c>2LB@1$f$h3>1p$4>1A$2>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>0@3$i1^8^7^9>0@3$i5@2$6@2$6$4$2$2@4$9@2$6$4$2$2@4$9$4$2^7^6^5^8>0@4$he?5HCEIL?4HSEC^b^4>0@2$7@2$5@1$0#k0^ic^5>0@4$h8$3^d^7@2$5@1$0#k0^id>0@2$7@1$h5?5HCEIL^8>0@2$7^9@2$i7@2$5@1$0#k0^if$hf>0@4$hc$3^h0@2$i6@2$5@1$0#k0^ie-q4@3$e$b@1$h6^8@1$h0$b>0@2$ha$3^h1>0@3$a@1$1@1$0#k0^j0@2$8@1$0#k0$hd>0@3$a@1$1@1$0#k0^ib@2$8@1$0#k0^f@7$i3$c$3$h1@2$i4?5HCEIL^h1^h3@h9$i2^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^h2^h1^e^d^c^h4@7$h9@hf$h7^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@2$8@1$0#k0$i0^h5@1$d@1$1@1$0#k0^h4@1$hb$3").

(* [comment removed for export] *)

End HCW.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
