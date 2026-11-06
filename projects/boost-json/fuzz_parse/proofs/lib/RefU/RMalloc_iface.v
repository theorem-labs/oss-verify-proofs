(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj63addj62lej62lthc2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~m36RERRNOm38RGOT_SSPm3aRSSP_GUARDm34RCTXm35RLIBC37Corelib4Init9Datatypest54list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~v45block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hk13mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hob6PState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ht16mstatehc2exhc2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocHINV~~~~~~ii39HINV_fromm3cref_reservedm35rmrepht15striphob6ps_brkhob4ps_m36Stdlib7SortingbPermutationiq5bPermutation89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdRMalloc_iface3HCW~~~~~~it05RHEAPhc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface~~~~~~ji88in_blockit0dralloc_static04Npos35stdpp9bitvectorbdefinitionsjp02bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jr32wat56optiont54None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskg35wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~kk35rsegsit0crclient_addrj63powit0arheap_pres36Stdlib5Lists4Listkqd2Inv48blk_addrv48blk_sizeit0drclient_rangejr38bytes_att56lengthj66of_natjr35wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lh48rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~llb4cellllbacells_size69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lqd5hceilj66modulot54prodt53fstt53sndht1eMMAP_THRESHOLDhob7ps_inithob9reservedZkg3dmachine_state3h5LinuxProcessSemantics5Riscv7Preludemk85bvmaphob4bptrt54consjp0bbv_unsignedt53nilt54pairhob5ps_fahob5ps_sojp07Z_to_bvt54unitllb2C4llb2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mt23mkRmt23stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~nhc2MSnhc6ret_pcjr37mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nn47seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~nre8rauxv_okit0draddr_exposedit0crblock_rangehob8ptr_addrj66to_natm34RATPit0dRMALLOC_STACKit0bRMALLOC_SYMit0crmalloc_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~ona5implMhobaraw_mallocj63subji89lb_removeit0bRFREE_STACKit09RFREE_SYMit0arfree_posthob8raw_free" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition RMALLOC_SYM : Z := 0xdfc04.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0xdfac4.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "b0!j0!ke!l4!l9!le!q5!qe!r9!h9!s6!sd\1a$8@2$4@2$0@2$2$a^1@2$3^1@2$1$9+jq0@2$4@2$0@2$2$5^1@2$3^1@2$1$5+4@2$4@2$0@2$2$7^1@2$3^1@2$1$7+8@2$4@2$0@2$2$6^1@2$3^1@2$1$6+8@2$0@2$2+hjggj0^1@2$3^1@2$1+hjggj0+4").   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP : ltac2:(zQ "40!ud!hj9!ho4!hs7>1s$3>2LB@1$0$1>1m$2P") := ltac2:(zQ "f0!hj9!ud!j0!igf!ih9!ihe!im6!ho4!in3!io2!ioa!hs7!ip3!ipd!is1\1s$b\2LB@1$1$0\1m$7@2$4$3\2st$3@2$4@1$1$0\3LB0@1$1$0@2$2@3$e$0^1^4@2$2@3$5$3@1$a^2@1$d^5@2$2@4$9?5HCEIL?4HSEC^2^3@5$6?4HSEC@1$8?5HCEIL^2@1$c^5^1").

Lemma RHEAP_perm : ltac2:(zQ "60!hj9!ud!jh9!ho4!hs7!is1>1s$4>2LB@1$1$0>3LB'@1$1$0>1m$3>0@3$2^4^3^1>0@3$5$0^4^3@3$2^6^4^3").
Proof. try hcb. try hsb.
  (intros s LB LB' m nd_i2 P; ndestruct nd_i2 as (st & LB0 & HP & H1 & H2 & H3)). exists st, LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr : ltac2:(zQ "30!h9!ud!hj9>2LB@1$1$2>2SP$0>1a$0P") := ltac2:(zQ "a0!j0!le!h9!l4!ud!ji2!hj9!jmd!jn9!l9\2LB@1$4$6\2SP$2\1a$2@2$1@2$3^2^1@2$1@2$0@2$0@2$3+vkgg0^1@2$9^1+hjhgg0@1$5@1$8^1@2$7^3^1").

Definition rheap_pres : ltac2:(zQ "40!ho4!ud!h9!hj9>2LB@1$1$3>2SP$2>1m$0>2m'$0P") := ltac2:(zQ "h20!joa!jqd!jud!jv3!ihe!jvc!j0!ji2!h9!kja!ho4!ko0!ud!hj9!ko9!l4!l9!kp9\2LB@1$c$d\2SP$8\1m$a\2m'$a>1a$8>0@2$6@2$fZ^1@2$h0^1@2$h1+2+k0>0@3$e^6^5^2@2$6@3$4@1$3@1$1@1$0#8@1^4@1$2^3@1^5@1$2^3>0@1$7@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^3@1$5@1$1@1$0#8@1$7@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^4@1$5@1$1@1$0#8").

Lemma rheap_pres_trans : ltac2:(zQ "50!ho4!kpf!ud!h9!hj9>2LB@1$2$4>2SP$3>2m1$0>2m2$0>2m3$0>0@4$1^5^4^3^2>0@4$1^6^5^3^2@4$1^7^6^5^3").
Proof. try hcb. try hsb.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : ltac2:(zQ "70!hj9!ud!h9!ho4!kpf!ks0!l4>2LB@1$1$0>3LB'@1$1$0>2SP$2>3SP'$2>1m$3>2m'$3>0@4$4^6^4^2^1>0@2$6^5^4>0>1b$0>0@3$5$0^1^8@3$5$0^2^a@4$4^8^6^5^4").
Proof. try hcb. try hsb.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range : ltac2:(zQ "30!h9!ud!hj9>2LB@1$1$2>2SP$0>1A$0>1n$0P") := ltac2:(zQ "h00!l4!ke!j0!le!hj9!h9!ks6!q5!qe!r9!ud!ih9!kt1!s6!sd!ks0\2LB@1$a$4\2SP$5\1A$5\1n$5@2$3@2$0^3^2@2$3@2$2@2$0+vkgg0^2@2$2@2$0@2$1^2^1+hjhgg0@2$2@2$3@2$0@2$1^2^1$e@2$0@2$1$d+jq0^2@2$2@2$3@2$0@2$1^2^1$7@2$0@2$1$7+4^2@2$2@2$3@2$0@2$1^2^1$9@2$0@2$1$9+8^2@2$2@2$3@2$0@2$1^2^1$8@2$0@2$1$8+8^2@2$3@2$0@2$1^2^1+hjggj0@2$0@2$1+hjggj0+4^2@2$b$4\1b$4@2$2@3$f$4^1^5@2$2@2$0@1$6^1^3@2$0@2$1^3^2@2$1@1$6^1@1$c^1").

Lemma rclient_range_addr : ltac2:(zQ "90!h9!ud!j0!hj9!ko9!ktc!ke!l4!l9>2LB@1$1$3>2SP$0>1A$0>1n$0>1a$0>0@4$5^5^4^3^2>0@2$2@2$7^4^2@2$8^2@2$6^4^3@3$4^7^6^3").
Proof. try hcb. try hsb.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Lemma rheap_pres_bytes_at : ltac2:(zQ "c0!ud!joa!h9!ho4!kud!ko0!jqd!kv9!hj9!ktc!kpf!lg2>2LB@1$0$8>2SP$2>1m$3>2m'$3>1A$2>2bs@1$0@1$6@1$1#8>0@4$a^6^5^4^3>0@4$4$5^5^3^2>0@4$9^8^7^4@1$b@2$7@1$6@1$1#8^3@4$4$5^6^5^4").
Proof. try hcb. try hsb.
  (intros LB SP m m' A bs HP nd_i3 HR; ndestruct nd_i3 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : ltac2:(zQ "80!h9!ho4!lgb!ko0!ud!hj9!ktc!kpf>2LB@1$4$5>2SP$0>1m$1>2m'$1>1A$0>1n$0>0@4$7^6^5^4^3>0@4$2$3^5^3^2>0@4$6^8^7^4^3@4$2$3^6^5^4").
Proof. try hcb. try hsb.
  (intros LB SP m m' A n HP nd_i4 HR; ndestruct nd_i4 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : ltac2:(zQ "b0!ud!h9!ho4!lkf!ko0!hj9!lp7!lpf!ktc!kpf!lg2>2LB@1$0$5>2SP$1>1m$2>2m'$2>1A$1>2cs@1$0$6>0@4$9^6^5^4^3>0@4$3$4^5^3^2>0@4$8^8^7^4@1$a@1$7^3@4$3$4^6^5^4").
Proof. try hcb. try hsb.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range : ltac2:(zQ "10!h9>1A$0>1n$0P") := ltac2:(zQ "90!j0!l4!h9!ke!ihe!le!lu8!l9!lv1\1A$2\1n$2@2$0@2$7Z^2@2$0@3$4$2@2$8^2+h0Z@2$0@2$1Z^1@2$0@2$1@2$3^2^1@1$6?5HCEIL@2$5@2$1@2$3^2^1+hggg0@2$1+hjhgg0^2").

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok : ltac2:(zQ "40!h9!ud!lva!hj9>2LB@1$1$3>2iv@2$2$0$0P") := ltac2:(zQ "h30!h9!l4!mg1!j0!mg7!le!ke!hj9!ks6!qe!r9!ud!lva!ih9!kt1!lu8!s6!sd!ks0\2LB@1$b$7\2iv@2$c$0$0@2$5@2$1@1$f?5HCEIL@3$2$0$0^1@2$5@2$3@2$1+vkgg0@3$2$0$0^1@2$3@2$1@3$4$0$0^1+hjhgg0@2$3@2$5@2$1@3$4$0$0^1$h1@2$1@2$6$h0+jq0@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$a@2$1@2$6$a+8@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$9@2$1@2$6$9+8@3$2$0$0^1@2$5@2$1@3$4$0$0^1+hjggj0@2$1@2$6+hjggj0+4@3$2$0$0^1@2$d$7\1b$7@2$3@3$h2$7^1^3@2$3@2$1@1$8^1@3$2$0$0^2@2$1@3$4$0$0^2@2$6@1$8^1@1$e^1").


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed : ltac2:(zQ "20!h9!hs7>1s$1>1n$0P") := ltac2:(zQ "b0!ipd!ihe!le!h9!ko0!mgd!igf!hs7!mhf!mia!l4\1s$7\1n$3@2$2@2$a$5^1@3$1$6@1$0^2@1$0@3$8?5HCEIL?4HSEC@1$9$4").


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post : ltac2:(zQ "b0!joa!jqd!h9!hs7!ud!jv3!mj7!mme!hj9!ho4!mn7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1n$2>2lo$2>1B$2>1m$9>1r@1$5$a>2s'$3>0$6P") := ltac2:(zQ "ib1!joa!jqd!ih9!j0!h9!ihe!mn7!jv3!ko0!lva!lp7!mnf!ud!mo6!mp5!mpb!mj7!lkf!jh9!hs7!mq2!mqb!mr4!jvc!mrf!mme!hj9!ho4!ms6!msc!nge!nh5!nl9!nlf!nm9!nr3!og1!ogd!ohe!kpf!oie!ke!oja&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$h3\2LB@1$c$ha\1n$4\2lo$4\1B$4\1m$hb\1r@1$7$6\2s'$h3\3ms'$h0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$3@3$5$h0^h2@7$i0@hf$he^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$i1^ic^hb@1$h7@1$1@1$0#k0^2@1$i3$8@2$3@2$i2$8^2@2$3@4$hf$8^2^h7@2$d@1$0#k0^ib@2$3@4$h1$8^2@2$i9@2$d@1$0#k0^i9-q4@3$b$a@1$hc^1@1$e$a@2$3@4$i4?5HCEIL?4HSEC^2^h6@2$3@4$i7^h9@2$d@1$0#k0^ib^h5^2@2$3@3$5@2$9$4$4@1$h4^h3@1$h4^ha@2$3@3$5$h8@1$h5^h3@1$h5^haM7\1r@1$7$6P^h4\1p$6@2$2$4\1A$4@2$2@1$c@1$1@1$0#8\4junk@1$c@1$1@1$0#8@2$3@3$5@1$1@1$0#k0^h1@2$h6@1$0#k0^2@2$3@2$i6^2^hb@2$3@3$h2^h6@3$b@2$9@2$9$6$4$4@4$f@2$9$6$4$4@4$f$6$4^3^2^hb^hc^5@2$3@4$h1$8^5^2@3$b$a@2$hd@1$ia^hb^1@1$e$a>0@2$i5^hd^hb@3$5$4^3@2$i8^h7^4@2$3@3$5@1$1@1$0#k0^e@2$h6@1$0#k0Z@3$h2^h3^h9^2").

Definition rmalloc_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i80!joa!jqd!ko0!l4!mo6!h9!mr4!ihe!lp7!hs7!jvc!mnf!ud!mp5!jv3!j0!mme!hj9!ho4!lu8!ms6!nge!nh5!nl9!nm9!nr3!lkf!ok3!og1!jh9!oka!olb!oma!or7!mn7!os0!ke!l9!kp9!ose>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h2>1s$9>2LB@1$c$h1>1n$5>2lo$5>1B$5>4errv@1$1@1$0#k0>0@3$hd^6^5^7>0@4$hc?5HCEIL?4HSEC^8^3>0@2$3@2$4@1$0#k0^i9^4>0@4$h6$2^a^6@2$4@1$0#k0^ia>0@2$3@1$h3?5HCEIL^7>0@2$3^8@2$i7@2$4@1$0#k0^ic$he>0@4$ha$2^d@2$i4@2$4@1$0#k0^ib-q4@3$b$8@1$h4^7@1$d$8>0@2$h8$2^e>0@3$7@1$1@1$0#k0^id@2$6@1$0#k0$hb>0@3$7@1$1@1$0#k0^i8@2$6@1$0#k0^d>0@2$f@2$3Z^e@2$i5^e@2$i6+2+i0@7$i1$9$2@1$e$i2@2$i3?5HCEIL^f^h1@h8$i0^j3^j2^j1^j0^ic^ib^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h4^h3^h1^h0^f^e^d^h2@7$h7@hf$h5^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4@2$6@1$0#k0$hf^h3@1$a@1$1@1$0#k0^h2@1$h9$2").

Definition rfree_post : ltac2:(zQ "b0!joa!jqd!h9!hs7!ud!mrf!mj7!mme!hj9!ho4!mn7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1p$a>2lo$2>1B$2>4errv@1$1@1$0#k0>1m$9>1r$5>2s'$3>0$6P") := ltac2:(zQ "i51!joa!jqd!ih9!j0!h9!ko0!ihe!mo6!jv3!mrf!mj7!ot4!lp7!hs7!mq2!mqb!jvc!mnf!ud!mp5!lva!mme!hj9!ho4!ms6!nge!nh5!nl9!nlf!nm9!nr3!lkf!og1!jh9!kpf!mn7!ke&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$d\2LB@1$h2$h6\1p$i3\2lo$4\1B$4\4errv@1$1@1$0#k0\1m$h7\1r$9\2s'$d\3ms'$a@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$3@3$6$a^h1@7$hb@hf$h9^ic^ib^ia^i9^h0^f^e^i8^i7^d^c^b^a^9^8^7^6^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^5^4^3^2^hc@1$hc^ic^hb@1$h0@1$1@1$0#k0^1@1$he$5@2$3@2$hd$5^1@2$3@4$ha$5^1^h7@2$7@1$0#k0^ib@2$3@4$hf$5^1@2$i4@2$7@1$0#k0^i9-q4@3$h1$c@1$h8^h5@1$h3$c@2$3@4$i0?5HCEIL?4HSEC^1^h6@2$3@4$i2@2$b^h8^h9@2$7@1$0#k0^ib^h4^1@2$3@3$6@2$h4$4$4@1$e^h2@1$e^ha@2$3@3$6$9@1$f^h2@1$f^ha@3$i1^h2@2$b^h8^h9^1").

Definition rfree_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i80!joa!jqd!h9!ko0!mn7!mo6!lva!l4!mr4!mpb!ihe!lp7!hs7!jvc!mnf!ud!mp5!mrf!mme!hj9!ho4!lu8!ms6!nge!nh5!nl9!nm9!nr3!lkf!ok3!og1!ou1!ov0!jh9!ovd!or7!pgb!ks0!ke!ose>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h4>1s$c>2LB@1$f$h3>1p$4>1A$2>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>0@3$i1^8^7^9>0@3$i5@2$6@2$6$4$2$2@4$9@2$6$4$2$2@4$9$4$2^7^6^5^8>0@4$he?5HCEIL?4HSEC^b^4>0@2$7@2$5@1$0#k0^ic^5>0@4$h8$3^d^7@2$5@1$0#k0^id>0@2$7@1$h5?5HCEIL^8>0@2$7^9@2$i7@2$5@1$0#k0^if$hf>0@4$hc$3^h0@2$i6@2$5@1$0#k0^ie-q4@3$e$b@1$h6^8@1$h0$b>0@2$ha$3^h1>0@3$a@1$1@1$0#k0^j0@2$8@1$0#k0$hd>0@3$a@1$1@1$0#k0^ib@2$8@1$0#k0^f@7$i3$c$3$h1@2$i4?5HCEIL^h1^h3@h9$i2^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^h2^h1^e^d^c^h4@7$h9@hf$h7^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@2$8@1$0#k0$i0^h5@1$d@1$1@1$0#k0^h4@1$hb$3").

(* [comment removed for export] *)

End HCW.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
