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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RBand.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~m33mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~qc6mstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~v36PStatek46option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshk1dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeho95bvmapqc4aptr37Corelib4Init5Logichrf2exhrf3and46Stdlib6ZArith6BinInt1Zhu03add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hvf4cellhfbbv_unsignedhrf2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~il75rsegsk44conshvf2C801Nqccget_meta_recqcaget_stridev35ps_fav34ps_mv35ps_sohf7Z_to_bvk43nilk43snd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iv58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMalloc_fp~~~~~~jjcarmalloc_fphu03mulk44Nonek44unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~jq08ticks_okjq02wzm3bbrk_link_ps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~kg24mrelhvf2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kl23mkRkl23stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~kpc2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ktf7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~li47seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~lme5rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~lr88rauxv_oklr8crpres_exceptqcec_mmap_counterqc3ctxqc6r_baseqc6regionhu02lehu02lthu03subk44Somek43fstk44pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~mm63rdvjq02pwm38pans_memkg29expo_condkg27slot_okkg29unk_agreekpc6ret_pclme6RMLOCKhu03pow89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefeRF_malloc_core4HCW2~~~~~~ng86rcoreQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefeRF_malloc_join~~~~~~nlc8renf_hypqc3retnlc9rfail_hyplmecref_reservedk44list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~nt7bAREACH_fromnt75block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_A~~~~~~oj48MFACTS_g69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~oo65hceillme4RATPlr89RAM_STACKlr86rimplTqceMMAP_THRESHOLDqc8full_layqcbmalloc_coreqc8set_ticklmedrmalloc_entryqc6s_tick46Stdlib6NArith6BinNat1Npj82lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh0RAllocSlot_iface~~~~~~pl6h0ralloc_slot_stmtqc4FUELqcasize_classng89rbig_stmt" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Local Unset Keyed Unification.

End HCW.


Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition rcoreQ : ltac2:(zQ "b0!h9!jc!k1!lc!q6!ua!hif!hj8!hn8!hqf!hr8>1o$4>2m0$4>2st$5>1s$6>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>3s0v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s4v@1$1@1$0#k0>1F@2$9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1n$2>2lo$2>3res@2$3$5@1$7@2$3$a$2>2s'$6>3ms'$8P") := ltac2:(zQ "k24!h9!jc!ht3!ht9!k1!hv8!lc!ijb!ik3!hr8!il1!ip3!ipc!q6!iq3!ua!hj8!iq9!iqc!irb!is8!it0!it7!itf!iu9!iuf!hn8!jj0!jnd!job!jp2!jp9!ju2!jue!jv4!kk4!kkc!koe!kp5!kt9!lh9!lm3!lqf!lva!mg6!mh6!mi7!mid!mj6!hif!mjf!mk5!mkb!ml2!ml9!mlf!hqf!mr0!mr7!mrd!ms8!mt5!mu0!mud!mv7!ng1&@2$5@1$if^h5@3$h9$h1$4^h6&@2$5~0+h0&@2$hd@1$h3@2$h2^hb^h8^h7&@2$5~1~2\1o$d\2m0$d\2st$f\1s$j1\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\3s0v@1$1@1$0#k0\3s1v@1$1@1$0#k0\3s2v@1$1@1$0#k0\3s3v@1$1@1$0#k0\3s4v@1$1@1$0#k0\1F@2$j8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1n$4\2lo$4\3res@2$6$f@1$h0@2$6$9$4\2s'$j1\3ms'$haM6\3res@2$6$f@1$h0@2$6$9$4P^3\3st2$f\2o0@1$h0@2$6$9$4Mh0\2o0@1$h0@2$6$9$4P^1\1p@2$6$9$4M6\1p@2$6$9$4P^1\1g$9\3idx$4@2$2$9\1b$9@2$2$j0\1r$j0@2$2$d\2m1$d@2$2@1$1@1$0#k0\4errv@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2s4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2@1$1@1$0#k0\3ra'@1$1@1$0#k0@2$3@3$a$ha^hb@7$i7@hf$i5^1@2$h7@1$0#k0@2$5@2$8@1$0#k0^j0-j0^if^ie^h1^h0^f@2$h7@1$0#k0^hf@2$h7@1$0#k0$k0^e^d^c^b^a^9^8^7@2$ja^ha@2$j5$9^h7@1$i1^h6^6^id^ic^ib^ia^i9^i8^i7^5^4^3^2^i1@2$h7@1$0#k0+ttmv0^i0@1$he@1$1@1$0#k0^h3@1$i9$b@2$3@4$ia?5HCEIL?4HSEC^ha^h3@2$3@1$i0^ha@2$3@3$je^ha^j5^h3@2$3@2$i8$b^h3@2$3@4$i6$b^h3^he@2$5@2$8@1$0#k0^j0-j0@2$3@4$hb$b^h3@2$5@2$8@1$0#k0^j0-j0@3$c$7@1$e^i2@3$c$7@1$e^i3@3$c$7@1$e^i4@3$c$7@1$e^i5@3$c$7@1$e^i6@3$c$7@1$e^j1@1$h8$7@2$3@4$hb$b^h3@2$5@2$8@1$0#k0^ie-q4@3$c$7@1$i4^h2@1$h8$7@2$3@4$ib?5HCEIL?4HSEC^h3@2$8@1$0#k0^j0@2$3@3$ic@4$hc^j3^ha^he@2$8@1$0#k0^j0^j4^h3@2$3>1a$4>0@2$3@2$j2@2$j4~3+4^1@2$j3^1@2$j4@2$5~3@1$h3@2$h2^hb^h8+4@5$hc^j5^hc^i0@2$8@1$0#k0^j2^2@2$3@2$3@2$j2Z@1$id@1$ie^ha@2$j3@1$id@1$ie^ha@2$k1+2+i0@2$3@6$jd^ha^h7^h5^h4^h6^hf@2$3>0@2$jc^j3^hf@3$a$4@5$j9$d$jb^j6^hb@4$j7$h1$4@3$j6$h1$4^h6@2$5@2$5@3$h9$h1$4^h6@2$5+h0~2-3Z@2$3@2$i3^j3^ha@2$3@2$i2^ha^hc@2$3@3$a$f@1$h5^hc@1$h5^j2@2$3@3$a@2$6$4$4@1$h4^hc@1$h4^j2@3$a$hf@1$h6^hc@1$h6^j2@2$2$d\2m1$d@2$2@1$1@1$0#k0\4errv@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3@3$a$ha^h3@7$i7@hf$i5^i9^i8^i7^i6^e^d^c^he^hd@1$i1Z^b^a^9^8^7^6^5^hc^hb^ha^i5^i4^i3^i2^i1^i0^hf^4^3^2^1^h9@1$jf^i9^h8@1$he@1$1@1$0#k0^h0@1$i9$b@2$3@4$ia?5HCEIL?4HSEC^h2^h0@2$3@1$i0^h2@2$3@2$i8$b^h0@2$3@4$i6$b^h0^h6@2$8@1$0#k0^i8@2$3@4$hb$b^h0@2$5@2$8@1$0#k0^i6-q4@3$c$7@1$i4^f@1$h8$7@2$3@4$ib?5HCEIL?4HSEC^h0@2$8@1$0#k0^i8@2$3@3$ic@4$hc^ib^h2^h6@2$8@1$0#k0^i8^ic^h0@2$3@2$i3^ib^h2@2$3@2$i2^h2^h4@2$3@3$a$f@1$h5^h4@1$h5^ia@2$3@3$a@2$6$4$4@1$h4^h4@1$h4^ia@3$a$hf@1$h6^h4@1$h6^ia").

Lemma renf_hyp_ret : ltac2:(zQ "e0!h9!jc!lc!k1!ua!hj8!hr8!q6!mlf!hqf!nl2!nq1!nqd!hif>1o$7>2m0$7>2st$4>1s$d>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>3s0v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s4v@1$1@1$0#k0>1F@2$9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1n$3>2lo$3@hd$b?5HCEIL?4HSEC@2$2$4@1$5@2$2$6$3\3st1$4\1r@1$5@2$2$6$3@2$c@2$2$4@1$5@2$2$6$3@4$8$4@1$5@2$2$6$3^2^1^h8^h7^h6^h5@h8$a^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1").
Proof. intros o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo. try hcb. try hsb.
  intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  nexists b, r, m1, errv. neexists 17. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Lemma rfail_hyp_ret : ltac2:(zQ "e0!h9!jc!lc!k1!ua!hj8!hr8!q6!mlf!hqf!nl2!nr3!nqd!hif>1o$7>2m0$7>2st$4>1s$d>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>3s0v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s4v@1$1@1$0#k0>1F@2$9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1n$3>2lo$3@hc$b?5HCEIL?4HSEC@2$2$4@1$5@2$2$6$3\3st1$4\1r@1$5@2$2$6$3@2$c@2$2$4@1$5@2$2$6$3@4$8$4@1$5@2$2$6$3^2^1^h8^h7^h6^h5@h8$a^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^1").
Proof. intros o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo. try hcb. try hsb.
  intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists m1, errv. neexists 14. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

(* [comment removed for export] *)
Definition rbig_stmt : ltac2:(zQ "00P") := ltac2:(zQ "j70!h9!jc!ijb!ipc!ik3!iq3!itf!ip3!hv8!k1!q6!ua!mjf!iu9!lc!jj0!ns0!lqf!mkb!jp2!nt0!hj8!ht9!il1!iq9!hqf!ohc!oib!ona!ju2!jv4!mu0!os1!kkc!koe!kp5!kt9!lh9!lm3!nl2!osa!mv7!ot2!lva!otf!mg6!jnd!ou9!hr8!ova!pg5!ph3!hif!mk5!ng1>1o$a>2m0$a>2st$b>2LB@1$h4$hb>1s$j4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>3s0v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s4v@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1n$9>2lo$9>1t$h8>2m1$a>4errv@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>3s2r@1$1@1$0#k0>3s3r@1$1@1$0#k0>3s4r@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>3ra'@1$1@1$0#k0=3st1$b@2$j3^h5^ic>0@4$ha?4HSEC@1$h0?5HCEIL^id^ic>0@3$hc@1$h0?5HCEIL^ie^id>0@4$h1?5HCEIL?4HSEC^if^j0>0@3$h7@1$1@1$0#k0^ia@2$6@1$0#k0$i8>0@2$c@1$i0?5HCEIL^hb>0@2$c^hc@2$h2@2$h2@2$4@1$0#k0^ie+j0$ia>0@2$h6@2$c$if^he@2$j5^he@2$j6+2+i0>0@2$he^j4^j2>0@4$h1?5HCEIL?4HSEC^9^hd>0@1$hd^a>0@3$hf^b^j9^hf>0@2$i5$7^i0>0@4$i3$7^i1^i3@2$8@2$4@1$0#k0^j5-j0>0@4$f$7^i2@2$8@2$4@1$0#k0^j6-j0@3$3$2@1$5^i8@3$3$2@1$5^i9@3$3$2@1$5^ia@3$3$2@1$5^ib@3$3$2@1$5^ic@3$3$2@1$5^j7@1$d$2>0@4$f$7^i3@2$8@2$4@1$0#k0^j5-q4@3$3$2@1$i1^i2@1$d$2>0@4$ib?5HCEIL?4HSEC^i4@2$4@1$0#k0^j8>0@3$id@4$ie^jd^h1^i7@2$4@1$0#k0^j9^je^i5@7$ic?5HCEIL@2$e$b@1$h5@2$e$j0$9^k0@3$j2$j1^h2^i9^jc@h8$i7^k0^jf^je^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8@7$i4@hf$i2^h3@2$6@1$0#k0@2$8@2$4@1$0#k0^ja-j0^j9^j8^i4^i3^i2@2$6@1$0#k0^i9@2$6@1$0#k0$i9@2$6@1$0#k0+hvvuc^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^j7^j6^j5^j4^j3^j2^j1^h7^h6^h5^h4^ib@2$6@1$0#k0+ttkk0^ia@1$h3@1$1@1$0#k0^i6@1$i6$7").

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ltac2:(zQ "10!ppe@4$0?5HCEIL?4HSEC?6as_pre?6as_inv").
Hypothesis AS_PRE : ltac2:(zQ "h30!mjf!ht9!k1!ns0!mk5!nt0!iq9!ohc!oib!ona!pr3!ua!pif!ph3!pra!pl0!hv8!job!ng1>2st$b>2LB@1$5$8>1t$6>2sc$2>1n$2>0@4$7?4HSEC@1$3?5HCEIL^5^4>0@3$9@1$3?5HCEIL^6^5>0@2$f@1$c^7^5>0@2$1@2$0Z^5@2$4^5+j0>0@2$1@2$0Z^5@2$4^5@2$h2+2+i0>0@2$0@2$h0^6+4@2$h1+h0@1$e^7@5?6as_pre^b@2$d^9^b^8^7$a").
Hypothesis RBIG : ltac2:(zQ "10!ps7$0").

Lemma rmalloc_core_implT : ltac2:(zQ "j20!h9!jc!ip3!ik3!k1!mjf!itf!lc!il1!ijb!ns0!ua!jp2!ipc!nt0!iu9!hj8!ht9!iq9!hqf!ohc!oib!ona!jv4!q6!os1!kkc!koe!kp5!kt9!lh9!lm3!jj0!nl2!osa!phe!lqf!lva!otf!hr8!ova!pg5!pif!ph3!hif!pl0!hv8!mk5!ng1!mkb>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h3@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h8>2st$b>2LB@1$e$h5>1s$ic>1n$4>2lo$4>4errv@1$1@1$0#k0>1t$h2>0@4$h4?4HSEC@1$a?5HCEIL^7^6>0@3$h6@1$a?5HCEIL^8^7>0@4$i4?5HCEIL?4HSEC^9^a>0@2$h7^a^8>0@4$i5?5HCEIL?4HSEC^c@2$3@1$0#k0^ic>0@4$hc$2^d^8@2$3@1$0#k0^id>0@2$5@1$h9?5HCEIL^9>0@2$5^a@2$j1@2$3@1$0#k0^if+igg0>0@4$i0$2^h0@2$ie@2$3@1$0#k0^ie-q4@3$d$9@1$ha^a@1$f$9>0@2$he$2^h1>0@3$8@1$1@1$0#k0^j0@2$6@1$0#k0$i2>0@3$8@1$1@1$0#k0^ib@2$6@1$0#k0^f>0@2$h1@2$5Z^h0@2$if^h0@2$j0+2+i0>0@2$id@1$ia^h4^e@7$i6?5HCEIL@2$7$b@1$h0@2$7$i7$4^h6@3$i9$i8@2$ib^f^h5^h2^h3@h8$i1^h6^h6^h5^h3^j7^j6^j5^j4^i3^i2^i1^i0^hf^he^hd^j0^if^i6^i5^i4^h8^h7^h2^h1@7$hd@hf$hb^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@2$6@1$0#k0$i3^h7@1$c@1$1@1$0#k0^h6@1$hf$2").
Proof. try hcb. try hsb.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= hceil).
  { intros rid r1 H1. npose (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in X2. lia. }
  npose MR as (WF0 & CX0 & GL0 & _). ndestruct GL0 as (_ & NL & _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  - (* [comment removed for export] *)
    riprefixT. eapply evt_cut.
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO; lia| lia| exact MI]. }
    (intros ms' nd_i1; ndestruct nd_i1 as (a1' & m1 & -> & FR & ST1 & MU & WM & MI1)).
    ndestruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO; lia| lia| exact MI| exact NL]. }
    (intros ms' nd_i2; ndestruct nd_i2 as (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1)).
    ndestruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    npose (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.

End HCW2.

