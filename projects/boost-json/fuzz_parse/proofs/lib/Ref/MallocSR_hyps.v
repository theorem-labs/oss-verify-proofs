(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Prog KLink KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt RHeapX HeapSR_iface MallocMF_klink MallocMF MallocSR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach SReachTree SReachCjNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~07SR_laws79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8MallocSR~~~~~~kc2HS0elb_remove_laws0cheap_sr_hypskc6PHASE23h5LinuxProcessSemanticsfLinuxProcessSem3Runr76config05hs_SR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~v35rsegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~hj76sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hnadhunspell_scfg37Corelib4Init5Logichs22eq3h5LinuxProcessSemanticsfLinuxProcessSem5Statehtc5Modelhtc5m_fdshtc4m_fs37Corelib4Init9Datatypesii44listii44prodhs23and37Corelib7Numbers7BinNumsil34Npos3h5LinuxProcessSemanticsfLinuxProcessSem2Fsin42Fshtc7FdEntry08hs_MPRES35stdpp9bitvectorbdefinitionsira2bv46Stdlib6ZArith6BinInt1Zitd2le0fhs_LIVE_CNT_MAX0bhs_LIVE_MAXitd3powhtc8m_haltedhtc9m_vm_lazyhtch1m_vm_materializedhtc8m_vmmaps07hs_KRELii46optionhtc6VmMaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~jn86PState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~jre7hs_KREL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8MallocMF~~~~~~kgb3HMFjre8hs_RHEAP08hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~km75blockkm73memil31Zjrebhs_rauxv_ok0bhs_rauxv_okjrechs_lb_remove0chs_lb_removejn84bptrii43nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~lgf5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~lld3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref6RHeapX~~~~~~lq77eh_imgR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefdRMalloc_iface~~~~~~luf5RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~mjc8rauxv_okii44Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mp24cellmp2bcells_bytesmp2acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mv33rdn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nj98rw_cellsira7Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsnobh0word_to_le_bytesii44cons69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~ntf7hcanary" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma SR_laws_proof : ltac2:(zQ "20!k3!ob@1$0@2$1?5HCEIL?4HSEC").
Proof.
  unfold HeapSR_iface.SR_laws. cbn [HeapSR_iface.hs_SR HS]. splits.
  - apply sreach_done.
  - intros Q Q' c H HQ. eapply sreach_mono; eauto.
  - intros Q1 Q2 c H1 H2. eapply sreach_seq; eauto.
  - intros P ms mo HH HL EV. eapply sreach_mono; [eapply (cj_evt_sreach rsegs _ _ mo HH HL EV)|]. intros c [A B]; auto.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_laws_proof : ltac2:(zQ "20!p0!ob@1$0@2$1?5HCEIL?4HSEC").
Proof.
  unfold HeapSR_iface.lb_remove_laws. cbn [HeapSR_iface.hs_lb_remove HS]. unfold lb_remove. splits.
  - intros p A n LB Hn. cbn -[bptr_eqb]. rewrite bptr_eqb_refl. cbn -[bptr_eqb].
    induction LB as [|b LB IH]; [reflexivity|]. cbn -[bptr_eqb]. cbn in Hn.
    destruct (bptr_eqb (MallocBlocks.blk_id b) p) eqn:E; cbn -[bptr_eqb].
    + exfalso. apply Hn. left. apply bptr_eqb_eq in E. exact E.
    + f_equal. apply IH. intros H; apply Hn; right; exact H.
  - intros p b LB Hne. cbn -[bptr_eqb]. destruct (bptr_eqb (MallocBlocks.blk_id b) p) eqn:E; cbn -[bptr_eqb]; [| reflexivity].
    exfalso. apply Hne. apply bptr_eqb_eq in E. exact E.
  - intros p LB b H. induction LB as [|c LB IH]; [exact H|]. cbn -[bptr_eqb] in H.
    destruct (bptr_eqb (MallocBlocks.blk_id c) p); cbn -[bptr_eqb] in H; [right; apply IH; exact H|].
    destruct H as [<-|H]; [left; reflexivity| right; apply IH; exact H].
Qed.

Theorem heap_sr_hyps_of_gap : ltac2:(zQ "30!q0!ob!qe>0@2$2?5HCEIL?4HSEC@2$0?5HCEIL@2$1?5HCEIL?4HSEC").
Proof.
  intros P2. unfold HeapSR_iface.heap_sr_hyps. splits.
  - apply SR_laws_proof.
  - apply KREL_laws_proof.
  - apply MPRES_laws_proof.
  - apply alloc_ok_of_live_proof.
  - exact RHEAP_frame_mirrorX.
  - exact RHEAP_block_range_mirrorX.
  - exact (RHeapX.RHEAP_blocks_disjoint_X _ RHEAP_blocks_disjoint_proof).
  - exact (RHeapX.RHEAP_blocks_nodup_X _ RHEAP_blocks_nodup_proof).
  - exact rauxv_frame_mirror.
  - apply lb_remove_laws_proof.
  - apply (malloc_sr P2).
  - apply (opnew_sr P2).
  - apply free_sr.
  - apply opdel_sr.
  - apply opdel2_sr.
  - apply opdel_null_sr.
  - apply opdel2_null_sr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hx_sr_proof : ltac2:(zQ "60!u3!uc!ob!hif!hn0!hr1>1Q>0$0P>1c$0>0@3$1@2$2?5HCEIL?4HSEC^2^1@4$4$3$5^3^2").
Proof. intros Q c H. exact H. Qed.

Lemma hx_mpres_proof : ltac2:(zQ "d0!ht6!iga!ih3!ihc!ijc!ik4!ikc!imc!ipf!iq5!ir0!ob!it7>2mo$1>3mo'$1>0@3$a@2$b?5HCEIL?4HSEC^2^1@2$6@3$0$8@1$3^2@1$3^3@3$0@1$4@2$5@1$c@1$7#k0$9@1$2^2@1$2^3").
Proof. (intros mo mo' nd_i1; ndestruct nd_i1 as (H1 & H2 & _)). auto. Qed.

(* [comment removed for export] *)
Lemma hx_live_proof : ltac2:(zQ "60!ob!iv5!ikc!ivb!jgc!jh9@2$2@2$1@2$5+2+hf@1$4@2$0?5HCEIL?4HSEC@2$1+il8@1$3@2$0?5HCEIL?4HSEC").
Proof. cbn [HeapSR_iface.hs_LIVE_MAX HeapSR_iface.hs_LIVE_CNT_MAX HS]. unfold HBYTES, HCNT. lia. Qed.

(* [comment removed for export] *)
Lemma hx_krel_vm_proof : ltac2:(zQ "f0!ht6!imc!it7!ijc!iga!ji0!jic!jj9!jkf!jlb!ob!jm4!ik4!jme!jr4>1s$e>2mo$4>3mo'$4>0@3$9@2$a?5HCEIL?4HSEC^3^2>0@3$0@1$b@1$2@1$1#k0@1$5^2@1$5^3>0@3$0@1$3@2$c@1$2@1$1#k0@1$2@1$1#k0@1$6^3@1$6^4>0@3$0@1$3@1$2@1$1#k0@1$7^4@1$7^5>0@3$0$d@1$8^5@1$8^6@3$9@2$a?5HCEIL?4HSEC^8^6").
Proof.
  cbn [HeapSR_iface.hs_KREL HS]. intros s mo mo' K Hh Hl Hm Hv. apply (KM_vm s mo mo' K).
  - ndestruct K as (L & _ & KL & _). destruct (kb_minv _ _ _ KL) as [A1 A2]. split; [rewrite Hl; exact A1 | rewrite Hm; exact A2].
  - rewrite Hh. exact (proj1 (KM_halted_lazy s mo K)).
  - exact Hv.
Qed.

Lemma hm_krel_vm_proof : ltac2:(zQ "f0!ht6!imc!it7!ijc!iga!ji0!jic!jj9!jkf!kg0!kka!jm4!ik4!jme!jr4>1s$e>2mo$4>3mo'$4>0@3$9@2$a?5HCEIL?4HSEC^3^2>0@3$0@1$b@1$2@1$1#k0@1$5^2@1$5^3>0@3$0@1$3@2$c@1$2@1$1#k0@1$2@1$1#k0@1$6^3@1$6^4>0@3$0@1$3@1$2@1$1#k0@1$7^4@1$7^5>0@3$0$d@1$8^5@1$8^6@3$9@2$a?5HCEIL?4HSEC^8^6").
Proof.
  cbn [HeapMF_iface.hs_KREL HMF]. intros s mo mo' K Hh Hl Hm Hv. apply (KMF_vm s mo mo' K).
  - ndestruct K as (L & _ & KL). destruct (km_minv _ _ _ KL) as [A1 A2]. split; [rewrite Hl; exact A1 | rewrite Hm; exact A2].
  - rewrite Hh. exact (proj1 (KMF_halted_lazy s mo K)).
  - exact Hv.
Qed.

(* [comment removed for export] *)
Lemma handover_rheap : ltac2:(zQ "80!ijc!kl1!kld!kka!ob!kr1!kra!jr4>1s$7>2LB@1$0$5>1m$6>0@4$2@2$4?5HCEIL?4HSEC^3^2^1@4$1@2$3?5HCEIL?4HSEC^4^3^2").
Proof. intros s LB m H. exact H. Qed.
Lemma handover_krel : ltac2:(zQ "60!iga!kg0!jlb!kka!ob!jr4>1s$5>2mo$0>0@3$2@2$4?5HCEIL?4HSEC^2^1@3$1@2$3?5HCEIL?4HSEC^3^2").
Proof. cbn [HeapSR_iface.hs_KREL HS HeapMF_iface.hs_KREL HMF]. (intros s mo nd_i2; ndestruct nd_i2 as (L & HR & K & _)). exact (KMF_of_budgeted s mo L HR K). Qed.
Lemma handover_rauxv : ltac2:(zQ "60!ks1!ks6!kt5!kka!ob!kra>1m$5>1B$0>0@3$2@2$4?5HCEIL?4HSEC^2^1@3$1@2$3?5HCEIL?4HSEC^3^2").
Proof. intros m B H. exact H. Qed.
Lemma handover_lb_remove : ltac2:(zQ "80!ijc!kr1!ht6!ku2!kv2!kka!ob!lg0>1p$7>2LB@1$0$1@3$2@1$0$1@3$4@2$6?5HCEIL?4HSEC^2^1@3$3@2$5?5HCEIL?4HSEC^2^1").
Proof. intros p LB. reflexivity. Qed.

(* [comment removed for export] *)
Lemma RINIT_HS : ltac2:(zQ "90!lg8!ll4!lq0!kld!ob!lu4!mj3!kr1!jr4>1s$8>1m$2>0@5$6?5HCEIL?4HSEC^2@1$0$1^1>0@1$5^2@4$3@2$4?5HCEIL?4HSEC^4@1$0$7^3").
Proof. intros s m H I. split; [exact H| exact I]. Qed.
Lemma AUXINIT_HS : ltac2:(zQ "50!ks1!lq0!kt5!ob!mne>1m$1>1B$0>0@4$4?5HCEIL?4HSEC^2^1@3$2@2$3?5HCEIL?4HSEC^3^2").
Proof. intros m B H. exact H. Qed.

End HCW.


From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RBand.

Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rw_cells_rdn1 : ltac2:(zQ "e0!imc!it7!ijc!jm4!hif!moa!ht6!ks1!mse!mt6!mu5!nj2!nn4!no0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$7>2cs@1$2$8>0@4$c$4^3^2^1@3$6@1$3@1$2@1$1@1$0#8@4$b$4^4@2$d@1$0#k0^3@1$a^2@2$5@1$2@1$1@1$0#8@1$9^2").
Proof.
  intros m A cs [[WF BA] _].
  pose proof (bytes_at_rdn rsegs m A (cells_bytes cs) 0 (cells_size cs) BA) as R.
  rewrite Z.add_0_r, firstn_all2 in R; [| cbn [skipn]; rewrite cells_bytes_length by exact WF; lia].
  apply R. cbn [skipn]. rewrite cells_bytes_length by exact WF. lia.
Qed.

Lemma hx_statics_proof : ltac2:(zQ "h20!imc!it7!ijc!no0!moa!jm4!ht6!nj2!hif!ikc!ns2!nt7!lg8!ll4!lq0!ohc!mj3!jr4>1s$h1>2LB@1$2$d>1m$e>0@5$h0?5HCEIL?4HSEC^3^2^1@2$9@3$6@1$5@1$2@1$1@1$0#8@4$7$8^2@2$3@1$0#k0+hirpkbN1@2$4@1$2@1$1@1$0#8@3$b@1$1@1$0#8@2$3@1$0#8Z@1$c@1$1@1$0#8@2$9@3$6@1$5@1$2@1$1@1$0#8@4$7$8^2@2$3@1$0#k0+vonn0N8@2$4@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hirmv8@3$6@1$5@1$2@1$1@1$0#8@4$7$8^2@2$3@1$0#k0+hirmv8N8@2$4@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0@1$f?4HSEC").
Proof.
  (intros s LB m nd_i3; ndestruct nd_i3 as (st & LB0 & _ & _ & MR & _)).
  ndestruct MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  split; [| split].
  - exact (rw_cells_rdn1 _ _ _ G2).
  - exact (rw_cells_rdn1 _ _ _ G4).
  - exact (rw_cells_rdn1 _ _ _ G5).
Qed.

End HCW2.

