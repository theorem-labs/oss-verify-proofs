(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Prog AllocTop KLink KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface MallocMF_klink MallocMF MallocMF_init MallocSR MallocSR_init MallocSR_hyps MallocSR_closed.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require MainDefs LibDiagKn.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8MallocSR~~~~~~02HS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs~~~~~~k4aheap_extra79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8MallocMF~~~~~~oe3HMFk4bheap_extraMk48handover37Corelib4Init9Datatypesud3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~hgb5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hl93mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapSR_iface~~~~~~hq38hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU6RHeapX~~~~~~hv37eh_imgR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdRMalloc_iface~~~~~~ijc5RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~ioa5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ite6PState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdMallocSR_hyps~~~~~~ji48RINIT_HS37Corelib7Numbers7BinNumsjn51Zhq3bhs_rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~jq28rauxv_okji4aAUXINIT_HSjn54Npos35stdpp9bitvectorbdefinitionskg72bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~kia5rsegs37Corelib4Init5Logickn02eq3h5LinuxProcessSemanticsfLinuxProcessSem3Runkoah1segments_reservedkoa9valid_brkkoa8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSem5Stateku59ProcInputku5ainit_modelku5estack_max_sizeku58with_tid69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lkc5hceilhq37hs_KRELite7ps_initite9reservedZ46Stdlib6ZArith6BinInt1Zlr32lelr33powlr33subkg7bbv_unsignedhq3cheap_sr_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUfMallocSR_closed~~~~~~lveh3heap_sr_hyps_closed" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

  (* [comment removed for export] *)
  Theorem heap_extra_HS : ltac2:(zQ "20!k0!o1@1$1@2$0?5HCEIL?4HSEC").
  Proof.
    split.
    - apply hx_sr_proof.
    - apply hx_mpres_proof.
    - apply hx_live_proof.
    - apply hx_krel_vm_proof.
    - intros s LB m RH. npose (hx_statics_proof s LB m (proj1 RH)) as (H1 & H2 & H3).
      split; [exact H1|]. split; [exact H2|]. exists hcanary. split; [exact H3 | hsb; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem heap_extraM_HMF : ltac2:(zQ "20!se!t4@2$1?5HCEIL@2$0?5HCEIL?4HSEC").
  Proof.
    split.
    - intros Q c H. exact H.
    - apply SR_laws_proof.
    - intros s mo K. exact (KMF_halted_lazy s mo K).
    - (intros mo mo' nd_i1; ndestruct nd_i1 as (H1 & H2 & _)). auto.
    - apply MallocMF.MPRES_laws_proof.
    - apply hm_krel_vm_proof.
    - intros s LB m RH. npose (hx_statics_proof s LB m (proj1 RH)) as (H1 & H2 & H3).
      split; [exact H1|]. split; [exact H2|]. exists hcanary. split; [exact H3 | hsb; lia].
    - apply free_mf.
    - apply RHEAP_frame_proof'.
    - apply RHEAP_block_range_proof'.
    - apply RHEAP_blocks_nodup_proof'.
    - apply RHEAP_perm_proof.
    - apply rauxv_frame_proof.
    - apply MallocMF.lb_remove_laws_proof.
  Qed.

  (* [comment removed for export] *)
  Theorem handover_HS_HMF : ltac2:(zQ "30!se!k0!u2@2$2@2$1?5HCEIL?4HSEC@2$0?5HCEIL?4HSEC").
  Proof.
    split; [| split; [| split]].
    - apply handover_rheap.
    - apply handover_krel.
    - apply handover_rauxv.
    - apply handover_lb_remove.
  Qed.

  (* [comment removed for export] *)
  Definition RINIT_HS : ltac2:(zQ "90!hg5!hl0!hpc!hu7!k0!ij1!io1!it5!jha>1s$8>1m$2>0@5$6?5HCEIL?4HSEC^2@1$0$1^1>0@1$5^2@4$3@2$4?5HCEIL?4HSEC^4@1$0$7^3") := ltac2:(zQ "10!jm9@2$0?5HCEIL?4HSEC").
  Definition AUXINIT_HS : ltac2:(zQ "50!joe!hpc!jp3!k0!ju5>1m$1>1B$0>0@4$4?5HCEIL?4HSEC^2^1@3$2@2$3?5HCEIL?4HSEC^3^2") := ltac2:(zQ "10!jv1@2$0?5HCEIL?4HSEC").

  (* [comment removed for export] *)
  Theorem KINIT_HS : ltac2:(zQ "h50!jvf!ki4!km7!joe!ko4!kr6!ksc!kt9!lh3!li0!lie!lk0!lo7!lp0!k0!lpb!lq6!lsb!lt1!lt8!ltf>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>2sp@1$1@1$0#k0>3lim$3>2pi$8>0@2$6$2^5>0@1$7^4>0@2$h1@2$h2+2+i2^4>0@3$4$3@2$h3@2$h4@1$0#k0^6$a@1$c?5HCEIL@3$d@2$e?5HCEIL?4HSEC@3$f?5HCEIL?4HSEC@1$h0$2@2$b^a@6$9@1$5$2^9^8^7^6^5").
  Proof. cbn [hs_KREL HS]. intros. apply KM_init; assumption. Qed.

  (* [comment removed for export] *)
  Definition heap_sr_hyps_closed : ltac2:(zQ "20!lue!k0@2$0?5HCEIL@2$1?5HCEIL?4HSEC") := ltac2:(zQ "10!mk5@2$0?5HCEIL?4HSEC").

End HCW.
