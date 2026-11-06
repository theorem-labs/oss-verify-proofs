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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Prog AllocTop KLink KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface
     MallocMF_klink MallocMF MallocMF_init MallocSR MallocSR_init MallocSR_hyps MallocSR_closed.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require MainDefs LibDiagKn.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs~~~~~~0aheap_extra79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8MallocSR~~~~~~k72HS0bheap_extraM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8MallocMF~~~~~~p83HMF08handover37Corelib4Init9Datatypesu73nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~hg55block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hl33mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~hpd8hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref6RHeapX~~~~~~huc7eh_imgR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefdRMalloc_iface~~~~~~ij45RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~io15block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~it46PState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefdMallocSR_hyps~~~~~~jha8RINIT_HS37Corelib7Numbers7BinNumsjma1Zhpdbhs_rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~jp78rauxv_okjhaaAUXINIT_HSjma4Npos35stdpp9bitvectorbdefinitionsjvb2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~khe5rsegs37Corelib4Init5Logickm32eq3h5LinuxProcessSemanticsfLinuxProcessSem3Runkndh1segments_reservedknd9valid_brkknd8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSem5Statekt89ProcInputkt8ainit_modelkt8estack_max_sizekt88with_tid69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ljf5hceilhpd7hs_KRELit47ps_initit49reservedZ46Stdlib6ZArith6BinInt1Zlq62lelq63powlq63subjvbbbv_unsignedhpdcheap_sr_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3ReffMallocSR_closed~~~~~~lv1h3heap_sr_hyps_closed" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

  (* [comment removed for export] *)
  Theorem heap_extra_HS : ltac2:(zQ "20!jb!o6@1$0@2$1?5HCEIL?4HSEC").
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
  Theorem heap_extraM_HMF : ltac2:(zQ "20!ob!t7@2$0?5HCEIL@2$1?5HCEIL?4HSEC").
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
  Theorem handover_HS_HMF : ltac2:(zQ "30!td!t7!o6@2$0@2$2?5HCEIL?4HSEC@2$1?5HCEIL?4HSEC").
  Proof.
    split; [| split; [| split]].
    - apply handover_rheap.
    - apply handover_krel.
    - apply handover_rauxv.
    - apply handover_lb_remove.
  Qed.

  (* [comment removed for export] *)
  Definition RINIT_HS : ltac2:(zQ "90!vf!hka!hp6!hu0!o6!ii9!in8!isb!jh0>1s$8>1m$2>0@5$6?5HCEIL?4HSEC^2@1$0$1^1>0@1$5^2@4$3@2$4?5HCEIL?4HSEC^4@1$0$7^3") := ltac2:(zQ "10!jle@2$0?5HCEIL?4HSEC").
  Definition AUXINIT_HS : ltac2:(zQ "50!jo3!hp6!jo8!o6!jt9>1m$1>1B$0>0@4$4?5HCEIL?4HSEC^2^1@3$2@2$3?5HCEIL?4HSEC^3^2") := ltac2:(zQ "10!ju5@2$0?5HCEIL?4HSEC").

  (* [comment removed for export] *)
  Theorem KINIT_HS : ltac2:(zQ "h50!jv3!kh8!kla!jo3!kn7!kq9!krf!ksc!lg6!lh3!li1!lj3!lna!lo3!o6!loe!lp9!lre!ls4!lsb!lt2>3tid@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>2sp@1$1@1$0#k0>3lim$3>2pi$8>0@2$6$2^5>0@1$7^4>0@2$h1@2$h2+2+i2^4>0@3$4$3@2$h3@2$h4@1$0#k0^6$a@1$c?5HCEIL@3$d@2$e?5HCEIL?4HSEC@3$f?5HCEIL?4HSEC@1$h0$2@2$b^a@6$9@1$5$2^9^8^7^6^5").
  Proof. cbn [hs_KREL HS]. intros. apply KM_init; assumption. Qed.

  (* [comment removed for export] *)
  Definition heap_sr_hyps_closed : ltac2:(zQ "20!lu1!o6@2$0?5HCEIL@2$1?5HCEIL?4HSEC") := ltac2:(zQ "10!mj7@2$0?5HCEIL?4HSEC").

End HCW.
