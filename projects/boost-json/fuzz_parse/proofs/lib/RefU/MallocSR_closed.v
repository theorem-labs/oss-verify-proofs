(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim STree Malloc MallocCtrl Prog KInv MI_Inv MI_Contracts GapGrid KLink KLink3
  KBudgetB1 KBudgetB2 KBudgetB3 KBudgetA.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_inv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMalloc_iface HeapSR_iface MallocMF_klink MallocMF MallocSR MallocSR_hyps.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RBand.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~03blk37Corelib4Init9Datatypesk36lengthk34list37Corelib4Init5Logicmb2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~o45blockk33natmb3and37Corelib7Numbers7BinNumstd1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentfMallocFacts_inv~~~~~~va4CORR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapSR_iface~~~~~~hk98lb_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9KBudgetB2~~~~~~hp94sumw05bsize79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hu96mstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~ij15block36Stdlib7SortingbPermutationio5bPermutationhk9cheap_sr_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8MallocSR~~~~~~is02HS" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma corr_sizes : ltac2:(zQ "d0!je!lb!m4!nf!s9!t1!t7!v6!hk2!hod!hta!hu2!ii7>2st$c>2LB@1$2$4>2BL@1$2$0>0@3$8^3^2^1@2$6@3$3$7@1$9^3@3$a$0$b^2@3$3$5@2$1$4^3@2$1$0^2").
Proof. intros st LB BL.
  induction 1 as [|b k LB' BL' [_ [E _]] H IH]; [split; reflexivity|].
  destruct IH as [IH1 IH2]. change (HeapSR_iface.lb_bytes (b :: LB')) with (RMalloc_iface_stmt.blk_size b + HeapSR_iface.lb_bytes LB').
  rewrite sumw_cons, IH1. cbn [length]. rewrite IH2. unfold blk_size in E. unfold RMalloc_iface_stmt.blk_size. rewrite E. split; reflexivity.
Qed.

Lemma lb_bytes_perm : ltac2:(zQ "60!inc!m4!hod!nf!v6!iq1>2LB@1$1$0>3LB'@1$1$0>0@3$5$0^2^1@3$3$4@1$2^3@1$2^2").
Proof. intros LB LB'. intros P. change (sumw RMalloc_iface_stmt.blk_size LB = sumw RMalloc_iface_stmt.blk_size LB'). apply sumw_perm. exact P. Qed.

Theorem phase2 : PHASE2.
Proof.
  intros s LB m L n HR HRC Hn HB HL HT HK.
  ndestruct HR as (st & LB0 & HP & Hst & _ & [_ AR]).
  destruct (areach_inv _ _ _ AR) as (L1 & LS1 & BL1 & I1 & _ & _ & _ & CORR1).
  destruct (hreach_sim _ _ HRC) as (st2 & BL2 & LS2 & Est2 & I2 & _ & CAP2).
  assert (ES : strip st = strip st2) by (rewrite Hst, Est2; reflexivity).
  pose proof (areas_cap_num _ CAP2) as A2.
  ndestruct (footprint2 st2 L BL2 LS2 st L1 BL1 LS1 522 I2 I1 ES A2 ltac:(lia)) as (FT & FC & FS).
  destruct (corr_sizes _ _ _ CORR1) as [SZ LEN].
  rewrite <- (lb_bytes_perm _ _ HP) in HB. rewrite SZ in HB. rewrite <- (Permutation_length HP), LEN in HL.
  assert (SNN : 0 <= sumw bsize BL1).
  { apply sumw_nonneg. intros k Hk. destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I1)))))) k Hk) as (_ & _ & _ & _ & B0 & _). exact B0. }
  assert (ECTX : ctx (ps_m s) = s_ctx st2) by (rewrite <- Est2; reflexivity).
  assert (SH2 : 0 <= c_meta_alloc_shift (ctx (ps_m s)) <= 10) by (rewrite ECTX; exact FS).
  exists (CB_malloc (ps_m s) n), CK_malloc.
  pose proof (CB_malloc_le (ps_m s) n ltac:(unfold HBYTES in HB; lia) ltac:(lia)) as CBL.
  assert (P11 : 2^(c_meta_alloc_shift (ctx (ps_m s)) + 1) <= 2^11) by (apply Z.pow_le_mono_r; lia).
  assert (CB0 : 0 <= CB_malloc (ps_m s) n).
  { unfold CB_malloc, GBIG, GB, MCOST. rewrite shiftl2_eq by lia.
    pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (ctx (ps_m s)) + 1) ltac:(lia) ltac:(lia)).
    destruct (_ <=? _); [pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)); unfold IB, UNIT, PGSZ in *; lia| unfold PGSZ; lia]. }
  split; [exact CB0|]. split; [unfold CK_malloc; lia|]. split; [apply tbound_cmalloc; [unfold HBYTES in HB; lia| lia]|].
  unfold HBYTES, HCNT, BUDCAP, RESV_MAX, GRID_J, CK_malloc, GB, IB, UNIT, PGSZ in *.
  split; [| lia].
  eapply Z.le_trans; [apply Z.add_le_mono; [exact FT| exact CBL]|].
  change (2^34) with 17179869184. change (2^11) with 2048 in *. change (2^20) with 1048576 in *. change (2^32) with 4294967296 in *.
  pose proof (Z.le_max_l (n + 4 + 16 + 4096) 1048576). pose proof (Z.le_max_r (n + 4 + 16 + 4096) 1048576).
  destruct (Z.max_spec (n + 4 + 16 + 4096) 1048576) as [[_ ->]|[_ ->]]; nia.
Qed.

(* [comment removed for export] *)
Theorem heap_sr_hyps_closed : ltac2:(zQ "20!ir0!jg0@2$0?5HCEIL@2$1?5HCEIL?4HSEC").
Proof. exact (heap_sr_hyps_of_gap phase2). Qed.

(* [comment removed for export] *)

End HCW.

(* [comment removed for export] *)
