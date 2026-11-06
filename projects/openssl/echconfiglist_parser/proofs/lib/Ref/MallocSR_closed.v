(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc MallocCtrl Prog KInv MI_Inv MI_Contracts GapGrid KLink KLink3
  KBudgetB1 KBudgetB2 KBudgetB3 KBudgetA.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_inv.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RMalloc_iface HeapSR_iface MallocSR MallocSR_hyps MallocSR_x.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RBand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma corr_sizes st LB BL : CORR st LB BL -> HeapSR_iface.lb_bytes LB = sumw bsize BL /\ length LB = length BL.
Proof. try hcb. try hsb.
  induction 1 as [|b k LB' BL' [_ [E _]] H IH]; [split; reflexivity|].
  destruct IH as [IH1 IH2]. change (HeapSR_iface.lb_bytes (b :: LB')) with (RMalloc_iface_stmt.blk_size b + HeapSR_iface.lb_bytes LB').
  rewrite sumw_cons, IH1. cbn [length]. rewrite IH2. unfold blk_size in E. unfold RMalloc_iface_stmt.blk_size. rewrite E. split; reflexivity.
Qed.

Lemma lb_bytes_perm LB LB' : Permutation LB LB' -> HeapSR_iface.lb_bytes LB = HeapSR_iface.lb_bytes LB'.
Proof. try hcb. try hsb. intros P. change (sumw RMalloc_iface_stmt.blk_size LB = sumw RMalloc_iface_stmt.blk_size LB'). apply sumw_perm. exact P. Qed.

(* [comment removed for export] *)
Lemma corr_big st LB BL : CORR st LB BL -> HeapSR_iface.lb_big LB = nbig BL.
Proof. try hcb. try hsb.
  unfold nbig. induction 1 as [|b k LB' BL' [_ [E _]] H IH]; [reflexivity|].
  change (HeapSR_iface.lb_big (b :: LB')) with (HeapSR_iface.big1 (RMalloc_iface_stmt.blk_size b) + HeapSR_iface.lb_big LB').
  rewrite IH. cbn [List.filter]. unfold HeapSR_iface.big1, HeapSR_iface.BIGB, bigb. unfold blk_size in E. unfold RMalloc_iface_stmt.blk_size. rewrite E.
  destruct (2028 <? bsize k); cbn [length]; [rewrite Nat2Z.inj_succ|]; lia.
Qed.

Lemma lb_big_perm LB LB' : Permutation LB LB' -> HeapSR_iface.lb_big LB = HeapSR_iface.lb_big LB'.
Proof. try hcb. try hsb.
  intros P. change (sumw (fun b => HeapSR_iface.big1 (RMalloc_iface_stmt.blk_size b)) LB = sumw (fun b => HeapSR_iface.big1 (RMalloc_iface_stmt.blk_size b)) LB').
  apply sumw_perm. exact P.
Qed.

Lemma big1_range n : 0 <= HeapSR_iface.big1 n <= 1.
Proof. unfold HeapSR_iface.big1. destruct (_ <? _); lia. Qed.

Theorem phase2 : PHASE2.
Proof. try hcb. try hsb.
  intros s LB m L n HR HRC Hn HB HL HG HT HK.
  destruct HR as (st & LB0 & HP & Hst & _ & [_ AR] & _).
  destruct (areach_inv _ _ _ AR) as (L1 & LS1 & BL1 & I1 & _ & _ & _ & CORR1).
  destruct (hreach_sim _ _ HRC) as (st2 & BL2 & LS2 & Est2 & I2 & _ & CAP2).
  assert (ES : strip st = strip st2) by (rewrite Hst, Est2; reflexivity).
  pose proof (areas_cap_num _ CAP2) as A2.
  destruct (footprint2 st2 L BL2 LS2 st L1 BL1 LS1 2012 I2 I1 ES A2 ltac:(lia)) as (FT & FC & FS).
  destruct (corr_sizes _ _ _ CORR1) as [SZ LEN].
  rewrite <- (lb_bytes_perm _ _ HP) in HB. rewrite SZ in HB. rewrite <- (Permutation_length HP), LEN in HL.
  rewrite <- (lb_big_perm _ _ HP), (corr_big _ _ _ CORR1) in HG. pose proof (big1_range n) as B1R.
  assert (SNN : 0 <= sumw bsize BL1).
  { apply sumw_nonneg. intros k Hk. destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 I1)))))) k Hk) as (_ & _ & _ & _ & B0 & _). exact B0. }
  assert (ECTX : ctx (ps_m s) = s_ctx st2) by (rewrite <- Est2; reflexivity).
  assert (SH2 : 0 <= c_meta_alloc_shift (ctx (ps_m s)) <= 11) by (rewrite ECTX; exact FS).
  exists (CB_malloc (ps_m s) n), CK_malloc.
  pose proof (CB_malloc_le (ps_m s) n ltac:(unfold HBYTES in HB; lia) ltac:(lia)) as CBL.
  assert (P11 : 2^(c_meta_alloc_shift (ctx (ps_m s)) + 1) <= 2^12) by (apply Z.pow_le_mono_r; lia).
  assert (CB0 : 0 <= CB_malloc (ps_m s) n).
  { unfold CB_malloc, GBIG, GB, MCOST. rewrite shiftl2_eq by lia.
    pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (ctx (ps_m s)) + 1) ltac:(lia) ltac:(lia)).
    destruct (_ <=? _); [pose proof (mmap_len_ge (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)); unfold IB, UNIT, PGSZ in *; lia| unfold PGSZ; lia]. }
  unfold HBYTES, HCNT, HBIG, BUDCAP, CBMAX, RESV_MAX, GRID_J, CK_malloc, GB, IB, UNIT, PGSZ in *.
  change (2^31) with 2147483648 in *. change (2^12) with 4096 in *. change (2^16) with 65536 in *.
  change (2^20) with 1048576 in *. change (2^30) with 1073741824 in *.
  pose proof (Z.le_max_l (n + 4 + 16 + 4096) 1048576). pose proof (Z.le_max_r (n + 4 + 16 + 4096) 1048576).
  assert (CBM : CB_malloc (ps_m s) n <= 1073741824 + 4 + 16 + 4096 + 2 * 4096 + 4096 * 4096).
  { eapply Z.le_trans; [exact CBL|]. destruct (Z.max_spec (n + 4 + 16 + 4096) 1048576) as [[_ ->]|[_ ->]]; nia. }
  split; [lia|]. split; [lia|]. split; [apply tbound_cmalloc; lia|].
  split; [| lia].
  (* [comment removed for export] *)
  eapply Z.le_trans; [apply Z.add_le_mono; [exact FT| exact CBL]|].
  destruct (Z.max_spec (n + 4 + 16 + 4096) 1048576) as [[_ ->]|[_ ->]]; lia.
Qed.

(* [comment removed for export] *)
Theorem heap_sr_hyps_closed : HeapSR_iface.heap_sr_hyps HS.
Proof. try hcb. try hsb. exact (heap_sr_hyps_of_gap phase2). Qed.

(* [comment removed for export] *)
Theorem malloc_sr_closed : HeapSR_iface.malloc_sr_stmt HS. Proof. try hcb. try hsb. exact (malloc_sr phase2). Qed.

(* [comment removed for export] *)
Theorem realloc_sr_closed : HeapSR_iface.realloc_sr_stmt HS. Proof. try hcb. try hsb. exact (realloc_sr phase2). Qed.
Theorem aalloc_sr_closed : HeapSR_iface.aalloc_sr_stmt HS. Proof. try hcb. try hsb. exact (aalloc_sr phase2). Qed.

Theorem heap_sr_hyps_x_closed : HeapSR_iface.heap_sr_hyps_x HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.heap_sr_hyps_x.
  split; [exact heap_sr_hyps_closed|]. split; [exact realloc_sr_closed|]. split; [exact aalloc_sr_closed|].
  split; [exact rauxv_elim_proof|]. split; [exact statics_of_RHEAP_proof|]. split; [exact RHEAP_perm_law_proof| exact RHEAP_slack_law_proof].
Qed.

End HCW.

