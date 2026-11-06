(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require MallocFacts_inv.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require MallocFacts_inv3.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.

#[using="Type"] Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

#[using="Type"] Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

#[using="Type"] Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis LO : ATOP <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.
End FP.

End CANSEC1.
