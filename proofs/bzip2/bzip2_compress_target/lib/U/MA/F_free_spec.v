(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B Malloc_iface. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocRep MallocTree MallocBlocks MallocFacts_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_Bpres OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_ntf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.F_free_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv3.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : mrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : pres_except (fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904) m m'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
