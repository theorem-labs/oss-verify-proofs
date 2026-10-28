(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srliw_small a k : 0 <= a < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 a) k) = Z.shiftr a k.
Proof.
  intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). rewrite Z.mod_small by lia.
  apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma lor_small n a b : 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
  - apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed.

Lemma shiftr_small n a k : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
  intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stc_q (q : Z) : Z :=
  if q <? 10 then q else
    let x := q + 1 in
    let i := 4 * Z.log2 x - 4 in
    let i := if size_class (i + 1) <? x then i + 2 else i in
    if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool :=
  let sc := stc_q q in (0 <=? sc) && (sc <? 48) && (q + 1 <=? size_class sc)
                    && ((q <? 10) || ((3 <=? Z.log2 (q + 1)) && (Z.log2 (q + 1) <=? 12))).
Lemma stc_check_true : forallb stc_fn (zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_q n : 0 <= n -> size_to_class n = stc_q ((n + 3) / 16).
Proof.
  intros Hn. unfold size_to_class, stc_q, IB, clz32.
  replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
  set (q := (n + 3) / 16). cbv zeta.
  replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
  reflexivity.
Qed.

Lemma size_to_class_props n : 0 <= n < MMAP_THRESHOLD ->
  0 <= size_to_class n < 48 /\ n + 4 <= 16 * size_class (size_to_class n)
  /\ (10 <= (n + 3) / 16 -> 3 <= Z.log2 ((n + 3) / 16 + 1) <= 12).
Proof.
  intros Hn. unfold MMAP_THRESHOLD in Hn. rewrite size_to_class_q by lia.
  assert (Q : 0 <= (n + 3) / 16 < 8191) by (Z.div_mod_to_equations; lia).
  pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
  apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
  apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
