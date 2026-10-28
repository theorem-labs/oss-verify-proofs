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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp MallocKit_A2 Malloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W10.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W10.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma small_cnt_range sc i : 0 <= sc < 9 -> 0 <= i < 3 -> 4 <= small_cnt sc i <= 31.
Proof.
  intros Hsc Hi.
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). cps_destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). cps_destruct Hi' as (k & -> & Hk).
  unfold small_cnt. rewrite !Nat2Z.id.
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End HALVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma med_cnt_range i : 0 <= i < 4 -> 20 <= med_cnt i <= 32 /\ med_cnt i mod 4 = 0.
Proof.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed.

Lemma halve_even_range F : forall cnt u, 1 <= cnt -> 1 <= halve_even F cnt u <= cnt.
Proof.
  induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma halve_big_range F : forall cnt sz, 0 <= cnt -> 0 <= halve_big F cnt sz <= cnt.
Proof.
  induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
  destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : mrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

(* [comment removed for export] *)

(* [comment removed for export] *)
End COUNT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

Lemma cnt1_range : 0 <= cnt1 <= 32.
Proof. unfold cnt1. destruct (_ && _); lia. Qed.

(* [comment removed for export] *)
End CNT2.

End ACeilS1.
