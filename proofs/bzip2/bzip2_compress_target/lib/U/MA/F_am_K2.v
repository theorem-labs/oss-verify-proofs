(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.F_ntf_B.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition clear_range (st : mstate) (lo n : Z) : Prop :=
  forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
  intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : mrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
