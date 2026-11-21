(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.


Section CANSEC1. Context {rc : runConstT}.


Definition clear_range (st : mstate) (lo n : Z) : Prop :=
  forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof.
  intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.


Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= ATOP.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma gr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.

End GROW.

End CANSEC1.
