(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/U/Prog/FuzzDup.v at
   bc49657c087aa7d6ab0af1ffb2cb67fa08b15de1; the shared fuzz.h text copied unchanged but for its module path (fuzz_egress). *)
(* New for reac-repacer. SHARED TEXT of the project: the fuzz.h idiom

     static inline uint8_t *fuzz_dup(const uint8_t *p, size_t n)
     { uint8_t *b = malloc(n ? n : 1); if (!b) abort(); if (n) memcpy(b, p, n); return b; }

   which every reac-repacer harness inlines, stated once, with no address of any image in it: the size it asks the
   allocator for, the room that size needs, and the fact its abort rests on -- the allocator contract never returns
   NULL when there is room, so the `if (!b) abort();` arm is unreachable. The instruction walk of one call site stays
   with that site's function (fuzz_uci: lib/Prog/check_value.v), because the inlined code differs per binary.
   Reviewed alone before a second prover uses it.
   This file is lib/Prog/FuzzDup.v word for word with only its imports moved to lib/U: its
   statements are over the allocator API of lib/U/Contract.v, a separate copy of lib/Contract.v, so the UBSan walk
   of check_value (lib/U/Prog/check_value.v) cannot use the plain file. No image value is in it. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract.
Import ListNotations.
Local Open Scope Z_scope.

(* malloc(n ? n : 1) *)
Definition fuzz_dup_size (n : Z) : Z := if n =? 0 then 1 else n.

Lemma fuzz_dup_size_range : forall n, 0 <= n -> 0 < fuzz_dup_size n /\ fuzz_dup_size n <= n + 1.
Proof.
  intros n Hn. unfold fuzz_dup_size. destruct (Z.eqb_spec n 0) as [->|H]; lia.
Qed.

(* the room the idiom needs of the allocator budget *)
(* n bound: AllocRoom.room_slots_big's, so (n ? n : 1) <= 2^28 - 2^13; covers fuzz.h FUZZ_INPUT_MAX = 2^26 *)
Lemma fuzz_dup_room : forall b n, 0 <= n <= 2 ^ 28 - 2 ^ 13 - 1 ->
  sb_live b + 1 <= sb_cap b <= CAPMAX -> 0 <= sb_bytes b -> sb_bytes b + n + 1 <= 2 ^ 40 ->
  room_slots b (fuzz_dup_size n).
Proof.
  intros b n Hn Hc Hb Hbn. pose proof (fuzz_dup_size_range n ltac:(lia)) as [H1 H2].
  apply room_slots_big; lia.
Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* The abort of `if (!b) abort();` is unreachable: on the allocator contract's own postcondition the pointer the
   idiom tests is a real heap block, never 0. *)
Lemma fuzz_dup_no_null : forall K L A regs mem md n b c',
  malloc_ret B API K L A regs mem md n b c' ->
  exists L' A' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    getr regs' 10 = Z_to_bv 64 res /\
    res <> 0 /\ 4096 <= res /\ res + n <= alloc_ceiling /\ res mod 16 = 0 /\
    In (res, n) (blocks L' A').
Proof.
  intros K L A regs mem md n b c'
    (L' & A' & regs' & mem' & md' & res & -> & Hpost & G10 & Hnz & Hal & (Hlo & Hhi & _)
     & (b1 & b2 & Eb1 & Eb2) & _).
  exists L', A', regs', mem', md', res.
  split; [reflexivity|]. split; [exact G10|]. split; [exact Hnz|]. split; [exact Hlo|].
  split; [exact Hhi|]. split; [exact Hal|].
  rewrite Eb1. apply in_or_app. right. left. reflexivity.
Qed.

End K.
