(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.Footprint — concrete address regions and their disjointness.

    EXPLORATION / PROTOTYPE.

    This is the SHARED VOCABULARY for "these two memory accesses cannot
    interfere".  It is deliberately tiny, deliberately CONCRETE (a region
    is a pair of [Z] bounds on [bv_unsigned], not a symbolic expression),
    and deliberately independent of [Common.SymExec]: the reflective
    executor discharges its cross-base [SCDisjoint] obligations through
    it, and a Hoare-style frame rule can use exactly the same [region] /
    [rg_disj] pair for its separating conjunction, without either
    importing the other.

    THE INTERFACE, in three lines:

    - [region] = a half-open byte interval [[rg_lo, rg_hi)] of the 64-bit
      address space, with [rg_lo <= rg_hi] and [0 <= rg_lo],
      [rg_hi <= 2^64] carried as the well-formedness predicate [rg_wf];
    - [covers r a n] = "the [n] bytes at address [a] lie inside [r]";
    - [rg_disj r1 r2] = "[r1] and [r2] do not overlap".

    Everything else is one [lia].  The point is not the theory (there is
    none) but that a per-binary proof states its memory layout ONCE, as a
    handful of [region]s with pairwise [rg_disj] facts, instead of
    re-deriving an address inequality at every load.

    The three regions every one of the examples has are built here:
    [stack_rg] (the [rsp - K .. rsp] frame window), [seg_rg] (a writable
    ELF segment: .data/.sbss/.bss), and [heap_rg] (a brk/mmap grant
    [[base, cur)]).  A bump allocator moving [cur] keeps the SAME region
    name with a larger [rg_hi]: [covers] is monotone in the region
    ([covers_mono]), so nothing downstream re-proves. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1. Regions                                                                *)
(* ######################################################################### *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(** [n] bytes at [a] are inside [r].  Stated on [bv_unsigned] so that the
    caller's arithmetic facts ([sp_window_lo <= bv_unsigned rsp], an
    image's segment bounds) apply directly. *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.

(** Growing a region (a bump allocator raising [cur]) preserves coverage. *)
Lemma covers_mono : forall r r' a n,
  covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.

(* ######################################################################### *)
(* 2. The three consequences a memory proof actually needs                   *)
(* ######################################################################### *)

(** (a) No-overflow: an access inside a well-formed region does not wrap
    the address space.  This is the [SCFit] obligation of [SymExec]. *)
Lemma covers_nowrap : forall r a n,
  rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.

(** (b) Disjointness of two accesses in disjoint regions, in exactly the
    [rdn_wbytes_disjoint] / [rdn_wbytes_below] shape. *)
Lemma covers_disj : forall r1 r2 a1 n1 a2 n2,
  rg_disj r1 r2 -> covers r1 a1 n1 -> covers r2 a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.

(** (c) Two accesses in the SAME region are disjoint when their offsets
    say so.  This is the case the reflective executor decides by [Z]
    arithmetic; the region supplies only the no-wrap fact. *)
Lemma covers_same_disj : forall r a1 n1 a2 n2,
  covers r a1 n1 -> covers r a2 n2 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
  \/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. auto. Qed.

(* ######################################################################### *)
(* 3. The regions the examples have                                          *)
(* ######################################################################### *)

(** The current frame window: [K] bytes below [sp], plus the [above]
    bytes at and above it that the startup image occupies (argv/envp).
    Splitting the two is what lets a [sd] into the frame be disjoint from
    a [ld] of [argc] at [sp] without any extra hypothesis. *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(** A writable ELF segment (.data / .sbss / .bss): plain literal bounds. *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(** A heap grant [[base, cur)].  [base] is symbolic (an mmap/brk result),
    [cur] moves as a bump allocator allocates. *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

Lemma heap_rg_bump : forall base cur cur' a n,
  cur <= cur' -> covers (heap_rg base cur) a n -> covers (heap_rg base cur') a n.
Proof.
  intros base cur cur' a n Hle H.
  apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.

(** A layout is a list of regions that are pairwise disjoint and
    well-formed.  This is the thing a per-binary proof states once. *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).
