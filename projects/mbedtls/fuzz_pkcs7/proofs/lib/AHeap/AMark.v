(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the heap's room invariant restated for LPS revision #38. *)
(* Modified by Theorem Labs, 2026-11: heap_mark_place builds its fit witness from the mark's own window under mmap_top instead of taking one; taken from projects/mbedtls/fuzz_pkcs7/proofs/lib/AHeap/AMark.v, lines 80-227, 232-251 and 257-519, as in the LPS 727298f3 update. *)

(** * The heap's room invariant: a SPLIT LEDGER WITH A DESCENDING HIGH MARK

    WHY THIS FILE EXISTS.  Until revision #38 the heap chose its own
    grant addresses — [AFreeSlot.free_slot_exists_B] returned a free
    page-aligned slot at [bottomup_floor + j*S] and [AVm.room_gen]
    claimed [ASysS.anon_grantable] about THAT address, whose third
    conjunct was [bottomup_floor <= a].  At #38 the checker's anonymous
    arms gate on [Checks.Placement.linux_place_is], which says the
    address IS the one Linux gives ([Checks/Sys/Mm/Mmap.v:111] for the
    modeled arm, [:135] for the PROT_NONE arm; every MAP_FIXED arm is
    unchanged and still gates on [region_free]/[map_contains]).  Linux's
    NULL-hint answer is top-down, below
    [mmap_top h = Z.min (vm_mmap_base h) (page_round_down_Z (alloc_top h))],
    and [Run.valid_mmap_base] admits [vm_mmap_base h] down to
    [State.mmap_base_min = 0x154555557000], which is BELOW
    [bottomup_floor = 0x2aaaaaaab000].  So the old third conjunct is
    FALSE for some admissible kernels: the revision made a tree-local
    invariant false, and this is its replacement.

    THE REPLACEMENT, which is the model's own design.  The ledger is
    SPLIT at a low mark [K] and a high mark [Y]: every recorded interval
    either ends at or below [K] or starts at or above [Y].  [K] sits at
    or above [AsanPlacement.kHighMemBeg] — everything the ASan layout
    owns (image, brk, both shadows, the MAP_FIXED application space)
    ends at or below it — and [Y] descends.  [AsanPlacement]'s
    [null_hint_grant_above] turns the split into a LOWER BOUND on
    Linux's answer, and [null_hint_grant_step] lowers the mark to
    [Z.min Y a] when the grant joins the ledger.  NO CONJUNCT OF THIS
    INVARIANT ASSUMES [bottomup_floor <= a]; the floor appears only as
    the alternative disjunct Linux's own rule may supply, never as an
    assumption.

    ** WHAT PAYS FOR THE DESCENT, AND WHY IT IS THE HEAP'S EXISTING BUDGET

    The mark is MONOTONE — [heap_mark_incl] never recovers it — so the
    descent is paid against every grant ever made, not against the live
    ones.  A count-denominated budget does NOT work: the only grant
    counters [AVm.HKv] carries are [v_cb20]/[v_cb23], bounded by the
    BAND SLOT COUNTS [J20 = 89,476,429] and [J23 = 11,184,553], which
    permit 52x more descent than the address space between the ASan
    space and [State.mmap_base_min] provides.

    A BYTE-denominated budget does work, and it is already in [HKv].
    Its seventh conjunct is [v_eb v + 4096 * vnb v <= VLIMIT] with
    [VLIMIT = 2^39], and EVERY NULL-HINT GRANT CHARGES AT LEAST ITS OWN
    SIZE AGAINST IT, at grant time:

      - eager ([0x22], 2^20): [AInstDepot.veb_N] adds 2^20 to [v_eb] and
        [vnb_N] adds [2^20/32768 + 3] pages — 1,191,936 bytes charged
        for a 1,048,576-byte block, against 2,097,152 of descent;
      - lazy ([0x4022], 2^23): [AInstDepot.vnb_S] adds
        [(2^23/32768 + 3) + (2^23/4096 + 1)] pages — 9,453,568 bytes
        charged for an 8,388,608-byte block, against 16,777,216 of
        descent.  THE CHARGE HAPPENS AT GRANT TIME, NOT AT
        MATERIALISATION: [v_add_lazy] bumps [vnb] by the block's own
        2048 pages plus its shadow, which is exactly what
        [AInstDepot.RES_DEPOT]'s [(2^23/4096 + 1)] term reserves.

    So the charge is at least the block size on both arms and the
    descent is at most twice it, giving
    [descent <= 2 * VLIMIT = 1.0995e12] against [3.5942e12] of room —
    a 3.27x margin for any mix of the two.  That is what [MARKCAP] and
    the [Y + 2 * used] conjunct below say, and it needs no new state,
    no depot eviction and no bound on the number of grants.

    PROVENANCE.  Everything this file reasons with lives in
    [ABoot/AsanPlacement.v] and [ABoot/AsanCeil.v], which are already in
    this tree and already compile at #38 (verified by a local build of
    this port with no stub).  Rule 23c therefore does
    not apply to this file: it ports no text out of the model's
    [theories/Common] or [theories/Examples], it only consumes names the
    tree already has.  The one model-side name used directly is
    [Checks.Placement.linux_place_exists], and [theories/LinuxProcessSem]
    is importable and unaffected. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil AsanPlacement.
Import ListNotations.
Local Open Scope Z_scope.

(** [GRANT_MAX] is the largest NULL-hint grant the heap ever asks for and
    [MARKSTEP] is twice that, the most one grant can cost the high mark.

    IT IS 2^29, NOT 2^23, AND THE FIRST VALUE WAS WRONG.  2^23 was read
    off the DEPOT's two arms -- [AInstDepot]'s 2^20 node block and 2^23
    store block -- but the depot is not the only caller.  The SECONDARY
    allocator grants a whole section in one go: [AInstSec]'s grant takes
    the VARIABLE [msz], whose only local bound is
    [AInstSec.MSZ : 0x11000 <= msz /\ msz mod 4096 = 0] -- a LOWER bound
    and an alignment, no ceiling at all -- and at the site that
    instantiates it the ceiling is [AInstMallocS.MSZH : mszh <= 2^28 +
    12288].  2^28 + 12288 = 268,447,744, which is 32x the old
    [GRANT_MAX].  So under the old constant the premise
    [n <= AMark.GRANT_MAX] was UNPROVABLE on a reachable path, and a
    premise the top cannot discharge is exactly what the library rule
    forbids.  The fix is the constant, not a precondition on the path:
    adding [msz <= 2^23] where the harness can reach 2^28 would be a
    NARROWING of a reachable statement.

    WHY RAISING IT IS FREE, which is why this is a one-line repair and
    not a redesign.  [GRANT_MAX] buys exactly one thing: [heap_mark_room]
    turns the split into [K + 2 * MARKSTEP <= Y], and the producer and
    the preservation step each need only [K + 2 * nZ <= Y], so any
    [MARKSTEP = 2 * GRANT_MAX] works.  What it COSTS is the fourth and
    fifth conjuncts of [heap_mark_with], and both have four orders of
    magnitude of slack:

      K + 2*MARKCAP + 2*MARKSTEP <= bottomup_floor
        17,594,333,495,296            (K >= kHighMemBeg)
      +  1,099,511,627,776            (2 * MARKCAP)
      +      2,147,483,648            (2 * MARKSTEP at 2^29)
      = 18,695,992,606,720  <=  46,912,496,118,272  (bottomup_floor)

    and against the tightest admissible [Y], which is bounded below by
    [State.mmap_base_min = 0x154555557000 = 23,311,658,860,544], the same
    sum leaves 4,615,666,253,824 of room.  Going from 2^23 to 2^29 spends
    2,113,929,216 of that -- 0.046% of the margin.  The AGGREGATE descent
    is untouched: it is bounded by [2 * used <= 2 * MARKCAP], which does
    not mention [GRANT_MAX] at all.  [GRANT_MAX] bounds ONE step, never
    the sum.

    2^29 rather than exactly [2^28 + 12288] so the constant is a round
    number with 2x headroom over the measured ceiling, and so a later
    change to [MSZH] does not silently re-open this hole.

    [MARKCAP] is [AVm.VLIMIT], the ceiling on [v_eb v + 4096 * vnb v]
    that [HKv]'s seventh conjunct already carries — repeated as a literal
    because [AVm] imports this file, not the other way round.  Literals,
    not [Z.pow]: every bound below is linear with constant coefficients,
    so [lia] closes it and no [nia] appears in this file. *)
Definition GRANT_MAX : Z := 536870912.         (* 2^29; see above, was 2^23 *)
Definition MARKSTEP  : Z := 1073741824.        (* 2^30 = 2 * GRANT_MAX *)
Definition MARKCAP   : Z := 549755813888.      (* 2^39 = AVm.VLIMIT *)

(** [used] is the heap's consumed backing budget, [v_eb v + 4096 * vnb v].
    The descent conjunct is [... <= Y + 2 * used]: the mark may have
    fallen by at most twice what the heap has spent.

    THE BODY IS NAMED SEPARATELY FROM THE EXISTENTIAL, and that is the
    only reason [heap_mark_slot] below can exist: a caller that needs to
    know WHERE an interval sits relative to the mark must speak about the
    SAME [K] and [Y] the mark is witnessed by, and an [exists] that has
    already been closed cannot be re-opened onto a second fact.
    [heap_mark] is unchanged as a proposition -- [heap_mark_with] is its
    body verbatim -- so every [destruct ... as (K & Y & H1 & .. & H8)] in
    the tree still binds the same ten names. *)
Definition heap_mark_with (h : VmMaps) (used K Y : Z) : Prop :=
       kHighMemBeg <= K
    /\ 0 <= used
    /\ used <= MARKCAP
    /\ K + 2 * MARKCAP + 2 * MARKSTEP <= bottomup_floor
    /\ K + 2 * MARKCAP + 2 * MARKSTEP <= Y + 2 * used
    /\ Y mod page_size = 0
    /\ Y <= mmap_top h
    /\ ledger_split (vm_reserved h ++ vm_maps h) K Y.

Definition heap_mark (h : VmMaps) (used : Z) : Prop :=
  exists K Y : Z, heap_mark_with h used K Y.

(** [heap_mark_slot h used lo hi] is [heap_mark] PLUS the placement of one
    interval against the mark it is witnessed by.  The heap needs it for
    exactly one transition: [AVm.HKv_rereserve] puts an interval BACK into
    [vm_maps] after a destroy cut it out, and a re-added interval must
    satisfy [ledger_split] like any other.  While the interval is still
    mapped the fact is derivable ([heap_mark_slot_of_covers] below); the
    destroy is what removes the evidence, so [AVm.HKh] carries the slot
    across the hole.  It is not a new assumption: it is a fact the model
    had and the hole threw away. *)
Definition heap_mark_slot (h : VmMaps) (used lo hi : Z) : Prop :=
  exists K Y : Z, heap_mark_with h used K Y /\ (hi <= K \/ Y <= lo).

Lemma heap_mark_slot_mark : forall h used lo hi,
  heap_mark_slot h used lo hi -> heap_mark h used.
Proof. intros h used lo hi (K & Y & HW & _). exists K, Y. exact HW. Qed.

(** The two facts every consumer reads off the invariant: the mark is a
    full [MARKSTEP] above the low mark, and the low mark is under the
    floor.  Both follow from [used <= MARKCAP]. *)
Lemma heap_mark_room : forall used K Y,
  0 <= used -> used <= MARKCAP ->
  K + 2 * MARKCAP + 2 * MARKSTEP <= bottomup_floor ->
  K + 2 * MARKCAP + 2 * MARKSTEP <= Y + 2 * used ->
  K + 2 * MARKSTEP <= Y /\ K < bottomup_floor.
Proof.
  intros used K Y H1 H2 H3 H4. unfold MARKCAP, MARKSTEP in *. lia.
Qed.

(** Spending more budget only weakens the invariant. *)
Lemma heap_mark_used_le : forall h u u',
  heap_mark h u -> u <= u' -> u' <= MARKCAP -> heap_mark h u'.
Proof.
  intros h u u' (K & Y & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hle Hcap.
  exists K, Y. split; [exact H1|]. split; [clear - H2 Hle; lia|]. split; [exact Hcap|].
  split; [exact H4|]. split; [clear - H5 Hle; lia|].
  split; [exact H6|]. split; [exact H7|]. exact H8.
Qed.

(** [alloc_top] is a machine address, so Linux's answer fits a word. *)
Lemma alloc_top_lt_two_pow_64 : forall h, alloc_top h < 2 ^ 64.
Proof.
  intro h. pose proof (fg_u64_range (vm_init_sp h)) as Hsp.
  unfold alloc_top, stack_max_size. lia.
Qed.

(** ** THE PRODUCER STEP

    Given the invariant, Linux's own answer exists, is above the low mark,
    and carries back the four facts the old guard listed.

    THE WITNESS IS THE MARK'S OWN WINDOW.  [linux_place_exists] wants one
    range of the requested size that fits either Linux's top-down window
    [[page_size, mmap_top h)] or its bottom-up one.  The split ledger leaves
    [[K, Y)] empty and [K + 2 * nZ <= Y], so [[Y - nZ, Y)] is free
    ([ledger_split_window_free]); [Y] is page-aligned and at most
    [mmap_top h], so that range fits the top-down window.  Until LPS 727298f3
    the caller passed a bottom-up slot found by [AFreeSlot.free_slot_exists_B],
    which needed the heap's census to count every ledger entry above the
    floor; the launch's vDSO pair is a ledger entry no cover of the heap's
    holds, and the mark needs no census.

    [thp] is passed in and never read — [linux_place_exists] is
    [forall thp] and the bound travels through [AsanCeil.placement_ok_b],
    the disjunction over BOTH kernel builds.  [State.kb_thp] stays one of
    the five fields [Run.recorded_kernel] leaves free. *)
Theorem heap_mark_place : forall h thp used nZ,
  heap_mark h used ->
  0 < nZ -> nZ mod page_size = 0 -> nZ <= GRANT_MAX ->
  exists a : word,
       linux_place_is h thp (Z_to_bv 64 0) nZ a = true
    /\ kHighMemBeg < bv_unsigned a
    /\ bv_unsigned a mod page_size = 0
    /\ 0 < bv_unsigned a
    /\ bv_unsigned a + nZ <= alloc_top h
    /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h thp used nZ Hmark HnZ HnAl Hsmall.
  destruct Hmark as (K & Y & HK1 & Hu0 & Hucap & Hfl & Hslack & HYal & HYtop & Hsplit).
  destruct (heap_mark_room used K Y Hu0 Hucap Hfl Hslack) as [Hroom2 HKfl].
  assert (HKpage : page_size <= K)
    by (clear - HK1; unfold kHighMemBeg, page_size in *; lia).
  assert (Hroom : K + 2 * nZ <= Y)
    by (clear - Hsmall Hroom2; unfold GRANT_MAX, MARKSTEP in *; lia).
  (* Linux's rule has an answer: the window just under the mark is free and
     fits the top-down window [page_size, mmap_top h). *)
  pose proof (Placement.mmap_top_lt_two_pow_64 h) as Hmt64. unfold two_pow_64 in Hmt64.
  assert (Hgal : (Y - nZ) mod page_size = 0)
    by (rewrite Zminus_mod, HYal, HnAl; reflexivity).
  assert (Hglo : page_size <= Y - nZ) by (clear - HKpage Hroom HnZ; lia).
  assert (Hghi : Y - nZ + nZ <= mmap_top h) by (clear - HYtop; lia).
  assert (Hgfree : region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 (Y - nZ)) (Z_to_bv 64 nZ) = true).
  { apply (ledger_split_window_free _ K Y nZ);
      [ clear - HKpage; unfold page_size in *; lia | exact HnZ | exact Hroom
      | clear - HYtop Hmt64; lia | exact Hsplit ]. }
  destruct (linux_place_exists h thp (Z_to_bv 64 0) nZ HnZ HnAl
              (ex_intro _ (Y - nZ) (or_introl (conj Hgal (conj Hglo (conj Hghi Hgfree))))))
    as (a0 & Hpl).
  destruct (linux_place_admissible h thp (Z_to_bv 64 0) nZ a0 HnZ HnAl Hpl)
    as (Hal0 & Hpos0 & Hhi0 & Hfree0).
  pose proof (alloc_top_lt_two_pow_64 h) as Htop64.
  assert (Hau : bv_unsigned (Z_to_bv 64 a0) = a0)
    by (apply fg_u64_lit; clear - Hpos0 Hhi0 Htop64 HnZ; lia).
  (* the lower bound; NEITHER disjunct assumes the floor *)
  assert (Habove : bottomup_floor <= a0 \/ Y - 2 * nZ < a0).
  { pose proof (null_hint_grant_above h (Z_to_bv 64 a0) nZ K Y HnZ HnAl
                  ltac:(rewrite Hau; exact Hal0) HYal HYtop HKpage Hroom Hsplit
                  (placement_policy_holds h thp (Z_to_bv 64 a0) nZ HnZ HnAl
                     ltac:(rewrite Hau; exact Hpl))) as H.
    rewrite Hau in H. exact H. }
  (* case 1 goes through the floor, case 2 through the mark; neither assumes it *)
  assert (HKa : kHighMemBeg < a0).
  { clear - Habove Hsmall HKfl Hroom HK1.
    unfold GRANT_MAX in *. destruct Habove; lia. }
  exists (Z_to_bv 64 a0). rewrite Hau.
  split.
  { apply (linux_place_is_iff h thp (Z_to_bv 64 0) nZ (Z_to_bv 64 a0) HnZ HnAl).
    rewrite Hau. exact Hpl. }
  split; [exact HKa|]. split; [exact Hal0|]. split; [exact Hpos0|]. split; [exact Hhi0|].
  exact Hfree0.
Qed.

(** ** THE PRESERVATION STEP

    The grant joins [vm_maps] and the mark drops to [Z.min Y a], which
    the heap's own backing charge pays for: [charge] is what this grant
    adds to [v_eb v + 4096 * vnb v], and [nZ <= charge] holds on both
    arms ([AInstDepot.veb_N]/[vnb_N] for [0x22], [vnb_S] for [0x4022]).
    The mark loses at most [2 * nZ] and the budget gains [2 * charge], so
    the conjunct [... <= Y + 2 * used] survives with room to spare.

    Stated over the two ledgers rather than over [Model] so that
    whichever constructor the heap uses ([AVm.v]'s [v_add_lazy] and
    [v_add_eager] both go through [with_vmmaps]) can discharge the three
    projections by [reflexivity]. *)
Theorem heap_mark_cons : forall h h' thp used charge (a n : word) nZ,
  heap_mark h used ->
  0 < nZ -> nZ mod page_size = 0 -> nZ <= GRANT_MAX ->
  linux_place_is h thp (Z_to_bv 64 0) nZ a = true ->
  vm_reserved h' = vm_reserved h ->
  vm_maps h' = (a, n) :: vm_maps h ->
  mmap_top h' = mmap_top h ->
  nZ <= charge -> used + charge <= MARKCAP ->
  heap_mark h' (used + charge).
Proof.
  intros h h' thp used charge a n nZ Hmark HnZ HnAl Hsmall His Hres Hmaps Htop Hch Hcap.
  destruct Hmark as (K & Y & HK1 & Hu0 & Hucap & Hfl & Hslack & HYal & HYtop & Hsplit).
  destruct (heap_mark_room used K Y Hu0 Hucap Hfl Hslack) as [Hroom2 HKfl].
  pose proof (proj1 (linux_place_is_iff h thp (Z_to_bv 64 0) nZ a HnZ HnAl) His) as Hpl.
  destruct (linux_place_admissible h thp (Z_to_bv 64 0) nZ (bv_unsigned a) HnZ HnAl Hpl)
    as (Hal0 & Hpos0 & Hhi0 & Hfree0).
  assert (HKpage : page_size <= K)
    by (clear - HK1; unfold kHighMemBeg, page_size in *; lia).
  assert (Hroom : K + 2 * nZ <= Y)
    by (clear - Hsmall Hroom2; unfold GRANT_MAX, MARKSTEP in *; lia).
  pose proof (null_hint_grant_step h a n nZ K Y HnZ HnAl Hal0 HYal HYtop HKpage HKfl
                Hroom Hsplit
                (placement_policy_holds h thp a nZ HnZ HnAl Hpl)) as HS.
  cbv zeta in HS.
  destruct HS as (Hlo' & Hcase & Hle' & Hal' & Htop' & Hsplit').
  exists K, (Z.min Y (bv_unsigned a)).
  split; [exact HK1|]. split; [clear - Hu0 Hch HnZ; lia|]. split; [exact Hcap|].
  split; [exact Hfl|].
  split.
  { (* Two cases from [null_hint_grant_step].  The mark-drop case: the mark
       loses at most 2*nZ and the budget gains 2*charge >= 2*nZ.  The floor
       case: the new mark is at or above [bottomup_floor], which [Hfl] already
       puts above the whole slack term -- which is why [Hfl] is carried here
       and not cleared. *)
    clear - Hslack Hfl Hcase Hch HnZ Hsmall Hu0.
    unfold GRANT_MAX, MARKSTEP, page_size in *. destruct Hcase; lia. }
  split; [exact Hal'|].
  split; [rewrite Htop; exact Htop'|].
  rewrite Hres, Hmaps. exact Hsplit'.
Qed.

(** ** THE LOWER BOUND, SEPARATED FROM THE PRODUCER

    [heap_mark_place] returns [kHighMemBeg < a] together with Linux's answer,
    because it is the thing that MAKES the answer.  But the heap also meets that
    answer coming the other way: [ASys.mmap_anon_inv] inverts an mmap the checker
    ALREADY accepted, so it has [linux_place_is] in hand and nothing to produce
    -- and [ASysS.grant_placed]'s second conjunct, [kHighMemBeg < a], is not
    something an inversion can invent.

    It does not have to.  The bound never depended on how the answer was found: it comes from
    [null_hint_grant_above] applied to the mark's own split, and that needs only
    the placement.  So the block is lifted out of [heap_mark_place] verbatim and
    stated on its own, and a caller holding [HKv] (whose fifteenth conjunct IS
    [heap_mark]) can rebuild the full [grant_placed] from the inversion's half.

    THE ALTERNATIVE WAS MUCH WORSE and is worth recording: weakening the premise
    threaded through the forty-odd grant statements from [grant_placed nZ mo a]
    to its first conjunct alone.  That would also have worked -- [heap_mark_cons]
    only ever needed the placement -- but it is a second sweep over every
    statement already restated, and it would leave the chain carrying a premise
    weaker than the fact its producer naturally yields. *)
Theorem heap_mark_above : forall h thp used nZ (a : word),
  heap_mark h used ->
  0 < nZ -> nZ mod page_size = 0 -> nZ <= GRANT_MAX ->
  linux_place_is h thp (Z_to_bv 64 0) nZ a = true ->
  kHighMemBeg < bv_unsigned a.
Proof.
  intros h thp used nZ a Hmark HnZ HnAl Hsmall His.
  destruct Hmark as (K & Y & HK1 & Hu0 & Hucap & Hfl & Hslack & HYal & HYtop & Hsplit).
  destruct (heap_mark_room used K Y Hu0 Hucap Hfl Hslack) as [Hroom2 HKfl].
  pose proof (proj1 (linux_place_is_iff h thp (Z_to_bv 64 0) nZ a HnZ HnAl) His) as Hpl.
  destruct (linux_place_admissible h thp (Z_to_bv 64 0) nZ (bv_unsigned a) HnZ HnAl Hpl)
    as (Hal0 & Hpos0 & Hhi0 & Hfree0).
  assert (HKpage : page_size <= K)
    by (clear - HK1; unfold kHighMemBeg, page_size in *; lia).
  assert (Hroom : K + 2 * nZ <= Y)
    by (clear - Hsmall Hroom2; unfold GRANT_MAX, MARKSTEP in *; lia).
  assert (Habove : bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ < bv_unsigned a)
    by exact (null_hint_grant_above h a nZ K Y HnZ HnAl Hal0 HYal HYtop HKpage
                Hroom Hsplit (placement_policy_holds h thp a nZ HnZ HnAl Hpl)).
  clear - Habove Hsmall HKfl Hroom HK1. unfold GRANT_MAX in *. destruct Habove; lia.
Qed.

(** ** PRESERVATION UNDER A SHRINKING LEDGER

    Unmapping, forgetting and filtering only remove intervals, and
    [ledger_split] is inherited by sublists, so the mark does not move.
    The budget does not move either: a free does not give the mark back,
    which is why the accounting is against spend rather than live bytes. *)
Theorem heap_mark_incl : forall h h' used,
  heap_mark h used ->
  incl (vm_reserved h' ++ vm_maps h') (vm_reserved h ++ vm_maps h) ->
  mmap_top h' = mmap_top h ->
  heap_mark h' used.
Proof.
  intros h h' used (K & Y & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hincl Htop.
  exists K, Y. repeat split; try assumption.
  - rewrite Htop. exact H7.
  - exact (ledger_split_incl _ _ K Y H8 Hincl).
Qed.

(** ** PRESERVATION UNDER A CUT LEDGER

    [State.maps_subtract] does not drop whole intervals, it CUTS them: the
    pieces it leaves are not members of the old list, so [heap_mark_incl] does
    not reach them.  They are CONTAINED in members, and [ledger_split] is
    inherited by containment for exactly the reason it is inherited by
    membership -- both of its disjuncts, "ends at or below [K]" and "starts at
    or above [Y]", only get easier as the interval shrinks inside its parent.

    This is the shape [AVm.HKv_munmap] and [AVm.HKv_destroy_sub] need, where
    the ledger loses an entry and gains the two stubs around the hole. *)
Lemma ledger_split_within : forall l l' K Y,
  ledger_split l K Y ->
  (forall b s, In (b, s) l' ->
     exists b0 s0, In (b0, s0) l
       /\ bv_unsigned b0 <= bv_unsigned b
       /\ bv_unsigned b + bv_unsigned s <= bv_unsigned b0 + bv_unsigned s0) ->
  ledger_split l' K Y.
Proof.
  intros l l' K Y H Hwithin b s Hb.
  destruct (Hwithin b s Hb) as (b0 & s0 & H0 & L1 & L2).
  destruct (H b0 s0 H0) as [X|X]; [left; clear - X L1 L2; lia | right; clear - X L1; lia].
Qed.

Theorem heap_mark_within : forall h h' used,
  heap_mark h used ->
  (forall b s, In (b, s) (vm_reserved h' ++ vm_maps h') ->
     exists b0 s0, In (b0, s0) (vm_reserved h ++ vm_maps h)
       /\ bv_unsigned b0 <= bv_unsigned b
       /\ bv_unsigned b + bv_unsigned s <= bv_unsigned b0 + bv_unsigned s0) ->
  mmap_top h' = mmap_top h ->
  heap_mark h' used.
Proof.
  intros h h' used (K & Y & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hwithin Htop.
  exists K, Y. repeat split; try assumption.
  - rewrite Htop. exact H7.
  - exact (ledger_split_within _ _ K Y H8 Hwithin).
Qed.

(** ** THE SLOT: WHERE A MAPPED INTERVAL SITS, AND WHY IT SURVIVES A HOLE

    [AVm.HKv_rereserve] re-adds an interval the heap had destroyed, so
    [ledger_split] must hold of it: [hi <= K \/ Y <= lo].  Neither
    disjunct follows from the band fact the heap carries
    ([lo + len <= 0x7fff7000 \/ kHighMemBeg <= lo]).  In the HIGH case
    [kHighMemBeg <= K] is a LOWER bound on [K] and [K] is capped below
    [bottomup_floor], so the high band is not under [K]; and [Y <= lo]
    fails because [Y <= mmap_top h] admits [State.mmap_base_min =
    0x154555557000], which is ABOVE [kHighMemBeg = 0x10007fff8000].

    But the fact is TRUE and the model had it: while the interval was
    still mapped, [ledger_split] said it of the entries COVERING it.
    [ledger_split_covered_slot] is that derivation, and it is the whole
    content of this section: a covered interval cannot straddle the gap
    [[K, Y)], because no entry may cover a point inside it. *)
Lemma ledger_split_covered_slot : forall l K Y lo hi,
  K < Y -> lo < hi ->
  ledger_split l K Y ->
  (forall x, lo <= x < hi ->
     exists b s, In (b, s) l /\ bv_unsigned b <= x < bv_unsigned b + bv_unsigned s) ->
  hi <= K \/ Y <= lo.
Proof.
  intros l K Y lo hi HKY Hlh Hsplit Hcov.
  destruct (Hcov lo ltac:(clear - Hlh; lia)) as (b & s & Hin & Hb1 & Hb2).
  destruct (Hsplit b s Hin) as [Hlow|Hhigh]; [| right; clear - Hhigh Hb1; lia].
  (* the covering entry of [lo] ends at or below [K], so [lo < K]; if [hi]
     passed [K] then [K] itself would be a covered point of the interval,
     and no entry may cover it -- one disjunct puts the entry below [K],
     the other at or above [Y > K]. *)
  left. destruct (Z_le_gt_dec hi K) as [Hle|Hgt]; [exact Hle|]. exfalso.
  destruct (Hcov K ltac:(clear - Hlow Hb1 Hb2 Hgt; lia)) as (b' & s' & Hin' & Hb1' & Hb2').
  destruct (Hsplit b' s' Hin'); [clear - Hb2' H; lia | clear - Hb1' H HKY; lia].
Qed.

(** The producer, used at the destroy: the interval is still in the
    ledger, so its own cover witnesses the slot. *)
Theorem heap_mark_slot_of_covers : forall h used lo hi,
  heap_mark h used -> lo < hi ->
  (forall x, lo <= x < hi ->
     exists b s, In (b, s) (vm_reserved h ++ vm_maps h)
       /\ bv_unsigned b <= x < bv_unsigned b + bv_unsigned s) ->
  heap_mark_slot h used lo hi.
Proof.
  intros h used lo hi (K & Y & HW) Hlh Hcov.
  pose proof HW as (HK1 & Hu0 & Hucap & Hfl & Hslack & HYal & HYtop & Hsplit).
  destruct (heap_mark_room used K Y Hu0 Hucap Hfl Hslack) as [Hroom2 _].
  exists K, Y. split; [exact HW|].
  apply (ledger_split_covered_slot _ K Y lo hi
           ltac:(clear - Hroom2; unfold MARKSTEP in *; lia) Hlh Hsplit Hcov).
Qed.

(** The carrier: the destroy cuts the ledger, and the slot rides across
    unchanged because it names the same [K] and [Y] the mark does. *)
Theorem heap_mark_slot_within : forall h h' used lo hi,
  heap_mark_slot h used lo hi ->
  (forall b s, In (b, s) (vm_reserved h' ++ vm_maps h') ->
     exists b0 s0, In (b0, s0) (vm_reserved h ++ vm_maps h)
       /\ bv_unsigned b0 <= bv_unsigned b
       /\ bv_unsigned b + bv_unsigned s <= bv_unsigned b0 + bv_unsigned s0) ->
  mmap_top h' = mmap_top h ->
  heap_mark_slot h' used lo hi.
Proof.
  intros h h' used lo hi (K & Y & (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) & Hslot) Hwithin Htop.
  exists K, Y. split; [| exact Hslot].
  unfold heap_mark_with. repeat split; try assumption.
  - rewrite Htop. exact H7.
  - exact (ledger_split_within _ _ K Y H8 Hwithin).
Qed.

(** The consumer, used at the re-reserve: the interval goes back into
    [vm_maps] and the slot is exactly what [ledger_split_cons] wants. *)
Theorem heap_mark_slot_cons : forall h h' used lo hi (a n : word),
  heap_mark_slot h used lo hi ->
  bv_unsigned a = lo ->
  bv_unsigned a + bv_unsigned n = hi ->
  vm_reserved h' = vm_reserved h ->
  vm_maps h' = (a, n) :: vm_maps h ->
  mmap_top h' = mmap_top h ->
  heap_mark h' used.
Proof.
  intros h h' used lo hi a n (K & Y & (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) & Hslot)
         Ha Han Hres Hmaps Htop.
  exists K, Y. unfold heap_mark_with. repeat split; try assumption.
  - rewrite Htop. exact H7.
  - rewrite Hres, Hmaps.
    apply ledger_split_app_inv in H8 as [Hr Hm].
    apply ledger_split_app; [exact Hr|].
    apply ledger_split_cons; [exact Hm|].
    clear - Hslot Ha Han. destruct Hslot; [left; lia | right; lia].
Qed.
