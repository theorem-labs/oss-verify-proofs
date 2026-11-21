(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YK10.v at , lines 6-7, 9-323, added for the port to the model. *)
(** * Common.PlacementSearch — deciding "is there a free gap here?"

    UNTRUSTED.  Nothing in [EquivalenceDefinition/] or
    [LinuxProcessSem/Sys/] depends on this file; it is proof-library
    machinery, and the trusted spec must not name it.

    [Mmap.mmap_spec] USED TO say three things about a preference-free
    placement — page-aligned, inside the user address space, disjoint
    from every recorded mapping — and leave the choice to the
    nondeterminism monad.  SINCE THE PLACEMENT WORK IT SAYS WHERE: the fresh-grant
    arms choose with [Mmap.linux_place], which has at most one solution.
    So the three conditions are still NECESSARY ([linux_place_admissible])
    and no longer SUFFICIENT, and a proof that needs one concrete
    address takes it from [Checks.Placement.linux_place_b], not from the
    search here.

    WHAT THIS FILE IS FOR NOW.  Linux's rule answers whenever a range of
    the requested size is free in either of its two windows
    ([Placement.linux_place_exists]).  That is a free-gap question, which
    is exactly what this file decides.  [place_in_model_linux] searches
    the window Linux falls back to, and
    [place_in_model_linux_grants] turns its answer into "the spec has a
    grant", without claiming the searched address is the granted one —
    it is not, in general.

    Both reduce to the same question — does a free gap of [nZ] bytes
    exist in a given interval of the ledger? — and this file answers it
    decidably, with the completeness argument proved.  The trusted spec
    does not use it.

    The candidate argument, which is what makes the question decidable
    at all: if ANY fitting free gap exists in an interval, then one
    exists whose base is either the interval's own floor or the
    page-rounded end of some ledger entry — slide the gap down until it
    rests on one or the other.  So a finite list of candidates suffices,
    one per ledger interval plus one. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
Import ListNotations.
Open Scope bv_scope.

(** No free region of [nZ] bytes lies wholly above [aZ + nZ] and at or
    below [baseZ].  Quantified over [Z] with the range conditions
    keeping [g] inside [word]; the page-alignment premise matches the
    kernel, which only ever considers page-aligned placements. *)
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
    : Prop :=
  forall g : Z,
    (g mod page_size = 0)%Z ->
    (aZ + nZ <= g)%Z ->
    (g + nZ <= baseZ)%Z ->
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.

(** The candidate list: one entry per ledger interval, plus the
    interval's own floor. *)
Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
    : list Z :=
  (aZ + nZ)%Z
    :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                      + bv_unsigned (snd p))%Z)
           maps.

Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
    : bool :=
  existsb (fun g => (g mod page_size =? 0)%Z
                    && (aZ + nZ <=? g)%Z && (g + nZ <=? baseZ)%Z
                    && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))
          (fit_candidates maps aZ nZ).

Lemma page_round_up_Z_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(** The round-up is the LEAST page multiple at or above its argument. *)
Lemma page_round_up_Z_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
  assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma fold_max_ge_seed : forall l s, (s <= fold_left Z.max l s)%Z.
Proof.
  induction l as [|x l IH]; intro s; cbn; [lia|].
  pose proof (IH (Z.max s x)). lia.
Qed.

Lemma fold_max_ge_in : forall l s x,
  In x l -> (x <= fold_left Z.max l s)%Z.
Proof.
  induction l as [|y l IH]; intros s x Hin; [contradiction|].
  destruct Hin as [->|Hin]; cbn.
  - pose proof (fold_max_ge_seed l (Z.max s x)). lia.
  - apply IH; assumption.
Qed.

Lemma fold_max_le : forall l s b,
  (s <= b)%Z -> (forall x, In x l -> (x <= b)%Z) ->
  (fold_left Z.max l s <= b)%Z.
Proof.
  induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|].
  apply IH.
  - pose proof (Hl y ltac:(now left)). lia.
  - intros x Hx. apply Hl. now right.
Qed.

Lemma fold_max_in_or_seed : forall l s,
  fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
  induction l as [|y l IH]; intro s; cbn; [now left|].
  destruct (IH (Z.max s y)) as [Heq|Hin].
  - rewrite Heq. destruct (Z.max_spec s y) as [[_ ->]|[_ ->]];
      [right; now left | now left].
  - right. now right.
Qed.

(** COMPLETENESS of the candidate scan: any page-aligned fitting free
    gap yields a candidate that is free and fitting.  This is the
    sliding argument: take the largest candidate at or below the given
    gap's base; every ledger entry ending at or below the given base has
    its page-rounded end among the candidates (so cannot reach past the
    chosen one), and every entry ending above it starts at or above the
    given gap's end (else it would have overlapped the given free gap).
    So the chosen candidate's window is free, and it inherits both
    bounds. *)

(** THE FLOOR HYPOTHESIS IS [0 <= aZ + nZ], NOT [0 <= aZ], and the
    difference is load-bearing rather than cosmetic — leave it weak.

    [aZ] enters this lemma only through [aZ + nZ]: it is the floor of the
    search expressed as a grant's END, and the proof below never needs
    the floor's own sign.  Strengthening it back to [0 <= aZ] costs a
    caller that reduces to this lemma at [aZ := loZ - nZ] the side
    condition [nZ <= loZ], which at a floor of [page_size] silently
    forces [nZ = 4096] — turning a general completeness claim into one
    about single-page requests while still typechecking.  That is how
    [place_complete] below was first written, and it is the reason this
    hypothesis is stated in the form the proof actually uses. *)
Lemma higher_fit_b_complete : forall maps aZ nZ baseZ g,
  (0 <= aZ + nZ)%Z -> (0 < nZ)%Z ->
  (aZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (baseZ < two_pow_64)%Z ->
  (g mod page_size = 0)%Z ->
  (aZ + nZ <= g)%Z ->
  (g + nZ <= baseZ)%Z ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  higher_fit_b maps aZ nZ baseZ = true.
Proof.
  (* The three [<=] steps over [g'] below are spelled as explicit
     transitivity terms rather than [lia].  The context carries four
     [_ mod page_size = 0] hypotheses; [page_size] is an opaque constant
     to micromega, so its div/mod preprocessing turns each one into a
     product [page_size * q] and the certificate search goes nonlinear.
     Blind [lia] took 231 s, 100 s and 90 s on those three goals — 97% of
     this file's compile time — where each is one application of
     [Z.le_trans].  Do not put [lia] back without clearing HaAl, HnAl,
     HgAl and Hg'Al first. *)
  intros maps aZ nZ baseZ g HaPos HnPos HaAl HnAl Hbase HgAl Hglo Hghi
    Hgfree.
  assert (Hmod : two_pow_64 = bv_modulus 64) by reflexivity.
  assert (HgW : bv_unsigned (Z_to_bv 64 g) = g)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; lia).
  set (cs := List.filter (fun c => (c <=? g)%Z) (fit_candidates maps aZ nZ)).
  set (g' := fold_left Z.max cs (aZ + nZ)%Z).
  assert (Hcs : forall x, In x cs <->
            In x (fit_candidates maps aZ nZ) /\ (x <=? g)%Z = true)
    by (intro x0; unfold cs; exact (filter_In _ x0 _)).
  assert (Hlo : (aZ + nZ <= g')%Z) by (unfold g'; apply fold_max_ge_seed).
  assert (Hhi : (g' <= g)%Z).
  { unfold g'. apply fold_max_le; [lia|]. intros x Hx.
    apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
  assert (Hcand : In g' (fit_candidates maps aZ nZ)).
  { destruct (fold_max_in_or_seed cs (aZ + nZ)%Z) as [Heq|Hin].
    - assert (Heq' : g' = (aZ + nZ)%Z) by exact Heq.
      rewrite Heq'. now left.
    - apply Hcs in Hin. exact (proj1 Hin). }
  assert (Hg'W : bv_unsigned (Z_to_bv 64 g') = g')
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; lia).
  assert (Hg'Al : (g' mod page_size = 0)%Z).
  { destruct Hcand as [Heq|Hin].
    - rewrite <- Heq.
      rewrite Z.add_mod, HaAl, HnAl by (unfold page_size; lia).
      reflexivity.
    - apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
      rewrite <- Heq. apply page_round_up_Z_aligned. }
  assert (Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ)
                    = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HgW, HnW in Hno.
    rewrite Hg'W, HnW.
    apply andb_false_iff in Hno.
    set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
    destruct (Z.le_gt_cases (B + S) g) as [Hend|Hend].
    - (* entry ends at or below g: its rounded end is a candidate <= g *)
      assert (Hc : In (page_round_up_Z (B + S)) (fit_candidates maps aZ nZ)).
      { right. apply in_map_iff. exists (b, s).
        split; [reflexivity|assumption]. }
      assert (Hcle : (page_round_up_Z (B + S) <= g)%Z)
        by (apply page_round_up_Z_le; assumption).
      assert (Hcg' : (page_round_up_Z (B + S) <= g')%Z).
      { unfold g'. apply fold_max_ge_in. apply Hcs. split; [assumption|].
        now apply Z.leb_le. }
      pose proof (page_round_up_Z_ge (B + S)) as Hround.
      apply andb_false_iff. left. apply Z.ltb_ge.
      exact (Z.le_trans _ _ _ Hround Hcg').
    - (* entry ends above g: it must start at or above g + nZ *)
      destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno. lia.
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. right. apply Z.ltb_ge.
        exact (Z.le_trans _ _ _
                 (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hno). }
  unfold higher_fit_b. apply existsb_exists. exists g'.
  split; [exact Hcand|].
  assert (Hg'base : (g' + nZ <= baseZ)%Z)
    by exact (Z.le_trans _ _ _
                (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hghi).
  rewrite Hg'free.
  rewrite (proj2 (Z.eqb_eq _ _) Hg'Al).
  rewrite (proj2 (Z.leb_le _ _) Hlo).
  rewrite (proj2 (Z.leb_le _ _) Hg'base).
  reflexivity.
Qed.

(** The easy direction, stated so this file proves an [iff] rather than
    half of one: a candidate the decision procedure accepts really is a
    page-aligned free gap inside the interval. *)
Lemma higher_fit_b_sound : forall maps aZ nZ baseZ,
  higher_fit_b maps aZ nZ baseZ = true ->
  exists g, (g mod page_size = 0)%Z /\ (aZ + nZ <= g)%Z
            /\ (g + nZ <= baseZ)%Z
            /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros maps aZ nZ baseZ H.
  unfold higher_fit_b in H. apply existsb_exists in H as (g & _ & Hg).
  apply andb_true_iff in Hg as [Hg Hfree].
  apply andb_true_iff in Hg as [Hg Hhi].
  apply andb_true_iff in Hg as [Hal Hlo].
  exists g. repeat split.
  - now apply Z.eqb_eq.
  - now apply Z.leb_le.
  - now apply Z.leb_le.
  - exact Hfree.
Qed.

(** …and the two together: [higher_fit_b] decides [no_higher_fit]. *)
Lemma no_higher_fit_iff : forall maps aZ nZ baseZ,
  (0 <= aZ)%Z -> (0 < nZ)%Z ->
  (aZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (baseZ < two_pow_64)%Z ->
  (higher_fit_b maps aZ nZ baseZ = false <-> no_higher_fit maps aZ nZ baseZ).
Proof.
  intros maps aZ nZ baseZ HaPos HnPos HaAl HnAl Hbase. split.
  - intros Hf g HgAl Hglo Hghi.
    destruct (region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ)) eqn:Hfree;
      [|reflexivity].
    exfalso.
    rewrite (higher_fit_b_complete maps aZ nZ baseZ g
               ltac:(lia) HnPos HaAl HnAl Hbase HgAl Hglo Hghi Hfree)
      in Hf.
    discriminate.
  - intro H. destruct (higher_fit_b maps aZ nZ baseZ) eqn:Hf;
      [|reflexivity].
    exfalso. apply higher_fit_b_sound in Hf as (g & HgAl & Hglo & Hghi & Hfree).
    rewrite (H g HgAl Hglo Hghi) in Hfree. discriminate.
Qed.

(* =========================================================================
   THE PLACEMENT WITNESS — one concrete address, for proofs that want one

   [Mmap.mmap_spec] places a mapping with [Mmap.linux_place], which is a
   Prop and has at most one solution
   ([Checks.Placement.linux_place_unique]); a proof that wants to compute
   an address needs an executable search.  This file gives one: an
   executable search, a soundness lemma against admissibility conditions,
   and a completeness lemma saying the search finds an address whenever
   one exists.

   IT IS KERNEL-*LIKE*, NOT KERNEL-PINNED, and the difference is the whole
   reason it lives here rather than in the spec.  Linux's answer is a
   function of the ledger, the run's [mm->mmap_base] and the kernel build,
   and [Mmap.linux_place] is that function (its executable twin is
   [Checks.Placement.linux_place_b]).  The search here is a different
   function: every address it returns is admissible, which is all a
   witness has to be, but it need not be Linux's address.

   Determinism IS claimed here, and may be: [find] returns the first
   fitting candidate in the candidate list's order, so [place] is a
   function of its arguments.  That claim is about this function, not
   about any kernel.
   ========================================================================= *)

(** The candidate list for a search from a floor, rather than from a
    grant's end.  Same shape as [fit_candidates] — the floor itself, plus
    the page-rounded end of every ledger entry — and
    [higher_fit_b_as_place] below records that it IS the same list, so the
    completeness argument transfers instead of being redone. *)
Definition search_candidates (maps : list (word * word)) (loZ : Z)
    : list Z :=
  loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                        + bv_unsigned (snd p))%Z)
             maps.

(** Is [g] a placement this search may return?  These are exactly
    [Mmap.mmap_spec]'s conditions, with the user range given as an
    interval: page-aligned, at or above [loZ], ending at or below [hiZ],
    and disjoint from every recorded mapping. *)
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
    : bool :=
  (g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
  && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).

Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
    : option Z :=
  find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).

(** ---- soundness: what comes out satisfies the spec's conditions ---- *)

Lemma place_sound : forall maps loZ hiZ nZ a,
  place maps loZ hiZ nZ = Some a ->
  (a mod page_size = 0)%Z /\ (loZ <= a)%Z /\ (a + nZ <= hiZ)%Z
  /\ region_free maps (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
  intros maps loZ hiZ nZ a H.
  unfold place in H. apply find_some in H as [_ Hf].
  unfold place_fits in Hf.
  apply andb_true_iff in Hf as [Hf Hfree].
  apply andb_true_iff in Hf as [Hf Hhi].
  apply andb_true_iff in Hf as [Hal Hlo].
  repeat split.
  - now apply Z.eqb_eq.
  - now apply Z.leb_le.
  - now apply Z.leb_le.
  - exact Hfree.
Qed.

(** ---- completeness: if any address fits, the search returns one ---- *)

Lemma existsb_find : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, find f l = Some x.
Proof.
  intros A f l. induction l as [|y l IH]; cbn; [discriminate|].
  destruct (f y) eqn:Hy; [intros _; now exists y|].
  cbn. exact IH.
Qed.

(** The candidate list a search from [loZ] walks is the one
    [fit_candidates] builds for a grant ending at [loZ], and the two
    fitting tests agree on it.  Stated so [higher_fit_b_complete]'s
    sliding argument carries over rather than being proved twice. *)
Lemma higher_fit_b_as_place : forall maps loZ hiZ nZ,
  higher_fit_b maps (loZ - nZ) nZ hiZ
  = existsb (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).
Proof.
  intros maps loZ hiZ nZ.
  unfold higher_fit_b, place_fits, search_candidates, fit_candidates.
  replace (loZ - nZ + nZ)%Z with loZ by lia.
  reflexivity.
Qed.

(** THE NONEMPTINESS OBLIGATION, and it is stated where it cannot compute
    away: quantified over the ledger and over a witness address, so no
    instance of it reduces to a triviality.  It says the search FINDS
    something whenever something is there — not that some particular
    concrete call happens to succeed, which a computation could discharge
    without the search being any good.

    IT IS CONDITIONAL, and the unconditional form is not available.  "The
    admissible set is nonempty" is FALSE for an arbitrary ledger: a full
    one has no gap, which is what [place_finds_nothing_when_full] below
    exhibits.  The honest unconditional statement would be a COUNTING
    argument — the occupied extent plus [nZ] fitting inside the range
    implies a gap exists — and that is not proved here.

    Nobody currently needs it, which is why.  A computational proof
    strategy arrives with a CONCRETE ledger and can exhibit a gap, so
    this is the shape it uses; and the spec's own anti-vacuity does not
    rest on this file at all, since [Mmap.mmap_spec]'s
    [alt (errno_from mmap_errnos) (choose ...)] collapses onto the errno
    arm when no address satisfies the guard, which makes an exhausted
    address space a modeled behaviour rather than a gap.  The counting
    argument is the stronger statement, and it is still open. *)
Lemma place_complete : forall maps loZ hiZ nZ g,
  (0 <= loZ)%Z -> (0 < nZ)%Z ->
  (loZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (hiZ < two_pow_64)%Z ->
  (g mod page_size = 0)%Z -> (loZ <= g)%Z -> (g + nZ <= hiZ)%Z ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place maps loZ hiZ nZ = Some a.
Proof.
  intros maps loZ hiZ nZ g Hlo0 Hn Hloal Hnal Hhi HgAl Hglo Hghi Hfree.
  apply existsb_find. rewrite <- higher_fit_b_as_place.
  apply (higher_fit_b_complete maps (loZ - nZ) nZ hiZ g).
  - lia.
  - exact Hn.
  - rewrite Zminus_mod, Hloal, Hnal. reflexivity.
  - exact Hnal.
  - exact Hhi.
  - exact HgAl.
  - lia.
  - exact Hghi.
  - exact Hfree.
Qed.

(** ---- the two together, at the spec's own interval ---- *)

(** The search a caller actually wants: over the whole user address space
    the model describes, against the ledger the spec checks.  [page_size]
    as the floor is what gives the spec's [0 < a]; a caller that wants a
    kernel-like bottom-up base passes it instead, and everything above
    still applies. *)
Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
  place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

(** SOUNDNESS AGAINST THE SPEC'S GUARD, and the conclusion is stated at
    [bv_unsigned (Z_to_bv 64 a)] rather than at [a] ON PURPOSE.

    The guard's conditions are about a [word]: [mmap_spec] quantifies
    over [a : word] and constrains [bv_unsigned a].  This search works in
    [Z], so a conclusion phrased about [a : Z] is the guard's conditions
    TRANSPORTED, not the guard's conditions — they coincide only where
    [bv_unsigned (Z_to_bv 64 a) = a], which needs [0 <= a < 2 ^ 64] and
    does not follow from [place_sound] alone.  Saying "conjunct for
    conjunct" of the [Z] form would overstate by exactly that coercion
    step.

    [0 <= nZ] is what closes it, and every caller has it for free:
    [nZ] is [page_round_up_Z (bv_unsigned len)] at each use site.  The
    round-trip is stated as the first conjunct rather than assumed, so a
    caller gets the bridge along with the conditions.

    Below [0 <= nZ] the search is not wrong, merely unconstrained by this
    lemma — no divergence is reachable, since a negative length makes the
    ceiling test pass on candidates the [region_free] test then rejects —
    but an unreachable gap in a statement is still a gap in the
    statement.

    Still minus the budget, which is the caller's to discharge because it
    depends on the model rather than on the ledger. *)
Lemma place_in_model_admissible : forall h nZ a,
  (0 <= nZ)%Z ->
  place_in_model h nZ = Some a ->
  bv_unsigned (Z_to_bv 64 a) = a
  /\ (bv_unsigned (Z_to_bv 64 a) mod page_size = 0)%Z
  /\ (0 < bv_unsigned (Z_to_bv 64 a))%Z
  /\ (bv_unsigned (Z_to_bv 64 a) + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h)
       (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a Hn H. unfold place_in_model in H.
  destruct (place_sound _ _ _ _ _ H) as (Hal & Hlo & Hhi & Hfree).
  pose proof (alloc_top_lt h) as Htop. unfold two_pow_64 in Htop.
  assert (Hrt : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. unfold page_size in Hlo. cbn. lia. }
  rewrite Hrt. repeat split; try assumption.
  unfold page_size in Hlo. lia.
Qed.

(** …and [0 <= nZ] is a real hypothesis rather than decoration, which is
    only visible if someone shows the search without it.  Nothing in
    [place] checks the length's sign: at a negative one the ceiling test
    passes trivially and the floor itself is returned.  No caller can
    reach this — every use site passes [page_round_up_Z (bv_unsigned
    len)] — but the lemma above cannot transport its conditions to
    [word] without ruling it out, and this is what stops the hypothesis
    being deleted as an unused premise later. *)
Example place_accepts_a_negative_length :
  place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma place_in_model_complete : forall h nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (g mod page_size = 0)%Z -> (page_size <= g)%Z ->
  (g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h)
    (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place_in_model h nZ = Some a.
Proof.
  intros h nZ g Hn Hnal HgAl Hglo Hghi Hfree.
  unfold place_in_model.
  apply (place_complete _ _ _ _ g); try assumption.
  - unfold page_size. lia.
  - unfold page_size. reflexivity.
  - exact (alloc_top_lt h).
Qed.

(* ---- the bridge to Linux's rule ---- *)

(** The same search over the window Linux FALLS BACK to
    ([[TASK_UNMAPPED_BASE, alloc_top h)], mm/mmap.c,
    [generic_get_unmapped_area_topdown], Linux v6.18.46 commit
    ).  Its floor is the only difference from
    [place_in_model], and the floor is what makes the answer a witness
    Linux's rule accepts. *)
Definition place_in_model_linux (h : VmMaps) (nZ : Z) : option Z :=
  place (vm_reserved h ++ vm_maps h) task_unmapped_base (alloc_top h) nZ.

(** THE WITNESS A BUILDER NEEDS.  A free gap in Linux's fallback window
    means the rule has an answer — for every kernel build and every
    hint.  The answer is [Placement.linux_place_b]'s, NOT [g]: the
    search here only shows the admissible set is non-empty. *)
Lemma place_in_model_linux_grants : forall h thp hint nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  place_in_model_linux h nZ = Some g ->
  exists a, linux_place h thp hint nZ a.
Proof.
  intros h thp hint nZ g HnPos HnAl H. unfold place_in_model_linux in H.
  destruct (place_sound _ _ _ _ _ H) as (Hal & Hlo & Hhi & Hfree).
  apply (linux_place_exists h thp hint nZ HnPos HnAl).
  exists g. right. unfold gap_fits. repeat split; assumption.
Qed.

(** …and the search finds one whenever a free aligned range sits in
    that window, so the bridge is not vacuous. *)
Lemma place_in_model_linux_complete : forall h nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (g mod page_size = 0)%Z -> (task_unmapped_base <= g)%Z ->
  (g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h)
    (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place_in_model_linux h nZ = Some a.
Proof.
  intros h nZ g Hn Hnal HgAl Hglo Hghi Hfree.
  unfold place_in_model_linux.
  apply (place_complete _ _ _ _ g); try assumption.
  - unfold task_unmapped_base. lia.
  - unfold task_unmapped_base, page_size. reflexivity.
  - exact (alloc_top_lt h).
Qed.

(* ---- that the completeness lemma is not vacuous ---- *)

(** [place_complete] concludes [exists a, place … = Some a], which cannot
    hold for a reason other than the search returning something — the
    only way it could be hollow is if its HYPOTHESES were unsatisfiable,
    which no reader can see by inspection.  These three instances settle
    that, and they are computations rather than assumptions: the first
    two exhibit ledgers meeting every premise, and the third exhibits one
    that does not, so the function is visibly partial rather than
    trivially total. *)

Definition witness_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 8192)].

(** The top a hand-built ledger stands under ([State.mkVmMaps] seeds the
    stack pointer at the bottom of the SP window), so the instances
    below are stated at the same bound every other concrete case in the
    tree uses. *)
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).

(** The search SKIPS an occupied candidate.  [page_size] is a candidate
    and is inside the entry, so the answer is the entry's page-rounded
    end — not the first thing in the list. *)
Example place_skips_the_occupied_floor :
  place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof. vm_compute. reflexivity. Qed.

(** …and the premises of [place_complete] are met at that instance, by a
    witness the search did not have to be told about: the address it
    returns is itself one. *)
Example place_complete_premises_are_satisfiable :
  (0 <= page_size)%Z /\ (0 < 4096)%Z
  /\ (page_size mod page_size = 0)%Z /\ (4096 mod page_size = 0)%Z
  /\ (demo_top < two_pow_64)%Z
  /\ (12288 mod page_size = 0)%Z /\ (page_size <= 12288)%Z
  /\ (12288 + 4096 <= demo_top)%Z
  /\ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true.
Proof.
  unfold page_size, demo_top, two_pow_64. rewrite alloc_top_mkVmMaps.
  repeat split; try (vm_compute; reflexivity); try lia.
Qed.

(** THE PARTIALITY: a ledger with nothing left returns [None].  A search
    that always succeeded would make [place_complete] true and useless,
    which is what this rules out.

    It says nothing about the SPEC's errno arm.  [Mmap.mmap_spec]'s
    [alt (errno_from mmap_errnos) (choose ...)] makes -ENOMEM available
    unconditionally, whatever this file does — see [place_complete]'s
    note above.  What is partial here is the WITNESS, not the spec. *)
Definition full_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].

Example place_finds_nothing_when_full :
  place full_ledger page_size demo_top 4096 = None.
Proof. vm_compute. reflexivity. Qed.
