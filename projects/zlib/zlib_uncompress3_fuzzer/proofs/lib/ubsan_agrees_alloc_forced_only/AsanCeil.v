(** * Common.AsanCeil — the reflective ASan plan checker's CONSTANT allocation
      ceiling and floor, bridged to the run-dependent spec.

    The reflective ASan automation (AsanPlanCore / AsanPlan / AsanPlanSound /
    the AsanNodes* files) assumes that every anonymous grant ends below the
    CONSTANT [alloc_ceiling = 0x7fff7f800000] and that first-fit placement
    starts at [bottomup_floor = 0x2aaaaaaab000].  The spec instead bounds
    grants by [State.alloc_top h = vm_init_sp h - stack_max_size] (the RUN's
    stack pointer) and has no floor (placement is admissibility, not a
    search).  The checker keeps its numeric constants
    ([AsanPlanCore.CEIL] / [FLOOR]); soundness needs only that the constant
    ceiling lies at or below the spec's: for every admissible run
    [sp >= sp_window_lo = 0x7fff80000000] ([Run.valid_sp]), hence
    [alloc_top h = sp - 8 MiB >= 0x7fff7f800000 = alloc_ceiling], exactly, and the
    stack pointer field of the ledger never changes after [init_model].

    [init_sp_ok h] is the invariant the node soundness proofs carry (it is a
    conjunct of [BackingAlgebra.model_ivs_wf]); [alloc_ceiling_le_alloc_top]
    turns a [<= alloc_ceiling] side condition into the spec's [<= alloc_top h].
    [hint_placement_ok_b] is the first-fit placement gate that the checker's
    boolean grant tests use.  SINCE THE PLACEMENT WORK THE SPEC HAS SUCH A GATE:
    [Sys/Mm/Mmap.linux_place] names the ONE address Linux gives, so the
    gate is a THEOREM ([placement_policy_holds]) rather than a named
    hypothesis the node layer carries. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PlacementSearch.
Import ListNotations.
Open Scope Z_scope.

(** the checker's constant ceiling *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

(** the bottom-up placement floor [page_round_up_Z (task_size_min / 3)] for
    an Sv48 task size (2^47 / 3 rounded up = 0x2aaaaaaab000).  The spec has no
    such floor.  Equals the
    checker's [AsanPlanCore.FLOOR]; the ASan layout lemma
    [AsanPlacement.kHighMemBeg_below_mmap_base_min] needs [mmap_base_min < bottomup_floor]. *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

(** ** The placement gate, stated over [Sys/Mm/Mmap.linux_place]

    WHAT THE GATE SAYS NOW.  [placement_ok h aZ nZ] is "aZ is where
    Linux puts a NULL-hint anonymous request of nZ bytes into the
    ledger h, on one of the two kernel builds" — the spec's own
    [Mmap.linux_place] at hint 0, with the build existentially
    quantified because the ASan plan layer does not carry the run's
    [State.KernelBuild].  [placement_ok_b] decides it with
    [Checks.Placement.linux_place_b], and [placement_ok_window] reads
    off Linux's two search windows (mm/mmap.c,
    [generic_get_unmapped_area_topdown], Linux v6.18.46 commit
    ): the grant either ends inside
    [[page_size, mmap_top h)] or starts at or above
    [task_unmapped_base].  The ASan lower bound
    ([AsanPlacement.null_hint_grant_above]) needs more than that
    summary: it uses the MAXIMALITY of the top-down branch, which only
    the full predicate carries, which is why the gate keeps the
    predicate.

    WHAT IT SAID BEFORE, AND WHY THAT WAS NOT A THEOREM.  The old gate
    was "at or above [bottomup_floor], or no free gap is higher below
    [vm_mmap_base h]" — the postcondition of a FIRST-FIT search the
    spec did not have — and the old [placement_policy] derived it from
    the four conditions of the old [choose] guard.  Both halves of
    that hypothesis are false, before and after this change:

    (i) its address was quantified over EVERY free page-aligned range
        below [alloc_top h], and Linux picks one of them.  With an
        empty ledger and [nZ = page_size], [aZ = page_size] passes the
        four old guard conditions and fails the old gate: it is not at
        or above the floor, and gaps above it are free.  So the
        premise has to name Linux's address, which is what
        [linux_place] does.

    (ii) even at Linux's address the old conclusion
        [aZ + nZ <= alloc_ceiling] is false for some admissible runs.
        The top-down window's ceiling is
        [mmap_top h = Z.min (vm_mmap_base h) (page_round_down_Z (alloc_top h))],
        and [Run.valid_mmap_base] allows [vm_mmap_base h] up to
        [State.mmap_base_max = 0x7ffff8000000], which is ABOVE the
        constant [alloc_ceiling = 0x7fff7f800000]; [alloc_top h] is as
        high as [sp_window_hi - stack_max_size = 0x7fffff800000].  A
        grant in [[alloc_ceiling, alloc_top h)] is Linux's and breaks
        the bound.  (This is residual R-a of the placement plan.)  The
        true bound at Linux's address is [aZ + nZ <= alloc_top h],
        which [Placement.linux_place_admissible] gives, so the grant
        predicates state that one and the gate states none. *)
Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
  exists thp : bool, linux_place h thp (Z_to_bv 64 0) nZ aZ.

Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
  (match linux_place_b h true (Z_to_bv 64 0) nZ with
   | Some x => (x =? aZ)%Z | None => false end)
  || (match linux_place_b h false (Z_to_bv 64 0) nZ with
      | Some x => (x =? aZ)%Z | None => false end).

Lemma placement_ok_b_iff : forall h aZ nZ,
  0 < nZ -> nZ mod page_size = 0 ->
  (placement_ok_b h aZ nZ = true <-> placement_ok h aZ nZ).
Proof.
  intros h aZ nZ HnPos HnAl. unfold placement_ok_b, placement_ok.
  assert (K : forall thp,
    (match linux_place_b h thp (Z_to_bv 64 0) nZ with
     | Some x => (x =? aZ)%Z | None => false end) = true
    <-> linux_place h thp (Z_to_bv 64 0) nZ aZ).
  { intro thp.
    destruct (linux_place_b_spec h thp (Z_to_bv 64 0) nZ HnPos HnAl)
      as [Hsome Hnone].
    destruct (linux_place_b h thp (Z_to_bv 64 0) nZ) as [x|] eqn:Hb.
    - split.
      + intro E. apply Z.eqb_eq in E. subst x. now apply Hsome.
      + intro Hp. apply Z.eqb_eq.
        exact (linux_place_unique _ _ _ _ _ _ (proj1 (Hsome x) eq_refl) Hp).
    - split; [discriminate|]. intro Hp. exfalso.
      exact (proj1 Hnone eq_refl aZ Hp). }
  rewrite orb_true_iff, (K true), (K false).
  split; [intros [H|H]; [now exists true | now exists false]
         | intros ([|] & H); [now left | now right]].
Qed.

(** Linux's address is unique, so the gate is a FUNCTION of the state:
    two addresses that both pass it under the same kernel build are
    equal.  (The disjunction over [thp] is there because the ASan plan
    layer does not carry the run's [KernelBuild]; both builds exist and
    the bound below holds for either.) *)
Lemma placement_ok_thp : forall h thp aZ nZ,
  linux_place h thp (Z_to_bv 64 0) nZ aZ -> placement_ok h aZ nZ.
Proof. intros h thp aZ nZ H. now exists thp. Qed.

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
  w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. now rewrite H. Qed.

(** Linux's plain search leaves the address in one of its two windows.
    Both halves are the [gap_fits] bound of the branch that produced
    it.  The ASan layer uses the stronger MAXIMALITY of the top-down
    branch (see [AsanPlacement.null_hint_grant_above]); this is the
    cheap consequence. *)
Lemma topdown_search_window : forall h nZ a,
  topdown_search h nZ a -> (a + nZ <= mmap_top h)%Z \/ (task_unmapped_base <= a)%Z.
Proof.
  intros h nZ a H. unfold topdown_search in H. cbv zeta in H.
  destruct H as [[(_ & _ & Hhi & _) _] | [_ [(_ & Hlo & _ & _) _]]];
    [now left | now right].
Qed.

Lemma placement_ok_window : forall h aZ nZ,
  placement_ok h aZ nZ ->
  (aZ + nZ <= mmap_top h)%Z \/ (task_unmapped_base <= aZ)%Z.
Proof.
  intros h aZ nZ (thp & Hpl).
  unfold linux_place in Hpl. cbv zeta in Hpl.
  assert (Hg : hint_address (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
  rewrite Hg, Z.eqb_refl in Hpl. cbv iota in Hpl.
  pose proof pmd_size_pos as Hpmd.
  destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool.
  - destruct Hpl as [(ret & Hret & ->)|[_ Hts]].
    + pose proof (thp_align_bounds ret) as [Hb1 Hb2].
      destruct (topdown_search_window _ _ _ Hret) as [Hhi|Hlo];
        [left|right]; lia.
    + exact (topdown_search_window _ _ _ Hts).
  - exact (topdown_search_window _ _ _ Hpl).
Qed.

(** THE GATE, now a theorem.  A NULL-hint grant of the spec is at the
    address [Mmap.linux_place] gives, and that address passes the
    checker's placement gate.  The node-soundness layer applies
    [placement_policy_holds] where it used to carry a hypothesis. *)
Definition placement_policy : Prop :=
  forall (h : VmMaps) (thp : bool) (a : word) (nZ : Z),
    0 < nZ -> nZ mod page_size = 0 ->
    linux_place h thp (Z_to_bv 64 0) nZ (bv_unsigned a) ->
    placement_ok_b h (bv_unsigned a) nZ = true.

Theorem placement_policy_holds : placement_policy.
Proof.
  intros h thp a nZ HnPos HnAl Hpl.
  apply (placement_ok_b_iff h (bv_unsigned a) nZ HnPos HnAl).
  now exists thp.
Qed.

(** the ledger's stack pointer is an admissible one *)
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.

(** every ledger update of the spec and of the checker copies [vm_init_sp] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.

(** [State.page_round_up_Z_ge] has a [0 <= z] hypothesis; the bound holds for every [z]. *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

(** ** Two [check_mmap] gates, for the node lemmas that unfold the checker *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** [MAP_ANONYMOUS] (bit 5) survives [mmap_flags_core] (which only clears MAP_NORESERVE, bit 14) *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(** rounding facts the node files use (see also Common.AllocSim/PlacementSearch) *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.

(* ------------------------------------------------------------------------- *)
(** ** The AT_RANDOM bytes are a draw                                         *)
(* ------------------------------------------------------------------------- *)
(** The 16 bytes the auxv AT_RANDOM entry points at are the [ed_random] half of
    the fourth [Run.ExecEntry] field [en_draw], quantified per binary.  The initial knowledge
    [AsanPlanCore.init_kn_zero] asserts that they are ZERO.  The soundness lemma for that entry
    ([AsanInit.atrandom_zero_ok]) therefore holds only under this NAMED hypothesis, which is
    FALSE on every real run: a certificate built on the base [init_kn_zero] proves a
    conditional statement that establishes nothing about the real binary.  Its only purpose is
    to keep certificates built on that base checkable.  The DEFAULT base [init_kn]
    is faithful — the block is byte string [AsanPlanCore.K_RND], bound to the draw — and needs
    no hypothesis. *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof. vm_compute. reflexivity. Qed.

(** one byte of a byte string, as the slice [RefLayout.at_random_off] reads it *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
