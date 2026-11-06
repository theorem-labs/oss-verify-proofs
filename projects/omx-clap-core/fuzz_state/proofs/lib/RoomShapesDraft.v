(** * OSSVerify.Core.RoomShapes: the agreement shapes read
      alloc-forced-only, judged on Linux's placement

    DRAFT (branch draft/canon-interface, for provers designing against the
    interface): names in this file may still change in review; the
    statements of [canon_complete] and [agrees_in_canon_of_parts] (and its
    abort-modelled and rv64gc variants) will not.

    lps places an anonymous mapping that does not name its address, and the
    new range of an [mremap(MREMAP_MAYMOVE)], at ANY free page-aligned range
    below the run's [alloc_top] (lps Sys/Mm/Mmap.v, the PLACEMENT note and the
    two fresh-grant arms of [mmap_spec]; Sys/Mm/Mremap.v, the MAYMOVE
    destination).  An execution may therefore spread its mappings so that
    every gap is shorter than a later request although far more space than it
    asks for is unused, put a mapping just above the program break so that a
    brk grow is blocked, or put one where the program later asks for a fixed
    address.  Under [Env.alloc_forced_only] a refusal that follows is FORCED
    (no other answer exists), so the execution takes it, and the memory
    budget does not explain it: the budget mark reads the request and the
    state, never a free range (lps Run.v, the KNOWN GAP note and
    [refusal_decided]).  Each build's run has its own entry and its own image:
    one build can be left with no range where the other always has one, and
    [agrees_in] is then false for a reason that is neither the program's nor
    the sanitizer's.  And because [agrees_in] reads every execution, such a
    placement can also remove an input from its premise, or give the other
    build a trace that matches a real difference.  Linux places a
    mapping where its placement policy picks and does neither.

    [agrees_in_room] is [agrees_in] (OSSVerify.Core.Shapes) judged, for
    EVERY claimed placement policy [p] separately and the same [p] for both
    builds (one kernel, as on one machine), on the CANONICAL executions of
    [p] ([canon_run]):
    - the budget premise reads the plain build's canonical executions of [p];
    - the two builds' canonical trace sets of [p] are equal;
    - no canonical execution of [p], and no execution at all, whatever its
      placements, up to its first UNPLACED or budget-refused configuration
      ([star_guarded]), reaches an error (abort-modelled: or is killed).
    A policy is Linux v6.18's placement for a static, non-PIE image, in the
    top-down layout or the legacy bottom-up one: an [mmap] gets its hint
    (rounded down to a page, raised to mmap_min_addr) when the hint is free
    and clear of the stack guard; else, top-down, the highest free range
    below the mmap base when it is clear of the stack guard, else the highest
    below the stack's low end less the guard gap, else the lowest free range
    from TASK_UNMAPPED_BASE up; legacy, the lowest free range from the legacy
    base up, clear of the stack guard.  On a kernel with transparent huge
    pages a length that is a multiple of 2 MiB is padded and aligned.
    Nothing overlaps the vDSO's two mappings, which lps does not record,
    while they are in place (the program may remove them).  An [mremap]
    moves only when it cannot grow in place.  The policies claimed are both
    huge-page settings, every vDSO of 1-8 data pages and 1-16 text pages at
    any address, every top-down mmap base and every legacy base within 32 TiB
    of TASK_UNMAPPED_BASE (the random offset root may allow), and every
    mmap_min_addr and stack guard gap; at each request the stack's low end
    may be anywhere in lps's 8 MiB stack.  The refusals a canonical execution
    meets are that policy's, including those the program's own mappings,
    hints and the image's layout cause.  An UNPLACED configuration is one
    where a request that places by choice (that mmap or mremap, or a brk
    grow) is pending, the budget does not refuse it, the model answers it,
    every answer is a refusal, and the address space below [alloc_top] has at
    least as many unused bytes as the request needs (so it is not
    exhaustion).

    Where a canonical execution has no canonical step (lps allows no answer
    of the policy: Linux would refuse where lps does not, or a canonical
    [mremap] move needs lps's lazy-ledger invariant, Mremap.v, which lps does
    not prove), [canon_run] goes on with any step lps allows from a
    configuration that is not unplaced, and from then on takes no step from
    an unplaced configuration: the comparison is not cut there, and the
    model's own placements cannot force a refusal into it afterwards.  Not
    claimed as a policy of its own: QEMU user mode's placement (next fit from
    a cursor, linux-user/mmap.c); a PIE or dynamically linked image, whose
    loader maps below the mmap base before the vDSO; a change of
    vm.mmap_min_addr while the program runs.  That the huge-page aligned
    address fits (it lies inside the padded fit) is argued, not proved here.
    Linux behaviours that are no lps execution (a placement above
    [alloc_top], a refusal for the stack guard or below a raised
    mmap_min_addr) are outside [agrees_in] too.

    A proof of a statement of these shapes needs, beside what a proof of
    [agrees_in] shows on every input, that every trace of each build's run is
    a canonical trace of every policy ([canon_complete];
    [agrees_in_canon_of_parts]).

    Like the shapes of Shapes.v, these are built from lps definitions only.
    This file is separate from Shapes.v because a statement's fingerprint
    hashes the code of Shapes.v (docs/versioning.md): a definition added there
    would change the fingerprint of every statement in the collection.  The
    fingerprint of a statement of one of these shapes also hashes this file.
    [Print Assumptions] of a lemma below lists only axioms in
    toolchain/allowed-axioms.txt. *)

From Stdlib Require Import ZArith List Lia Arith Classical_Prop.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
Import ListNotations.

(** ** Requests whose address the model picks *)

(** The bytes a ledger entry [(start, length)] touches, counted from the page
    its first byte is in to the end of the page its last byte is in.  An entry
    recorded by a brk grow inside one page need not start on a page
    boundary. *)
Definition entry_bytes (e : word * word) : Z :=
  (page_round_up_Z (bv_unsigned (fst e) + bv_unsigned (snd e))
   - page_round_down_Z (bv_unsigned (fst e)))%Z.

(** The bytes the ledger's entries touch, summed: the image's page-rounded
    segments ([vm_reserved]) and every live mapping and brk grow
    ([vm_maps]).  A page two entries share is counted twice, so this is at
    least the size of the pages the ledger covers. *)
Definition ledger_bytes (h : VmMaps) : Z :=
  fold_right (fun e acc => (entry_bytes e + acc)%Z) 0%Z (vm_reserved h ++ vm_maps h).

(** The length a request asks the model to find room for, when the model,
    not the program, decides where it goes: an anonymous [mmap] (222) with
    neither MAP_FIXED nor MAP_FIXED_NOREPLACE, its length; an
    [mremap(old, old_size, new_size, MREMAP_MAYMOVE)] (216), its new size; a
    [brk] (214) above the current break, the growth.  Any other request:
    [None]. *)
Definition placement_len (i : SyscallInput) (m : Model) : option Z :=
  let no := bv_unsigned (in_sysno i) in
  if Z.eqb no 222 then
    if andb (mmap_anon_b (in_arg i 3))
            (Z.eqb (Z.land (bv_unsigned (in_arg i 3)) (Z.lor MAP_FIXED MAP_FIXED_NOREPLACE)) 0)
    then Some (bv_unsigned (in_arg i 1)) else None
  else if Z.eqb no 216 then
    if Z.eqb (bv_unsigned (in_arg i 3)) MREMAP_MAYMOVE
    then Some (bv_unsigned (in_arg i 2)) else None
  else if Z.eqb no 214 then
    let b := bv_unsigned (vm_brk (m_vmmaps m)) in
    if Z.ltb b (bv_unsigned (in_arg i 0)) then Some (bv_unsigned (in_arg i 0) - b)%Z else None
  else None.

(** A configuration with such a request pending. *)
Definition placement_at (segs : list Segment) (c : config) (x8 : word) (len : Z) : Prop :=
  m_halted (cfg_model c) = None
  /\ ms_svc_pending (cfg_ms c) = Some x8
  /\ placement_len (sys_input segs (cfg_ms c) x8) (cfg_model c) = Some len.

(** ** Unplaced: refused for want of a range that the unused space would hold *)

(** The request [i] at model [m] is refused for want of placement alone: it
    places by choice; its length, the ledger and the page below the lowest
    address fit below [alloc_top] (so enough bytes are unused); the budget
    does not refuse it; the model answers it; and every answer is a
    refusal. *)
Definition unplaced_request (i : SyscallInput) (m : Model) : Prop :=
  exists len,
    placement_len i m = Some len
    /\ (page_round_up_Z len + ledger_bytes (m_vmmaps m) + page_size <= alloc_top (m_vmmaps m))%Z
    /\ alloc_budget_refused_b i m = false
    /\ (exists eff m' evs, syscall_spec i m (Ok eff m' evs))
    /\ (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true).

(** A configuration about to make such a request. *)
Definition unplaced_at (segs : list Segment) (c : config) : Prop :=
  m_halted (cfg_model c) = None
  /\ exists x8, ms_svc_pending (cfg_ms c) = Some x8
                /\ unplaced_request (sys_input segs (cfg_ms c) x8) (cfg_model c).


(** ** Canonical: every placement is the one a Linux placement policy picks

    The model is Linux v6.18's placement for a static, non-PIE riscv64 image
    (the images OSS Verify builds).  A policy is fixed for the whole
    execution:
    - [p_thp]: whether the kernel is built with transparent huge pages, so an
      anonymous mapping whose length is a multiple of 2 MiB is padded and
      aligned ([__get_unmapped_area], [thp_get_unmapped_area_vmflags]);
    - [p_vvar], [p_text], [p_vdso]: the sizes of the vDSO data pages and
      text, and where they start, which lps's ledger does not record ([execve]
      maps them with the first search of the run: directly below a top-down
      base or at a legacy one, or elsewhere when that range is taken);
    - [p_legacy], [p_base]: the layout and its mmap base.  Top-down
      ([p_legacy = false]): the base is [STACK_TOP] less a gap and a random
      offset ([mmap_base], mm/util.c).  Legacy ([p_legacy = true]: an
      unlimited stack rlimit, ADDR_COMPAT_LAYOUT or vm.legacy_va_layout): the
      base is TASK_UNMAPPED_BASE plus a random offset.  The policy carries its
      own base rather than reading lps's [vm_mmap_base], whose band assumes at
      most 24 random bits, where root may set up to 33 on an Sv48 kernel;
    - [p_min]: vm.mmap_min_addr, any page multiple;
    - [p_guard]: stack_guard_gap, any size.
    Two things change during the execution: the program may unmap or map
    over either vDSO mapping, so a canonical execution may drop one after any
    step and never gets one back; and the stack mapping's low end, which lps
    does not track and which, less the guard gap, bounds Linux's searches
    from above, may be anywhere in lps's 8 MiB stack at each request.  The
    statements claim the canonical executions of every policy [policy_ok]
    admits. *)

Record policy := mkPolicy {
  p_thp : bool; p_vvar : Z; p_text : Z; p_vdso : Z; p_legacy : bool; p_base : Z; p_min : Z;
  p_guard : Z }.

(** Which of the vDSO's two mappings are still in place. *)
Record strip := mkStrip { s_vvar : bool; s_text : bool }.

Definition full_strip : strip := mkStrip true true.

(** [s'] has no mapping that [s] has not. *)
Definition strip_le (s' s : strip) : Prop :=
  (s_vvar s' = true -> s_vvar s = true) /\ (s_text s' = true -> s_text s = true).

Definition page_multiple_in (lo hi z : Z) : Prop :=
  (lo <= z <= hi)%Z /\ (z mod page_size = 0)%Z.

(** Where Linux's bottom-up search starts: riscv64's TASK_UNMAPPED_BASE,
    PAGE_ALIGN(2^MMAP_MIN_VA_BITS / 3) with MMAP_MIN_VA_BITS = 39 for every
    64-bit task whatever the paging mode (riscv processor.h, pgtable.h). *)
Definition task_unmapped_base : Z := page_round_up_Z (2 ^ 39 / 3).

(** The largest random offset of an mmap base claimed: 32 TiB, 2^33 pages:
    riscv64's mmap_rnd_bits_max on a 48-bit address space,
    MMAP_VA_BITS - PAGE_SHIFT - 3 (arch/riscv/mm/init.c), which root may set
    through vm.mmap_rnd_bits. *)
Definition legacy_rnd_max : Z := (2 ^ 45)%Z.

(** The policies claimed: vDSO data 1 .. 8 pages and text 1 .. 16 pages
    (Linux v6.18 riscv64 maps 4 data pages and a few pages of text) at any
    page-aligned address; both huge-page settings; every top-down base in the
    address space and every legacy base; every vm.mmap_min_addr from 4 KiB
    (lps's own floor) up; every stack guard gap (stack_guard_gap, a boot
    parameter with no maximum). *)
Definition policy_ok (p : policy) : Prop :=
  page_multiple_in page_size (8 * page_size) (p_vvar p)
  /\ page_multiple_in page_size (16 * page_size) (p_text p)
  /\ page_multiple_in 0 TASK_SIZE (p_vdso p)
  /\ (if p_legacy p
      then page_multiple_in task_unmapped_base (task_unmapped_base + legacy_rnd_max) (p_base p)
      else page_multiple_in page_size TASK_SIZE (p_base p))
  /\ page_multiple_in page_size TASK_SIZE (p_min p)
  /\ (0 <= p_guard p)%Z.

(** Where the stack mapping's low end may be at a request: in an lps
    execution, within lps's 8 MiB stack, from [alloc_top] (page-rounded
    down) to [alloc_top + 8 MiB]. *)
Definition stack_low_ok (h : VmMaps) (st : Z) : Prop :=
  (page_round_down_Z (alloc_top h) <= st <= alloc_top h + stack_max_size)%Z.

(** Where Linux's top-down search starts: the policy's mmap base, never above
    [alloc_top]. *)
Definition mmap_top (h : VmMaps) (p : policy) : Z := Z.min (alloc_top h) (p_base p).

(** The end of the vDSO. *)
Definition vdso_end (p : policy) : Z := (p_vdso p + p_vvar p + p_text p)%Z.

(** [n] bytes at [a] lie wholly below [lo] or wholly at or above [hi]. *)
Definition away (n : Z) (a : word) (lo hi : Z) : Prop :=
  (bv_unsigned a + n <= lo)%Z \/ (hi <= bv_unsigned a)%Z.

(** [n] bytes at [a] overlap neither vDSO mapping still in place: the data
    pages at [end - text - vvar, end - text), the text at [end - text, end). *)
Definition off_vdso (h : VmMaps) (p : policy) (s : strip) (n : Z) (a : word) : Prop :=
  let b := vdso_end p in
  (s_vvar s = true -> away n a (b - p_text p - p_vvar p) (b - p_text p))
  /\ (s_text s = true -> away n a (b - p_text p) b).

(** [n] bytes at [a] keep clear of the stack mapping whose low end is [st]:
    they end at or below [st] less the guard gap, or some mapping (in the
    ledger, or a vDSO mapping still in place) starts between their end and
    [st], so the next mapping above them is not the stack ([vm_start_gap]
    applies the guard only to a stack). *)
Definition clear_of_stack (h : VmMaps) (p : policy) (s : strip) (st n : Z) (a : word) : Prop :=
  let e := (bv_unsigned a + n)%Z in
  (e <= Z.max 0 (st - p_guard p))%Z
  \/ (exists m, In m (vm_reserved h ++ vm_maps h) /\ (e <= bv_unsigned (fst m) < st)%Z)
  \/ (s_vvar s = true /\ (e <= p_vdso p < st)%Z)
  \/ (s_text s = true /\ (e <= p_vdso p + p_vvar p < st)%Z).

(** [a] is a page-aligned address at or above [lo] and above 0 at which [n]
    bytes end at or below [top], overlap nothing in the ledger (the guard of
    the fresh-grant arms of lps's [mmap_spec], with [top] for [alloc_top]),
    overlap no vDSO mapping in place, and, when [g], keep clear of the stack. *)
Definition fits (h : VmMaps) (p : policy) (s : strip) (st : Z) (g : bool) (n lo top : Z) (a : word) : Prop :=
  (bv_unsigned a mod page_size = 0)%Z
  /\ (lo <= bv_unsigned a)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= top)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true
  /\ off_vdso h p s n a
  /\ (g = true -> clear_of_stack h p s st n a).

Definition highest_fit h p s st g n lo top (a : word) : Prop :=
  fits h p s st g n lo top a /\ forall a', fits h p s st g n lo top a' -> (bv_unsigned a' <= bv_unsigned a)%Z.

Definition lowest_fit h p s st g n lo top (a : word) : Prop :=
  fits h p s st g n lo top a /\ forall a', fits h p s st g n lo top a' -> (bv_unsigned a <= bv_unsigned a')%Z.

(** Linux's search with no usable hint, with vm.mmap_min_addr [pm] and the
    stack's low end at [st].  Top-down ([unmapped_area_topdown]): the
    highest free range below the mmap base, when it keeps clear of the stack;
    else, the guard having lowered the search's top to [st] less the gap for
    the rest of the search, the highest free range below that; else the lowest
    fit from TASK_UNMAPPED_BASE up (the bottom-up fallback).  Legacy: the
    lowest fit from the legacy base up ([generic_get_unmapped_area]). *)
Definition search_addr (h : VmMaps) (p : policy) (s : strip) (pm st n : Z) (a : word) : Prop :=
  if p_legacy p then lowest_fit h p s st true n (Z.max pm (p_base p)) (alloc_top h) a
  else
    let low := Z.min (mmap_top h p) (Z.max 0 (st - p_guard p)) in
    let first_unclear := forall a1, highest_fit h p s st false n pm (mmap_top h p) a1 ->
                                    ~ clear_of_stack h p s st n a1 in
    (highest_fit h p s st false n pm (mmap_top h p) a /\ clear_of_stack h p s st n a)
    \/ (first_unclear /\ highest_fit h p s st false n pm low a)
    \/ (first_unclear /\ (forall a', ~ fits h p s st false n pm low a')
        /\ lowest_fit h p s st true n (Z.max pm task_unmapped_base) (alloc_top h) a).

(** 2 MiB, a PMD on riscv64. *)
Definition pmd_size : Z := 0x200000%Z.

(** Where [thp_get_unmapped_area_vmflags] puts a mapping found at [ret] by
    the padded search: up to the next 2 MiB boundary; when [ret] is on one,
    2 MiB higher in the top-down layout and at [ret] in the bottom-up one. *)
Definition thp_align (p : policy) (ret : Z) : Z :=
  if p_legacy p then (ret + ((pmd_size - ret mod pmd_size) mod pmd_size))%Z
  else (ret + (pmd_size - ret mod pmd_size))%Z.

(** The address of a request with no usable hint, for the stack's low end
    [st].  Under [p_thp], a length that is a multiple of 2 MiB is searched for
    padded by 2 MiB and aligned ([thp_align]); when the padded length fits
    nowhere, the plain search.  Otherwise the plain search. *)
Definition fresh_addr_at (h : VmMaps) (p : policy) (s : strip) (pm st n : Z) (a : word) : Prop :=
  if andb (p_thp p) (andb (Z.ltb 0 n) (Z.eqb (n mod pmd_size) 0)) then
    (exists ret, search_addr h p s pm st (n + pmd_size) ret /\ bv_unsigned a = thp_align p (bv_unsigned ret))
    \/ ((forall ret, ~ search_addr h p s pm st (n + pmd_size) ret) /\ search_addr h p s pm st n a)
  else search_addr h p s pm st n a.

Definition fresh_addr (h : VmMaps) (p : policy) (s : strip) (pm n : Z) (a : word) : Prop :=
  exists st, stack_low_ok h st /\ fresh_addr_at h p s pm st n a.

(** The address an [mmap] with hint [hint] and page-rounded length [n] gets.
    Linux rounds the hint down to a page; one below a page is no hint, and
    then the request gets [fresh_addr].  Otherwise the hint, raised to [pm],
    when [n] bytes fit there (clear of the stack, too), else the plain search
    (a hint makes the kernel skip the huge-page alignment). *)
Definition mmap_addr (h : VmMaps) (p : policy) (s : strip) (pm : Z) (hint : word) (n : Z) (a : word) : Prop :=
  let down := page_round_down_Z (bv_unsigned hint) in
  if Z.eqb down 0 then fresh_addr h p s pm n a
  else
    let at_hint := Z.max down pm in
    exists st, stack_low_ok h st /\
    let hint_ok := exists w, bv_unsigned w = at_hint /\ fits h p s st true n pm (alloc_top h) w in
    ((hint_ok /\ bv_unsigned a = at_hint) \/ (~ hint_ok /\ search_addr h p s pm st n a)).

(** An error answer: -4095 .. -1 read as an unsigned word. *)
Definition errno_answer (r : word) : Prop := (2 ^ 64 - 4096 < bv_unsigned r)%Z.

(** The policy keeps an [mremap] in place: lps can answer in place, and the
    grown range overlaps no vDSO mapping in place (a shrink always may). *)
Definition mremap_in_place (p : policy) (s : strip) (i : SyscallInput) (m : Model) : Prop :=
  (exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ eff_ret eff = in_arg i 0)
  /\ ((page_round_up_Z (bv_unsigned (in_arg i 2)) <= page_round_up_Z (bv_unsigned (in_arg i 1)))%Z
      \/ off_vdso (m_vmmaps m) p s (page_round_up_Z (bv_unsigned (in_arg i 2))) (in_arg i 0)).

(** The answer [r] to the placement request [i] at model [m] is the policy's,
    with vm.mmap_min_addr [pm]: an error; for an [mmap], [mmap_addr]; for an
    [mremap], the old address when the policy keeps it in place, else a fresh
    address of its page-rounded new size.  A [brk] has no choice to make. *)
Definition canonical_ret (p : policy) (s : strip) (pm : Z) (i : SyscallInput) (m : Model) (r : word) : Prop :=
  errno_answer r
  \/ (bv_unsigned (in_sysno i) = 222%Z
      /\ mmap_addr (m_vmmaps m) p s pm (in_arg i 0) (page_round_up_Z (bv_unsigned (in_arg i 1))) r)
  \/ (bv_unsigned (in_sysno i) = 216%Z
      /\ ((r = in_arg i 0 /\ mremap_in_place p s i m)
          \/ (~ mremap_in_place p s i m
              /\ fresh_addr (m_vmmaps m) p s pm (page_round_up_Z (bv_unsigned (in_arg i 2))) r)))
  \/ bv_unsigned (in_sysno i) = 214%Z.

(** The step from [c1] to [c2] places as the policy does: if [c1] has a
    placement request pending, [c2] is its outcome for an answer of the
    policy's. *)
Definition canonical_step (p : policy) (s : strip) (segs : list Segment) (c1 c2 : config) : Prop :=
  forall x8 len, placement_at segs c1 x8 len ->
    exists eff m' evs m'',
      syscall_spec (sys_input segs (cfg_ms c1) x8) (cfg_model c1) (Ok eff m' evs)
      /\ c2 = mkCfg (advance_past_svc (apply_effect (cfg_ms c1) eff)) m''
      /\ canonical_ret p s (p_min p) (sys_input segs (cfg_ms c1) x8) (cfg_model c1) (eff_ret eff).

(** lps's [star_cfg] over the canonical steps of one policy, from the vDSO
    state [s]; after each step the execution may drop vDSO mappings. *)
Inductive star_canonical (p : policy) (segs : list Segment) (cfg : SpuriousCfg)
    : strip -> config -> list event -> config -> Prop :=
| star_canonical_refl : forall s c, star_canonical p segs cfg s c [] c
| star_canonical_step : forall s s' c1 evs c2 tr c3,
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    canonical_step p s segs c1 c2 ->
    strip_le s' s ->
    star_canonical p segs cfg s' c2 tr c3 ->
    star_canonical p segs cfg s c1 (evs ++ tr) c3.

(** A search answers whenever anything fits: the fits are bounded by [top]
    above and by [lo] below, so there is a highest and a lowest. *)
Lemma highest_fit_exists : forall h p s st g n lo top a,
  (0 <= n)%Z -> fits h p s st g n lo top a -> exists b, highest_fit h p s st g n lo top b.
Proof.
  intros h p s st g n lo top a Hn Ha.
  remember (Z.to_nat (top - bv_unsigned a)) as k eqn:Hk.
  revert a Ha Hk. induction k as [k IH] using lt_wf_ind. intros a Ha Hk.
  destruct (classic (exists a', fits h p s st g n lo top a' /\ (bv_unsigned a < bv_unsigned a')%Z))
    as [(a' & Ha' & Hlt) | Hno].
  - assert (Hlt' : (Z.to_nat (top - bv_unsigned a') < k)%nat).
    { subst k. destruct Ha' as (_ & _ & _ & Hle' & _). apply Z2Nat.inj_lt; lia. }
    exact (IH _ Hlt' a' Ha' eq_refl).
  - exists a. split; [exact Ha |]. intros a' Ha'.
    destruct (Z_le_gt_dec (bv_unsigned a') (bv_unsigned a)) as [Hle | Hgt]; [exact Hle |].
    exfalso. apply Hno. exists a'. split; [exact Ha' | lia].
Qed.

Lemma lowest_fit_exists : forall h p s st g n lo top a,
  fits h p s st g n lo top a -> exists b, lowest_fit h p s st g n lo top b.
Proof.
  intros h p s st g n lo top a Ha.
  remember (Z.to_nat (bv_unsigned a - lo)) as k eqn:Hk.
  revert a Ha Hk. induction k as [k IH] using lt_wf_ind. intros a Ha Hk.
  destruct (classic (exists a', fits h p s st g n lo top a' /\ (bv_unsigned a' < bv_unsigned a)%Z))
    as [(a' & Ha' & Hlt) | Hno].
  - assert (Hlt' : (Z.to_nat (bv_unsigned a' - lo) < k)%nat).
    { subst k. destruct Ha' as (_ & Hlo' & _). apply Z2Nat.inj_lt; lia. }
    exact (IH _ Hlt' a' Ha' eq_refl).
  - exists a. split; [exact Ha |]. intros a' Ha'.
    destruct (Z_le_gt_dec (bv_unsigned a) (bv_unsigned a')) as [Hle | Hgt]; [exact Hle |].
    exfalso. apply Hno. exists a'. split; [exact Ha' | lia].
Qed.

Lemma fits_weaken : forall h p s st g n lo lo' top top' a,
  (lo' <= lo)%Z -> (top <= top')%Z -> fits h p s st g n lo top a -> fits h p s st g n lo' top' a.
Proof.
  intros h p s st g n lo lo' top top' a Hlo Htop (Hal & Hl & Hpos & Ht & Hfree & Hv & Hc).
  split; [exact Hal | split; [lia | split; [exact Hpos | split; [lia | split; [exact Hfree | split; [exact Hv | exact Hc]]]]]].
Qed.

(** An unguarded fit that keeps clear of the stack is a guarded one. *)
Lemma fits_guard : forall h p s st n lo top a,
  fits h p s st false n lo top a -> clear_of_stack h p s st n a -> fits h p s st true n lo top a.
Proof.
  intros h p s st n lo top a (Hal & Hl & Hpos & Ht & Hfree & Hv & _) Hc.
  split; [exact Hal | split; [exact Hl | split; [exact Hpos | split; [exact Ht | split; [exact Hfree | split; [exact Hv | intros _; exact Hc]]]]]].
Qed.

(** A guarded fit is an unguarded one. *)
Lemma fits_unguard : forall h p s st n lo top a,
  fits h p s st true n lo top a -> fits h p s st false n lo top a.
Proof.
  intros h p s st n lo top a (Hal & Hl & Hpos & Ht & Hfree & Hv & _).
  split; [exact Hal | split; [exact Hl | split; [exact Hpos | split; [exact Ht | split; [exact Hfree | split; [exact Hv | discriminate]]]]]].
Qed.

(** Whether a range keeps clear of the stack reads only its end. *)
Lemma clear_of_stack_same : forall h p s st n a a',
  bv_unsigned a = bv_unsigned a' -> clear_of_stack h p s st n a -> clear_of_stack h p s st n a'.
Proof. intros h p s st n a a' E H. unfold clear_of_stack in *. rewrite <- E. exact H. Qed.

(** The top-down search answers whenever some fit that keeps clear of the
    stack lies wholly at or above TASK_UNMAPPED_BASE. *)
Lemma search_addr_exists_topdown : forall h p s pm st n a,
  p_legacy p = false -> (0 <= n)%Z -> fits h p s st true n (Z.max pm task_unmapped_base) (alloc_top h) a ->
  exists b, search_addr h p s pm st n b.
Proof.
  intros h p s pm st n a Hl Hn Ha. unfold search_addr. rewrite Hl.
  set (low := Z.min (mmap_top h p) (Z.max 0 (st - p_guard p))).
  assert (Hfall : (forall a1, highest_fit h p s st false n pm (mmap_top h p) a1 ->
                              ~ clear_of_stack h p s st n a1) ->
                  exists b, (highest_fit h p s st false n pm (mmap_top h p) b /\ clear_of_stack h p s st n b)
                    \/ ((forall a1, highest_fit h p s st false n pm (mmap_top h p) a1 ->
                                    ~ clear_of_stack h p s st n a1) /\ highest_fit h p s st false n pm low b)
                    \/ ((forall a1, highest_fit h p s st false n pm (mmap_top h p) a1 ->
                                    ~ clear_of_stack h p s st n a1)
                        /\ (forall a', ~ fits h p s st false n pm low a')
                        /\ lowest_fit h p s st true n (Z.max pm task_unmapped_base) (alloc_top h) b)).
  { intros Hun.
    destruct (classic (exists a', fits h p s st false n pm low a')) as [(a' & Ha') | Hno].
    - destruct (highest_fit_exists h p s st false n pm low a' Hn Ha') as (b & Hb).
      exists b. right. left. split; [exact Hun | exact Hb].
    - destruct (lowest_fit_exists h p s st true n _ _ a Ha) as (b & Hb).
      exists b. right. right. split; [exact Hun | split; [| exact Hb]].
      intros a' Ha'. apply Hno. exists a'. exact Ha'. }
  destruct (classic (exists a', fits h p s st false n pm (mmap_top h p) a')) as [(a' & Ha') | Hno].
  - destruct (highest_fit_exists h p s st false n pm (mmap_top h p) a' Hn Ha') as (b & Hb).
    destruct (classic (clear_of_stack h p s st n b)) as [Hc | Hnc].
    + exists b. left. split; [exact Hb | exact Hc].
    + apply Hfall. intros a1 Ha1 Hc1. apply Hnc.
      apply (clear_of_stack_same h p s st n a1 b); [| exact Hc1].
      destruct Hb as (Hbf & Hbmax). destruct Ha1 as (Ha1f & Ha1max).
      pose proof (Hbmax a1 Ha1f). pose proof (Ha1max b Hbf). lia.
  - apply Hfall. intros a1 (Ha1 & _) _. apply Hno. exists a1. exact Ha1.
Qed.

(** The legacy search answers whenever some fit lies at or above its base. *)
Lemma search_addr_exists_legacy : forall h p s pm st n a,
  p_legacy p = true -> fits h p s st true n (Z.max pm (p_base p)) (alloc_top h) a ->
  exists b, search_addr h p s pm st n b.
Proof.
  intros h p s pm st n a Hl Ha. unfold search_addr. rewrite Hl.
  exact (lowest_fit_exists h p s st true n _ _ a Ha).
Qed.

(** The search's answer passes the guard of lps's fresh-grant arms:
    page-aligned, nonzero, below [alloc_top], overlapping nothing in the
    ledger (the arm's remaining conjunct, [mmap_noreserve_backed_ok], does
    not read the address); it also keeps clear of the stack. *)
Lemma search_addr_fits : forall h p s pm st n a,
  search_addr h p s pm st n a -> fits h p s st true n pm (alloc_top h) a.
Proof.
  intros h p s pm st n a H. unfold search_addr in H.
  destruct (p_legacy p).
  - destruct H as (Hf & _).
    apply (fits_weaken h p s st true n (Z.max pm (p_base p)) pm (alloc_top h)); [lia | lia | exact Hf].
  - destruct H as [((Hf & _) & Hc) | [(_ & (Hf & _)) | (_ & _ & (Hf & _))]].
    + apply fits_guard; [| exact Hc].
      apply (fits_weaken h p s st false n pm pm (mmap_top h p)); [lia | unfold mmap_top; lia | exact Hf].
    + apply fits_guard.
      * apply (fits_weaken h p s st false n pm pm (Z.min (mmap_top h p) (Z.max 0 (st - p_guard p))));
          [lia | unfold mmap_top; lia | exact Hf].
      * left. destruct Hf as (_ & _ & _ & Ht & _). lia.
    + apply (fits_weaken h p s st true n (Z.max pm task_unmapped_base) pm (alloc_top h)); [lia | lia | exact Hf].
Qed.

(** ** The executions the statements read *)

Lemma star_canonical_star_cfg : forall p segs cfg s c tr c',
  star_canonical p segs cfg s c tr c' -> star_cfg segs cfg c tr c'.
Proof.
  intros p segs cfg s c tr c' H. induction H as [s c | s s' c1 evs c2 tr c3 Hstep _ _ _ IH].
  - apply star_cfg_refl.
  - eapply star_cfg_step; [exact Hstep | exact IH].
Qed.

(** From [c1], under policy [p] with vDSO state [s], some step is canonical. *)
Definition canon_can_step (p : policy) (s : strip) (segs : list Segment) (cfg : SpuriousCfg)
    (c1 : config) : Prop :=
  exists evs c2, sstep_cfg segs cfg c1 evs (SNext c2) /\ canonical_step p s segs c1 c2.

(** [star_canonical], and, at a configuration that has no canonical step and
    is not unplaced, any lps step.  [dev] records that such a step was taken;
    from then on no step is taken from an unplaced configuration. *)
Inductive star_canon_fb (p : policy) (segs : list Segment) (cfg : SpuriousCfg)
    : bool -> strip -> config -> list event -> config -> Prop :=
| scf_refl : forall dev s c, star_canon_fb p segs cfg dev s c [] c
| scf_canon : forall dev s s' c1 evs c2 tr c3,
    (dev = true -> ~ unplaced_at segs c1) ->
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    canonical_step p s segs c1 c2 ->
    strip_le s' s ->
    star_canon_fb p segs cfg dev s' c2 tr c3 ->
    star_canon_fb p segs cfg dev s c1 (evs ++ tr) c3
| scf_fallback : forall dev s c1 evs c2 tr c3,
    ~ canon_can_step p s segs cfg c1 ->
    ~ unplaced_at segs c1 ->
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    star_canon_fb p segs cfg true s c2 tr c3 ->
    star_canon_fb p segs cfg dev s c1 (evs ++ tr) c3.

(** The canonical executions of policy [p], from [c] with the whole vDSO in
    place. *)
Definition canon_run (p : policy) (segs : list Segment) (cfg : SpuriousCfg) (c : config)
    (tr : list event) (c' : config) : Prop :=
  star_canon_fb p segs cfg false full_strip c tr c'.

(** lps's [star_cfg], except that no step is taken from an unplaced or a
    budget-refused configuration. *)
Inductive star_guarded (segs : list Segment) (cfg : SpuriousCfg)
    : config -> list event -> config -> Prop :=
| sg_refl : forall c, star_guarded segs cfg c [] c
| sg_step : forall c1 evs c2 tr c3,
    ~ unplaced_at segs c1 ->
    ~ budget_refused_at segs c1 ->
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    star_guarded segs cfg c2 tr c3 ->
    star_guarded segs cfg c1 (evs ++ tr) c3.

Lemma star_canon_fb_star_cfg : forall p segs cfg dev s c tr c',
  star_canon_fb p segs cfg dev s c tr c' -> star_cfg segs cfg c tr c'.
Proof.
  intros p segs cfg dev s c tr c' H.
  induction H as [dev s c | dev s s' c1 evs c2 tr c3 _ Hstep _ _ _ IH
                  | dev s c1 evs c2 tr c3 _ _ Hstep _ IH].
  - apply star_cfg_refl.
  - eapply star_cfg_step; [exact Hstep | exact IH].
  - eapply star_cfg_step; [exact Hstep | exact IH].
Qed.

Lemma canon_run_star_cfg : forall p segs cfg c tr c',
  canon_run p segs cfg c tr c' -> star_cfg segs cfg c tr c'.
Proof. intros p segs cfg c tr c' H. exact (star_canon_fb_star_cfg _ _ _ _ _ _ _ _ H). Qed.

Lemma star_canonical_canon_fb : forall p segs cfg s c tr c',
  star_canonical p segs cfg s c tr c' -> star_canon_fb p segs cfg false s c tr c'.
Proof.
  intros p segs cfg s c tr c' H.
  induction H as [s c | s s' c1 evs c2 tr c3 Hstep Hc Hle _ IH].
  - apply scf_refl.
  - eapply scf_canon; [intros E; discriminate E | eassumption ..].
Qed.

(** Every canonical execution of [p] from the whole vDSO is one of these. *)
Lemma star_canonical_canon_run : forall p segs cfg c tr c',
  star_canonical p segs cfg full_strip c tr c' -> canon_run p segs cfg c tr c'.
Proof. intros p segs cfg c tr c' H. exact (star_canonical_canon_fb _ _ _ _ _ _ _ H). Qed.

Lemma star_guarded_star_cfg : forall segs cfg c tr c',
  star_guarded segs cfg c tr c' -> star_cfg segs cfg c tr c'.
Proof.
  intros segs cfg c tr c' H. induction H as [c | c1 evs c2 tr c3 _ _ Hstep _ IH].
  - apply star_cfg_refl.
  - eapply star_cfg_step; [exact Hstep | exact IH].
Qed.

(** From [c0] no execution reaches a configuration with a request pending
    whose address the model picks. *)
Definition no_placement_from (segs : list Segment) (cfg : SpuriousCfg) (c0 : config) : Prop :=
  forall tr c, star_cfg segs cfg c0 tr c -> forall x8 len, ~ placement_at segs c x8 len.

(** A program that never asks the model to place anything has only canonical
    executions, under every policy. *)
Lemma canon_run_of_no_placement : forall p segs cfg c0 tr c,
  no_placement_from segs cfg c0 -> star_cfg segs cfg c0 tr c -> canon_run p segs cfg c0 tr c.
Proof.
  intros p segs cfg c0 tr c Hn H. unfold canon_run. revert Hn.
  induction H as [c | c1 evs c2 tr c3 Hstep Hstar IH]; intros Hn.
  - apply scf_refl.
  - apply (scf_canon p segs cfg false full_strip full_strip c1 evs c2 tr c3).
    + intros E. discriminate E.
    + exact Hstep.
    + intros x8 len Hpl. exfalso. exact (Hn [] c1 ltac:(apply star_cfg_refl) x8 len Hpl).
    + split; intros E; exact E.
    + apply IH. intros tr' c' Hs. apply (Hn (evs ++ tr') c'). eapply star_cfg_step; [exact Hstep | exact Hs].
Qed.

(** ** What the statements read, for one policy [p] *)

Definition canon_trace (cfg : SpuriousCfg) (p : policy) (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) (tr : list event) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists tr' c, canon_run p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr' c
                  /\ is_prefix tr tr'
  end.

Definition canon_budget_refused (cfg : SpuriousCfg) (p : policy) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists tr c, canon_run p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c
                 /\ budget_refused_at segs c
  end.

(** An error that a canonical execution of [p] reaches, or that any other
    execution reaches before an unplaced or budget-refused configuration. *)
Definition guarded_reaches_error (cfg : SpuriousCfg) (p : policy) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists tr c evs,
      ((star_guarded segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c
        /\ ~ unplaced_at segs c /\ ~ budget_refused_at segs c)
       \/ canon_run p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr c)
      /\ sstep_cfg segs cfg c evs SError
  end.

Definition guarded_trace (cfg : SpuriousCfg) (p : policy) (img : Image) (lim : Z) (en : ExecEntry)
    (inp : ProcInput) (tr : list event) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    exists tr' c,
      (star_guarded segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr' c
       \/ canon_run p segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp) tr' c)
      /\ is_prefix tr tr'
  end.

Definition guarded_dies_by_signal (cfg : SpuriousCfg) (p : policy) (img : Image) (lim : Z)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  exists tr sig fs, guarded_trace cfg p img lim en inp tr /\ In (KillEv sig fs) tr.

Lemma canon_trace_sub : forall cfg p img lim en inp tr,
  canon_trace cfg p img lim en inp tr -> bh_traces (run_scfg cfg img lim en inp) tr.
Proof.
  intros cfg p [segs pc ph] lim [sp brk0 mbase rnd] inp tr H.
  cbn [canon_trace] in H. destruct H as (tr' & c & Hs & Hp).
  cbn [run_scfg bh_traces]. unfold obs_trace_cfg. exists tr', c.
  split; [apply (canon_run_star_cfg p); exact Hs | exact Hp].
Qed.

(** Prefix-closed, like lps's trace sets. *)
Lemma canon_trace_prefix : forall cfg p img lim en inp tr tr',
  canon_trace cfg p img lim en inp tr -> is_prefix tr' tr -> canon_trace cfg p img lim en inp tr'.
Proof.
  intros cfg p [segs pc ph] lim [sp brk0 mbase rnd] inp tr tr' H Hp.
  cbn [canon_trace] in H |- *. destruct H as (t & c & Hs & Ht).
  exists t, c. split; [exact Hs | exact (is_prefix_trans _ _ _ Hp Ht)].
Qed.

(** The premise is implied by [agrees_in]'s, for every policy: no input
    [agrees_in] covers is lost. *)
Lemma canon_budget_refused_sub : forall cfg p img lim en inp,
  canon_budget_refused cfg p img lim en inp -> run_scfg_budget_refused cfg img lim en inp.
Proof.
  intros cfg p [segs pc ph] lim [sp brk0 mbase rnd] inp H.
  cbn [canon_budget_refused] in H. destruct H as (tr & c & Hs & Hb).
  cbn [run_scfg_budget_refused]. exists tr, c.
  split; [apply (canon_run_star_cfg p); exact Hs | exact Hb].
Qed.

Lemma guarded_reaches_error_sub : forall cfg p img lim en inp,
  guarded_reaches_error cfg p img lim en inp -> bh_errors (run_scfg cfg img lim en inp).
Proof.
  intros cfg p [segs pc ph] lim [sp brk0 mbase rnd] inp H.
  cbn [guarded_reaches_error] in H. destruct H as (tr & c & evs & Hs & He).
  cbn [run_scfg bh_errors]. unfold reaches_error_cfg. exists tr, c, evs. split; [| exact He].
  destruct Hs as [(Hs & _) | Hs]; [apply star_guarded_star_cfg | apply (canon_run_star_cfg p)]; exact Hs.
Qed.

Lemma guarded_trace_sub : forall cfg p img lim en inp tr,
  guarded_trace cfg p img lim en inp tr -> bh_traces (run_scfg cfg img lim en inp) tr.
Proof.
  intros cfg p [segs pc ph] lim [sp brk0 mbase rnd] inp tr H.
  cbn [guarded_trace] in H. destruct H as (tr' & c & Hs & Hp).
  cbn [run_scfg bh_traces]. unfold obs_trace_cfg. exists tr', c. split; [| exact Hp].
  destruct Hs as [Hs | Hs]; [apply star_guarded_star_cfg | apply (canon_run_star_cfg p)]; exact Hs.
Qed.

Lemma guarded_dies_by_signal_sub : forall cfg p img lim en inp,
  guarded_dies_by_signal cfg p img lim en inp -> dies_by_signal (run_scfg cfg img lim en inp).
Proof.
  intros cfg p img lim en inp (tr & sig & fs & Ht & Hin).
  exists tr, sig, fs. split; [apply (guarded_trace_sub cfg p); exact Ht | exact Hin].
Qed.

(** ** The shapes *)

(** [agrees_in_room env lim_plain lim_san plain san]: for every claimed
    placement policy [p], every valid input and every valid pair of entries
    on which no canonical execution of [p] of the plain build is refused
    memory for exceeding [lim_plain], when the environment refuses only what
    [env] allows:
    - no canonical execution of [p] of the plain build, and no execution of
      it before an unplaced or budget-refused configuration, reaches an
      error;
    - the same for the sanitizer build;
    - the two builds' canonical executions of [p] have the same finite
      traces. *)
Definition agrees_in_room (env : SpuriousCfg) (lim_plain lim_san : Z) (plain san : Image) : Prop :=
  forall (p : policy) (en_plain en_san : ExecEntry) (inp : ProcInput),
    policy_ok p ->
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input inp ->
    ~ canon_budget_refused env p plain lim_plain en_plain inp ->
    ~ guarded_reaches_error env p plain lim_plain en_plain inp
    /\ ~ guarded_reaches_error env p san lim_san en_san inp
    /\ (forall tr, canon_trace env p plain lim_plain en_plain inp tr
                   <-> canon_trace env p san lim_san en_san inp tr).

(** The same claim with abort() read as death by SIGABRT
    ([agrees_in_abort_modelled]): it still forbids it, in both builds. *)
Definition agrees_in_abort_modelled_room (env : SpuriousCfg) (lim_plain lim_san : Z)
    (plain san : Image) : Prop :=
  forall (p : policy) (en_plain en_san : ExecEntry) (inp : ProcInput),
    policy_ok p ->
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_abort inp ->
    ~ canon_budget_refused env p plain lim_plain en_plain inp ->
    (~ guarded_reaches_error env p plain lim_plain en_plain inp
     /\ ~ guarded_dies_by_signal env p plain lim_plain en_plain inp)
    /\ (~ guarded_reaches_error env p san lim_san en_san inp
        /\ ~ guarded_dies_by_signal env p san lim_san en_san inp)
    /\ (forall tr, canon_trace env p plain lim_plain en_plain inp tr
                   <-> canon_trace env p san lim_san en_san inp tr).

(** The same claim on inputs whose advertised machine is RV64GC
    ([agrees_in_rv64gc]). *)
Definition agrees_in_rv64gc_room (env : SpuriousCfg) (lim_plain lim_san : Z)
    (plain san : Image) : Prop :=
  forall (p : policy) (en_plain en_san : ExecEntry) (inp : ProcInput),
    policy_ok p ->
    valid_entry plain en_plain inp ->
    valid_entry san en_san inp ->
    valid_input_hwcap_rv64gc inp ->
    ~ canon_budget_refused env p plain lim_plain en_plain inp ->
    ~ guarded_reaches_error env p plain lim_plain en_plain inp
    /\ ~ guarded_reaches_error env p san lim_san en_san inp
    /\ (forall tr, canon_trace env p plain lim_plain en_plain inp tr
                   <-> canon_trace env p san lim_san en_san inp tr).

(** ** What a proof needs beside [agrees_in]'s facts *)

(** For every claimed policy, every trace of the run is a trace of a
    canonical execution of that policy. *)
Definition canon_complete (vi : ProcInput -> Prop) (cfg : SpuriousCfg) (img : Image) (lim : Z) : Prop :=
  forall p en inp, policy_ok p -> valid_entry img en inp -> vi inp ->
    forall tr, bh_traces (run_scfg cfg img lim en inp) tr -> canon_trace cfg p img lim en inp tr.

(** A program that never asks the model to place anything is canonically
    complete. *)
Lemma canon_complete_of_no_placement : forall vi cfg segs pc ph lim,
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> vi inp ->
     match en with
     | mkEntry sp brk0 mbase rnd =>
       no_placement_from segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp)
     end) ->
  canon_complete vi cfg (mkImage segs pc ph) lim.
Proof.
  intros vi cfg segs pc ph lim Hn p [sp brk0 mbase rnd] inp _ Hv Hi tr Ht.
  specialize (Hn _ _ Hv Hi). cbn in Hn.
  cbn [run_scfg bh_traces] in Ht. unfold obs_trace_cfg in Ht. destruct Ht as (tr' & c & Hs & Hp).
  cbn [canon_trace]. exists tr', c. split; [| exact Hp].
  exact (canon_run_of_no_placement p _ _ _ _ _ Hn Hs).
Qed.

(** A proof that shows, for every policy, on every input on which no
    canonical plain execution of that policy is refused for the budget (for
    instance on every input), that both runs are error-free with equal trace
    sets, proves the statement once each build's traces are canonical traces
    of every policy. *)
Lemma agrees_in_canon_of_parts : forall env lp ls pl sn,
  (forall p en_p en_s inp, policy_ok p ->
     valid_entry pl en_p inp -> valid_entry sn en_s inp -> valid_input inp ->
     ~ canon_budget_refused env p pl lp en_p inp ->
     error_free (run_scfg env pl lp en_p inp) /\ error_free (run_scfg env sn ls en_s inp)
     /\ trace_equiv (bh_traces (run_scfg env pl lp en_p inp)) (bh_traces (run_scfg env sn ls en_s inp))) ->
  canon_complete valid_input env pl lp -> canon_complete valid_input env sn ls ->
  agrees_in_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn H Cp Cs p en_p en_s inp Hpol Hp Hs Hi Hb.
  destruct (H p en_p en_s inp Hpol Hp Hs Hi Hb) as (Ep & Es & T).
  split; [| split; [| intros tr; split; intros Ht]].
  - intros Hr. exact (Ep (guarded_reaches_error_sub _ _ _ _ _ _ Hr)).
  - intros Hr. exact (Es (guarded_reaches_error_sub _ _ _ _ _ _ Hr)).
  - apply (Cs p en_s inp Hpol Hs Hi). apply (proj1 (T tr)). exact (canon_trace_sub _ _ _ _ _ _ _ Ht).
  - apply (Cp p en_p inp Hpol Hp Hi). apply (proj2 (T tr)). exact (canon_trace_sub _ _ _ _ _ _ _ Ht).
Qed.

Lemma agrees_in_abort_modelled_canon_of_parts : forall env lp ls pl sn,
  (forall p en_p en_s inp, policy_ok p ->
     valid_entry pl en_p inp -> valid_entry sn en_s inp -> valid_input_abort inp ->
     ~ canon_budget_refused env p pl lp en_p inp ->
     error_free_unkilled (run_scfg env pl lp en_p inp) /\ error_free_unkilled (run_scfg env sn ls en_s inp)
     /\ trace_equiv (bh_traces (run_scfg env pl lp en_p inp)) (bh_traces (run_scfg env sn ls en_s inp))) ->
  canon_complete valid_input_abort env pl lp -> canon_complete valid_input_abort env sn ls ->
  agrees_in_abort_modelled_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn H Cp Cs p en_p en_s inp Hpol Hp Hs Hi Hb.
  destruct (H p en_p en_s inp Hpol Hp Hs Hi Hb) as ((Ep & Kp) & (Es & Ks) & T).
  split; [| split; [| intros tr; split; intros Ht]].
  - split; intros Hr; [exact (Ep (guarded_reaches_error_sub _ _ _ _ _ _ Hr))
                       | exact (Kp (guarded_dies_by_signal_sub _ _ _ _ _ _ Hr))].
  - split; intros Hr; [exact (Es (guarded_reaches_error_sub _ _ _ _ _ _ Hr))
                       | exact (Ks (guarded_dies_by_signal_sub _ _ _ _ _ _ Hr))].
  - apply (Cs p en_s inp Hpol Hs Hi). apply (proj1 (T tr)). exact (canon_trace_sub _ _ _ _ _ _ _ Ht).
  - apply (Cp p en_p inp Hpol Hp Hi). apply (proj2 (T tr)). exact (canon_trace_sub _ _ _ _ _ _ _ Ht).
Qed.

Lemma agrees_in_rv64gc_canon_of_parts : forall env lp ls pl sn,
  (forall p en_p en_s inp, policy_ok p ->
     valid_entry pl en_p inp -> valid_entry sn en_s inp -> valid_input_hwcap_rv64gc inp ->
     ~ canon_budget_refused env p pl lp en_p inp ->
     error_free (run_scfg env pl lp en_p inp) /\ error_free (run_scfg env sn ls en_s inp)
     /\ trace_equiv (bh_traces (run_scfg env pl lp en_p inp)) (bh_traces (run_scfg env sn ls en_s inp))) ->
  canon_complete valid_input_hwcap_rv64gc env pl lp -> canon_complete valid_input_hwcap_rv64gc env sn ls ->
  agrees_in_rv64gc_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn H Cp Cs p en_p en_s inp Hpol Hp Hs Hi Hb.
  destruct (H p en_p en_s inp Hpol Hp Hs Hi Hb) as (Ep & Es & T).
  split; [| split; [| intros tr; split; intros Ht]].
  - intros Hr. exact (Ep (guarded_reaches_error_sub _ _ _ _ _ _ Hr)).
  - intros Hr. exact (Es (guarded_reaches_error_sub _ _ _ _ _ _ Hr)).
  - apply (Cs p en_s inp Hpol Hs Hi). apply (proj1 (T tr)). exact (canon_trace_sub _ _ _ _ _ _ _ Ht).
  - apply (Cp p en_p inp Hpol Hp Hi). apply (proj2 (T tr)). exact (canon_trace_sub _ _ _ _ _ _ _ Ht).
Qed.

(** For a proof of [agrees_in] itself: also every budget refusal of the
    plain run is reached by a canonical execution of every policy. *)
Lemma agrees_in_canon_of_agrees_in : forall env lp ls pl sn,
  agrees_in env lp ls pl sn ->
  (forall p en inp, policy_ok p -> valid_entry pl en inp -> valid_input inp ->
     run_scfg_budget_refused env pl lp en inp -> canon_budget_refused env p pl lp en inp) ->
  canon_complete valid_input env pl lp -> canon_complete valid_input env sn ls ->
  agrees_in_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn H Bp Cp Cs.
  apply agrees_in_canon_of_parts; [| exact Cp | exact Cs].
  intros p en_p en_s inp Hpol Hp Hs Hi Hb. apply (H en_p en_s inp Hp Hs Hi).
  intros Hr. exact (Hb (Bp p en_p inp Hpol Hp Hi Hr)).
Qed.

(** A proof that judges each build on the statement's own executions: for
    every policy, on every input on which no canonical plain execution of
    that policy is refused for the budget, each build reaches no guarded
    error and its canonical traces are exactly one set [T], the same for
    both builds (for instance a set that depends only on the input). *)
Lemma agrees_in_canon_of_spec : forall env lp ls pl sn
    (T : policy -> ExecEntry -> ExecEntry -> ProcInput -> list event -> Prop),
  (forall p en_p en_s inp, policy_ok p ->
     valid_entry pl en_p inp -> valid_entry sn en_s inp -> valid_input inp ->
     ~ canon_budget_refused env p pl lp en_p inp ->
     ~ guarded_reaches_error env p pl lp en_p inp /\ ~ guarded_reaches_error env p sn ls en_s inp
     /\ (forall tr, canon_trace env p pl lp en_p inp tr <-> T p en_p en_s inp tr)
     /\ (forall tr, canon_trace env p sn ls en_s inp tr <-> T p en_p en_s inp tr)) ->
  agrees_in_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn T H p en_p en_s inp Hpol Hp Hs Hi Hb.
  destruct (H p en_p en_s inp Hpol Hp Hs Hi Hb) as (Ep & Es & Tp & Ts).
  split; [exact Ep | split; [exact Es |]].
  intros tr. rewrite (Tp tr), (Ts tr). reflexivity.
Qed.

Lemma agrees_in_abort_modelled_canon_of_spec : forall env lp ls pl sn
    (T : policy -> ExecEntry -> ExecEntry -> ProcInput -> list event -> Prop),
  (forall p en_p en_s inp, policy_ok p ->
     valid_entry pl en_p inp -> valid_entry sn en_s inp -> valid_input_abort inp ->
     ~ canon_budget_refused env p pl lp en_p inp ->
     (~ guarded_reaches_error env p pl lp en_p inp /\ ~ guarded_dies_by_signal env p pl lp en_p inp)
     /\ (~ guarded_reaches_error env p sn ls en_s inp /\ ~ guarded_dies_by_signal env p sn ls en_s inp)
     /\ (forall tr, canon_trace env p pl lp en_p inp tr <-> T p en_p en_s inp tr)
     /\ (forall tr, canon_trace env p sn ls en_s inp tr <-> T p en_p en_s inp tr)) ->
  agrees_in_abort_modelled_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn T H p en_p en_s inp Hpol Hp Hs Hi Hb.
  destruct (H p en_p en_s inp Hpol Hp Hs Hi Hb) as (Ep & Es & Tp & Ts).
  split; [exact Ep | split; [exact Es |]].
  intros tr. rewrite (Tp tr), (Ts tr). reflexivity.
Qed.

Lemma agrees_in_rv64gc_canon_of_spec : forall env lp ls pl sn
    (T : policy -> ExecEntry -> ExecEntry -> ProcInput -> list event -> Prop),
  (forall p en_p en_s inp, policy_ok p ->
     valid_entry pl en_p inp -> valid_entry sn en_s inp -> valid_input_hwcap_rv64gc inp ->
     ~ canon_budget_refused env p pl lp en_p inp ->
     ~ guarded_reaches_error env p pl lp en_p inp /\ ~ guarded_reaches_error env p sn ls en_s inp
     /\ (forall tr, canon_trace env p pl lp en_p inp tr <-> T p en_p en_s inp tr)
     /\ (forall tr, canon_trace env p sn ls en_s inp tr <-> T p en_p en_s inp tr)) ->
  agrees_in_rv64gc_room env lp ls pl sn.
Proof.
  intros env lp ls pl sn T H p en_p en_s inp Hpol Hp Hs Hi Hb.
  destruct (H p en_p en_s inp Hpol Hp Hs Hi Hb) as (Ep & Es & Tp & Ts).
  split; [exact Ep | split; [exact Es |]].
  intros tr. rewrite (Tp tr), (Ts tr). reflexivity.
Qed.
