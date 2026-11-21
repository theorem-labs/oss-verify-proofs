(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YK1b.v at , lines 6-8, 11-90, 99-101, 108-110, 112-312, 319-338, ported to the model. *)
(** * StoreOk — discharging the machine-store bound

    [RiscvSemantics.store_ok segs m a n] is the premise every machine
    store carries: each of the [n] bytes from [a] must be writable
    in [wview], the overlay merged over the 'w' segments.  It is the
    same view the syscall specs write through, and the SIGSEGV
    analogue when it fails (see the comment at [store_ok] itself for
    why an unbounded store made [strong_universal] falsifiable).

    Proofs never unfold it.  Every store site in the examples is one of
    three shapes, and this file turns each into a one-line side
    condition:

    - the STACK: an address in the RLIMIT_STACK window
      [[Run.stack_window_lo], init_sp) that [Run.init_machine_state]
      (and its proof-side mirror [PropExec.wrap_mem]) zero-maps up
      front — [store_ok_wrap_window];
    - a HEAP grant: an address inside a range some brk/mmap already
      zero-filled — [store_ok_zeros_hit], or [store_ok_zmem] for the
      single-grant spelling the examples actually carry;
    - .data/.bss: an address in a WRITABLE segment, where [wview] falls
      through to the segment image whatever the overlay holds.  The
      per-byte condition is decidable, and is exactly [StreamSim.wseg_ok],
      so an image settles its whole rw- window once by [vm_compute] and
      every store inside it costs two [lia]s — [store_ok_window].

    On top of that: anywhere the proof has ALREADY stored, or that a
    syscall wrote, the overlay only grows, so an earlier [store_ok]
    still holds — [store_ok_mono] and the [mem_grows] instances below.

    The monotonicity story is what keeps store proofs cheap: a store site
    deep in a long [wbytes]/[apply_zeros] chain proves its bound
    against the ORIGINAL memory and lifts it through the chain, instead
    of re-deriving it against a term that grows with every step.  It is
    also what a loop invariant carries when its memory is quantified
    existentially and there is no [wrap_mem] left to peel back to: the
    invariant says [mem_grows wmem mem] and registers the projection in
    [store_ok_db], which is where [solve_store_ok_inv] looks. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [StepTac] rather than just [PropExec]/[CatExec]: the dispatch tactic at
   the bottom reuses [u_norm], and every call site already loads it. *)
(* [StreamSim] for [wseg_ok], the decidable "this concrete range is in a
   writable segment and its bytes are present" check the images already use
   for read buffers — reused here for .data/.bss store targets. *)
(* [Footprint] for the [region]/[covers] vocabulary the buffer lemmas at
   the bottom re-use, so a binary's arena is named ONCE and both its
   stores and its read buffers are discharged against the same region. *)
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.AS Require Import PropExec CatExec StepTac StreamSim AllocSim Footprint.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Overlay growth

    [store_ok] only ever asks whether a byte is DEFINED, so the
    relevant order on overlays is definedness, not equality: writing
    bytes, or zero-filling a grant, can only add. *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(** [wview]'s segment fallback does not depend on the overlay, so a
    byte that was writable stays writable however the overlay grows:
    if the overlay had it, the larger one does; if it did not, both
    fall through to the same segment. *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
  mem_grows m m' ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(** *** The overlay operations grow it *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(** ** Ranges

    The workhorse: a range every byte of which the overlay already
    defines.  Stated over [wview] so the segment fallback counts too
    (a store into .data needs no overlay entry). *)
Lemma store_ok_of_all : forall segs n m a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      wview segs m x <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* The successor address is only ever needed when bytes remain: on the
     LAST byte [a + 1] may wrap (a one-byte store at the top of the
     address space is legal), and the recursion stops before using it. *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(** ** The stack window

    [PropExec.wrap_mem] is the proof-side mirror of the initial
    overlay: Linux's entry block from [sp] up to the stack VMA's end
    [StackLayout.ed_top], then [Some 0] everywhere in
    [[Run.stack_window_lo], sp), what the RLIMIT_STACK window and the
    guard gap above the mmap base leave below [sp].  A store wholly
    inside that window is therefore always in bounds -- which is the
    point of the window, and the reason [store_ok] does not need [sp]
    threaded into [step]. *)
Lemma wrap_mem_window_defined :
  forall inp mbase ph entry sp (x : word) draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem inp mbase ph entry sp draw x <> None.
Proof.
  intros inp mbase ph entry sp x draw Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) x)
    as [b|]; [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window :
  forall segs inp mbase ph entry sp a n draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp a n draw Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem inp mbase ph entry sp draw x) as [b|] eqn:Hw;
    [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(** How low the window reaches for ANY admissible launch, counted from
    [sp].  Linux counts RLIMIT_STACK from the stack VMA's end
    [StackLayout.ed_top] (mm/vma.c, [expand_downwards], Linux v6.18.46,
    commit ), so what is left below [sp] is the 8 MiB less
    the block between [sp] and that end.  [stack_window_reach] is an
    upper bound on that block plus the head room the other floor -- the
    guard gap above the mmap base -- costs; [stack_window_lo_valid]
    proves both floors stay under [sp - stack_window_depth]. *)
Definition stack_window_reach : Z := 2244095.

(** What is left of the 8 MiB below [sp] for every admissible launch:
    [stack_max_size - stack_window_reach] = 6144513 bytes. *)
Definition stack_window_depth : Z := stack_max_size - stack_window_reach.

Lemma stack_window_depth_val : stack_window_depth = 6144513.
Proof. vm_compute. reflexivity. Qed.

(** [mmap_base] page-aligns what it returns, and every number it
    subtracts from [STACK_TOP] is already a multiple of the page size,
    so [PAGE_ALIGN] is the identity there and the base is EXACTLY
    [STACK_TOP - gap - rnd].  The lossy "within a page" bound is not
    enough: the whole margin the guard-gap floor leaves is smaller than
    a page in the un-randomized mode. *)
Lemma page_round_up_Z_aligned : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

(** [mmap_base]'s gap under Sv48: the MAX_GAP clamp is dead, because
    SCOPE.md caps [stack_guard_gap] at 0x4aba6a2ab000 bytes
    ([State.stack_guard_gap_bytes_bounds]) and [STACK_TOP / 6 * 5] is
    117281240296105.  What is left is the kernel's own
    [gap = RLIMIT_STACK + stack_guard_gap (+ STACK_RND_MASK << PAGE_SHIFT)],
    floored at MIN_GAP (mm/util.c, [mmap_base], Linux v6.18.46, commit
    ). *)
Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  (* the kernel's own overflow guard [gap + pad > gap] first: [pad] is
     never negative, so it decides the branch and the remaining tests
     are between a closed form and literals *)
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

(** The window never reaches below [sp - stack_max_size], the
    image-independent line [MemSplit.win_lo] splits the overlay at:
    RLIMIT_STACK is counted from [ed_top], which is at or above [sp]. *)
Lemma stack_window_lo_ge_sp : forall inp (sp brk0 mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (bv_unsigned sp - stack_max_size
   <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk0 mbase draw (_ & Hsp & _).
  pose proof (launch_sp_le_top inp (ed_top draw) sp Hsp).
  unfold stack_window_lo.
  apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z;
    [lia | apply Z.le_max_l].
Qed.

(** The other floor of the window: the guard gap above the mmap base.
    [mmap_base] (mm/util.c, Linux v6.18.46, commit ) puts
    the base at [STACK_TOP - gap - rnd] with [gap] at least
    [RLIMIT_STACK + stack_guard_gap] -- and, under PF_RANDOMIZE, at
    least [STACK_RND_MASK << PAGE_SHIFT] more -- so the base PLUS its
    guard gap is at least that much below STACK_TOP.  The MAX_GAP clamp
    cannot fire under Sv48: SCOPE.md caps [stack_guard_gap] at
    0x4aba6a2ab000 bytes ([State.stack_guard_gap_bytes_bounds]), well
    under [STACK_TOP / 6 * 5]. *)
Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_aligned
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

(** Both floors are below [sp - stack_window_depth] for every launch
    the fifth conjunct of [Run.valid_entry_va] admits.  With
    randomization the base and its gap are at most
    [STACK_TOP - 0x407ff000] while [ed_top] is at least
    [STACK_TOP - 2^30]; without it they are at most
    [STACK_TOP - 8 MiB] while [ed_top] is at least
    [STACK_TOP - 4096].  [launch_top_minus_sp] turns the [ed_top]
    bound into one on [sp]. *)
Lemma stack_window_lo_valid : forall inp (sp brk0 mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  stack_window_lo (in_kernel inp) mbase draw
  <= bv_unsigned sp + stack_window_reach - stack_max_size.
Proof.
  intros inp sp brk0 mbase draw Hlaunch (Htop & Hsp & Hbase).
  pose proof (launch_top_minus_sp inp (ed_top draw) sp Hlaunch Hsp) as Hd.
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  destruct Htop as (_ & Hhi & Hlo).
  unfold stack_window_lo, stack_window_reach, stack_max_size,
    va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.

(** The window in the form a [lia] closes: an address [a] with
    [sp + stack_window_reach - stack_max_size <= a] is in it for every
    admissible launch. *)
Lemma store_ok_wrap_window_valid :
  forall segs inp mbase ph entry (sp brk0 : word) a n draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  bv_unsigned sp + stack_window_reach - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp brk0 a n draw Hvl Hlau Hlo Hhi.
  apply store_ok_wrap_window; [|exact Hhi].
  pose proof (stack_window_lo_valid inp sp brk0 mbase draw Hvl Hlau). lia.
Qed.

(** ** Grants

    A store into a range brk or mmap already zero-filled.  [apply_zeros]
    maps every covered address, so the side condition is exactly
    [zeros_cover] on each byte -- and the caller usually has the grant
    bounds in hand already. *)
Lemma store_ok_zeros_hit : forall segs m zs a n,
  zs <> [] ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      zeros_cover zs x = true) ->
  store_ok segs (apply_zeros m zs) a n = true.
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(** [AllocSim.zmem] is the single-grant spelling of [apply_zeros] the
    brk/mmap examples carry, and the one their store sites actually
    face.  Same fact, without the [zeros_cover] bookkeeping. *)
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
  store_ok segs (zmem m b l) a n = true.
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.

(** The copy-loop lemmas take the memory they write into ABSTRACTLY (a
    read hypothesis), so they cannot appeal to
    [store_ok_zmem] themselves.  [store_grant_ok segs m b l] is the hypothesis
    they carry instead: the whole grant is writable in [m].  One
    hypothesis at the top covers every iteration, since the loop's own
    stores are peeled off ([store_ok_peel]) before it is applied — or
    lifted through with [store_grant_mono] where that is more
    convenient. *)
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
                    (b l : word) : Prop :=
  forall (a : word) (n : nat),
    bv_unsigned b <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
    store_ok segs m a n = true.

Lemma store_grant_zmem : forall segs m b l,
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  store_grant_ok segs (zmem m b l) b l.
Proof.
  intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.

(** A page-rounded physical grant is also a writable grant for any logical
    prefix at the same base.  [brk] accounts for the prefix in its live-byte
    budget while the kernel maps the enclosing pages. *)
Lemma store_grant_zmem_prefix : forall segs m b logical physical,
  (bv_unsigned logical <= bv_unsigned physical)%Z ->
  (bv_unsigned b + bv_unsigned physical <= 2 ^ 64)%Z ->
  store_grant_ok segs (zmem m b physical) b logical.
Proof.
  intros segs m b logical physical Hle Hnw a n Hlo Hhi.
  apply store_ok_zmem; lia.
Qed.

Lemma store_grant_mono : forall segs m m' b l,
  mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
  intros segs m m' b l Hg H a n Hlo Hhi.
  eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.

(** ** Writable segments

    A store into .data/.bss needs no overlay entry at all: [wview]
    falls through to the segment.  Stated per byte so the caller can
    reuse whatever segment-bound facts it already [vm_compute]d. *)
Lemma store_ok_seg_writable : forall segs m a n,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      exists seg,
        find_segment segs (bv_unsigned x) 1 = Some seg /\
        seg_writable seg = true /\
        segment_byte_at (seg_bytes seg)
                    (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg))) <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs m a n Hnw Hall.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview.
  destruct (m x) as [b|]; [discriminate|].
  destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
  rewrite Hfind, Hw. exact Hb.
Qed.

(** *** …decided once per image, for a whole window

    [store_ok_seg_writable] is stated per byte, which is awkward for a
    SYMBOLIC target such as [buf + i]: [find_segment] cannot be
    computed on an open address.  [StreamSim.wseg_ok] decides exactly
    the same per-byte condition on a CONCRETE range, so an image proves
    its writable window good once by [vm_compute] and every store site
    inside it becomes two [lia]s.  Nothing here mentions the overlay:
    the segment fallback is what carries the window, so the fact holds
    for every memory the proof ever reaches. *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(** The converse of [store_ok_of_all]: a good range is good byte by
    byte.  Only used to cut a window down to one of its sub-ranges
    ([store_ok_sub]), which is what a store site actually needs. *)
Lemma store_ok_all : forall segs m n a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m a n = true ->
  forall x : word,
    bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    wview segs m x <> None.
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [x] is past [a], so at least one byte remains and [a + 1] cannot
     wrap — the only address at which it could is the last one. *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [exact H] is what picks the successor address for the IH; the two
     arithmetic goals are then closed against [Hu1]. *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
  bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m lo N = true ->
  bv_unsigned lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(** The per-image workhorse.  [base]/[hi] are the window's bounds as [Z]
    NUMERALS, tied to the [word] base and the [nat] length by two
    conversions: [lia] is no good at [Z.of_nat] of a large decimal
    literal (it stays an [of_num_uint] atom), and every call site would
    otherwise have to work around that.  So the shape is: two
    [vm_compute]s for the numerals, the [vm_compute]d window fact, and
    the caller's two [Z] bounds. *)
Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
  bv_unsigned lo = base ->
  base + Z.of_nat N = hi ->
  hi <= 2 ^ 64 ->
  wseg_ok segs lo N = true ->
  base <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= hi ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* ######################################################################### *)
(* The KERNEL side of the same view: a read(2) buffer                        *)
(* ######################################################################### *)

(** ** [store_ok] discharges a read BUFFER's writability too

    [read(2)] into a buffer raises the obligation

      read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w

    ("the kernel may copy [cnt] bytes to [buf]", the copy_to_user /
    EFAULT gate).  [StreamSim.wseg_ok], a decidable predicate over the
    STATIC segment image, settles a buffer in .data/.bss by [vm_compute]
    but says nothing at all about a buffer in memory the process obtained
    from [mmap] or [brk], where the segment image has no bytes and the
    whole grant lives in the overlay.  That is the [DrainAlg.Hread]
    obligation for every arena-based drain loop.

    No new theory is needed, because it is the SAME view: [store_ok] is
    "every byte of this range is defined in [wview]" and
    [read_bytes_map] over [ms_writable_byte] is "every byte of this
    range is defined in [wview]", and both recurse on [a + 1] in
    lockstep.  So the bridge below is an eight-line induction, and it
    hands the buffer obligation the ENTIRE store-side toolbox above:
    [store_ok_zmem] / [store_grant_ok] for a grant, [store_ok_window]
    for .data/.bss, [store_ok_wrap_window] for the stack, and
    [store_ok_mono] / [store_ok_peel] to lift any of them through the
    stores the loop has already performed.  In particular a per-binary
    proof discharges a read buffer with the very tactic it already uses
    for stores, [solve_store_ok].

    Note what is NOT required: no no-wrap side condition.  [store_ok]
    stops before dereferencing the successor of its last byte, exactly
    as [read_bytes_aux] does, so a one-byte buffer at the top of the
    address space is fine on both sides. *)
Lemma store_ok_read_aux : forall segs m n (a : word),
  store_ok segs m a n = true ->
  exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

Lemma store_ok_wbuf : forall segs ms (buf cnt : word),
  store_ok segs (ms_mem ms) buf (word_to_nat cnt) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms buf cnt H.
  rewrite read_bytes_map_eq. unfold ms_writable_byte.
  apply store_ok_read_aux. exact H.
Qed.

(** The [word_to_nat]/[bv_unsigned] conversion the two sides differ by:
    the buffer LENGTH arrives as a [word] (it is a register), and every
    bound a caller has about it is in [Z]. *)
Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

(** ** The grant case, which is the one that was missing

    A buffer inside an [mmap]/[brk] grant, stated against the
    [store_grant_ok] invariant a loop already carries: the whole grant
    is writable, so every sub-range of it is, so every read INTO it is
    admissible.  The two premises are pure [Z] arithmetic — [lia]-level
    effort at the call site, which is the point. *)
Lemma store_grant_wbuf : forall segs ms (b l buf cnt : word),
  store_grant_ok segs (ms_mem ms) b l ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt Hg Hlo Hhi.
  apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.

(** The same in [Common/Footprint]'s vocabulary, so a binary that has
    already named its arena [heap_rg base cur] discharges a read buffer
    by exhibiting [covers] — the identical obligation its stores raise,
    and monotone in the bump pointer through [heap_rg_bump]. *)
Lemma heap_rg_wbuf : forall segs ms (b l buf cnt : word) (cur : Z),
  store_grant_ok segs (ms_mem ms) b l ->
  cur <= bv_unsigned b + bv_unsigned l - bv_unsigned b ->
  covers (heap_rg b cur) buf (word_to_nat cnt) ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms b l buf cnt cur Hg Hcur Hc.
  destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
  rewrite of_nat_word_to_nat in Hhi.
  eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.

(** A grant straight out of the [mmap]/[brk] step, before any store has
    been layered on: [zmem m b l] is the model's zero-filled overlay
    ([Run.apply_zeros] at one range, [MmapSim.zfill]).  With
    [store_ok_mono]/[store_grant_mono] this is what a loop invariant's
    [store_grant_ok] conjunct is INITIALIZED from. *)
Lemma zmem_wbuf : forall segs ms m (b l buf cnt : word),
  mem_grows (zmem m b l) (ms_mem ms) ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
  eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
  eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.

(** Worked example / regression, in exactly the shape [DrainAlg]'s
    [Hread] hypothesis asks for: a drain loop that has already written
    into its arena still has a writable read buffer there, because the
    stores only GREW the overlay.  Two peels and three [lia]-level
    facts, and — the point — no [vm_compute] anywhere, which is what
    [StreamSim.wseg_ok] could only offer over a static segment. *)
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
  ms_mem ms = wbytes (zmem m b l) a bs ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
  eapply zmem_wbuf;
    [ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.

(** ** Dispatch

    The tactic every store site calls.  It peels the overlay
    chain back to something with a known shape and closes the bound
    there; [lia] finishes the address arithmetic. *)
Ltac store_ok_peel :=
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [stack_max_size] and [stack_window_reach] have to be unfolded: they
   are atoms to [lia].  A stack store needs the launch's
   [Run.valid_launch] and [Run.entry_launch_ok_va] in context, which
   together place the window's floor below [sp - stack_window_depth]
   ([store_ok_wrap_window_valid]). *)
Ltac store_ok_base :=
  first
    [ eapply store_ok_wrap_window_valid;
      [ eassumption | eassumption
      | unfold stack_window_reach, stack_max_size; u_norm; lia
      | u_norm; lia ]
    | eapply store_ok_zeros_hit;
      [ discriminate | u_norm; lia | intros; u_norm; lia ]
    | apply store_ok_zmem; u_norm; lia ].

(* [zmem] is NOT part of [store_ok_peel]: a store into the grant is
   discharged AT the [zmem] layer ([store_ok_zmem], in [store_ok_base]),
   so peeling past it would lose the only fact that closes it.  A store
   that is NOT in the grant — a stack slot, with a grant sitting on top
   of the memory — falls through to the second branch, which strips the
   [zmem] and keeps going. *)
Ltac solve_store_ok :=
  store_ok_peel;
  first [ store_ok_base
        | eapply store_ok_mono; [apply zmem_grows|];
          store_ok_peel; store_ok_base ].

(** Loop invariants quantify their memory EXISTENTIALLY ("some [mem]
    agreeing with [fmem] outside the scratch window"), so a stack store
    inside such a loop has no [wrap_mem] to peel back to.  The
    invariant carries [mem_grows wmem mem] instead — the overlay only
    ever grows — and the bound is lifted through it. *)
(* The [mem_grows] fact is usually bundled into the example's memory
   invariant ([bg_ok mem], [mem_ok mem], ...), so the dispatcher cannot
   name it.  Each example registers its own projection here instead. *)
Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
  first [ solve_store_ok
        | store_ok_peel;
          eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

(** Re-establishing that conjunct after a step: the memory is the
    invariant's own (or the initial one) with writes on top. *)
Ltac solve_mem_grows :=
  repeat first
    [ solve [ eauto with store_ok_db ]
    | apply mem_grows_refl
    | eapply mem_grows_trans; [ | apply wbytes_grows ]
    | eapply mem_grows_trans; [ | apply zmem_grows ]
    | eapply mem_grows_trans; [ | apply write_to_mem_grows ]
    | eapply mem_grows_trans; [ | apply apply_zeros_grows ]
    | eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
