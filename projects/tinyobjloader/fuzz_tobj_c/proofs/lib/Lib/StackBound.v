(* SPDX-License-Identifier: MIT *)
(* The model's own bound on the initial stack image, copied because this build does not carry the
   model's [Common] library.  Statements and proofs verbatim from
   rocq-linux-process-semantics@b84e73ef (the same text at 727298f3, except that b84e73ef gave
   [launch_auxv] the entry's stack pointer):
     theories/Common/PropExec.v:2506-2508  [la_rseq_launch_auxv]
     theories/Common/PropExec.v:2534-2554  [length_entry_stack_image_launch]
     theories/Common/StepTac.v:1124-1133   [block_head_size_le]
     theories/Common/StepTac.v:1162-1176   [launch_top_minus_sp]
     theories/Common/StepTac.v:1192-1202   [bsb_bound]
     theories/Common/StepTac.v:1138-1152   [launch_sp_le_top]
     theories/Common/StoreOk.v:209-374     [stack_window_reach] .. [stack_window_lo_valid]
   Nothing here is proved by hand that the model does not already prove. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
Import ListNotations.
Open Scope bv_scope.

Lemma la_rseq_launch_auxv : forall inp sp mbase,
  la_rseq (launch_auxv inp sp mbase) = kb_rseq (in_kernel inp).
Proof. reflexivity. Qed.

Lemma length_entry_stack_image_launch :
  forall v inp mbase ph entry (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
  = (bv_unsigned (ed_top draw) - bv_unsigned sp)%Z.
Proof.
  intros v inp mbase ph entry sp brk draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as (_ & (_ & _ & Hhi) & _).
  unfold entry_stack_image.
  rewrite length_build_stack_bytes, la_rseq_launch_auxv.
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp)))
    16 ltac:(lia)) as Hm.
  unfold block_pad_len.
  rewrite !Nat2Z.inj_add.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma block_head_size_le : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp)
   <= 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  pose proof (Nat.mod_upper_bound
                (length argv + length envp + 3) 2 ltac:(lia)).
  destruct rseq; lia.
Qed.

Lemma launch_top_minus_sp : forall inp (top sp : word),
  valid_launch inp ->
  valid_launch_sp top inp sp ->
  (bv_unsigned top - bv_unsigned sp <= 2101782)%Z.
Proof.
  intros inp top sp [_ Hb] [_ [Hlo _]].
  unfold launch_bytes, e2big_limit in Hb.
  unfold launch_sp_lo, align_down16 in Hlo.
  pose proof (block_head_size_le (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))
     - 4095) 16 ltac:(lia)).
  lia.
Qed.

Lemma bsb_bound : forall v inp mbase ph entry (sp brk : word) draw,
  valid_launch inp ->
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
   <= 2101782)%Z.
Proof.
  intros v inp mbase ph entry sp brk draw Hvl Hlau.
  rewrite (length_entry_stack_image_launch v inp mbase ph entry sp brk draw
             Hlau).
  destruct Hlau as (_ & Hsp & _).
  exact (launch_top_minus_sp inp (ed_top draw) sp Hvl Hsp).
Qed.

Section Window.
Local Open Scope Z_scope.

Lemma launch_sp_le_top : forall inp (top sp : word),
  valid_launch_sp top inp sp ->
  (bv_unsigned sp <= bv_unsigned top)%Z.
Proof.
  intros inp top sp [_ [_ Hhi]].
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

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
    1f99e9ab748f). *)
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
    [mmap_base] (mm/util.c, Linux v6.18.46, commit 1f99e9ab748f) puts
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

End Window.
