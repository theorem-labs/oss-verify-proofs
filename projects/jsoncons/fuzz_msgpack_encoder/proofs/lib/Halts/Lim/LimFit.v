(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimFit.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim and nothing else. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the fit lemmas follow the model's Linux placement (linux_place, through the lemma place_top) and the MAP_FIXED overflow arm in mmap_fit, brk's shrink cut (brk_unmap_cut) and page-range grow arm in brk_fit, munmap's cut (maps_subtract) in both model-changing arms of munmap_fit, and mremap's TASK_SIZE gate, room gate and cut in mremap_fit, with comments on these changes; fits_map_remove, which nothing here uses, is removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import BudgetPremise.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim Require Import LimBase LimMm LimMmap LimSpec LimMove LimFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fits (l : list (word * word)) : Prop :=
  forall (a sz : word), In (a, sz) l -> (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.

Lemma fits_nil : fits [].
Proof. intros a sz []. Qed.
Lemma fits_cons : forall (a n : word) l, (bv_unsigned a + bv_unsigned n <= two_pow_64)%Z -> fits l -> fits ((a, n) :: l).
Proof. intros a n l H Hl b s [E|Hin]; [inversion E; subst; exact H | exact (Hl b s Hin)]. Qed.
Lemma fits_app : forall l1 l2, fits l1 -> fits l2 -> fits (l1 ++ l2).
Proof. intros l1 l2 H1 H2 a sz Hin. apply in_app_or in Hin as [H|H]; [exact (H1 _ _ H) | exact (H2 _ _ H)]. Qed.
Lemma fits_maps_subtract : forall l lo hi, fits l -> fits (maps_subtract l lo hi).
Proof.
  intros l lo hi H b s Hin.
  destruct (maps_subtract_In l lo hi b s Hin) as (a & sz & Hin0 & Hiv).
  pose proof (H a sz Hin0) as Hf.
  pose proof (iv_subtract_within a sz lo hi b s Hf Hiv). lia.
Qed.

Lemma Z_to_bv_le : forall z, (0 <= z)%Z -> (bv_unsigned (Z_to_bv 64 z) <= z)%Z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  apply Z.mod_le; [exact Hz | reflexivity].
Qed.
Lemma round_nonneg : forall w : word, (0 <= page_round_up_Z (bv_unsigned w))%Z.
Proof. intros w. apply page_round_up_Z_nonneg. exact (proj1 (mremap_word_range w)). Qed.

(** [mmap_fit]'s arms carry the placement as [Mmap.linux_place], and the bound
    those arms need is its THIRD admissible conjunct: [Placement.linux_place_admissible]
    ([c0dd863a:theories/LinuxProcessSem/Checks/Placement.v:801-806]) gives [a + nZ <= alloc_top h] from
    [0 < nZ] and [nZ mod page_size = 0].  Both witnesses are the model's own --
    [Syscall.w_is0_false_pos] turns the arm's own [w_is0 len = false] gate into
    [0 < bv_unsigned len], [State.page_round_up_Z_pos] lifts it to the rounded
    length, and [Placement.page_round_up_Z_aligned] is unconditional.

    A NAMED lemma rather than a [match] inside [mmap_fit]: it can be read, it is
    a control whose failure breaks the build at its own line instead of inside a
    tactic block, and it keeps every one of these names out of term position. *)
Lemma place_top : forall h thp hint (len : word) a,
  w_is0 len = false ->
  linux_place h thp hint (page_round_up_Z (bv_unsigned len)) a ->
  (a + page_round_up_Z (bv_unsigned len) <= alloc_top h)%Z.
Proof.
  intros h thp hint len a Hz Hpl.
  pose proof (page_round_up_Z_pos (bv_unsigned len) (w_is0_false_pos len Hz)) as HP.
  (* [Placement.] on both: [linux_place] resolves bare in the statement above but
     [page_round_up_Z_aligned] and [linux_place_admissible] do not, so the module
     is loaded and not imported.  A bare name that resolves says nothing about its
     neighbours in the same module. *)
  pose proof (Placement.page_round_up_Z_aligned (bv_unsigned len)) as HA.
  assert (HPos : (0 < page_round_up_Z (bv_unsigned len))%Z)
    by (unfold page_size in HP; lia).
  exact (proj1 (proj2 (proj2 (Placement.linux_place_admissible h thp hint _ a HPos HA Hpl)))).
Qed.

(* [comment removed for export] *)
Lemma grant_fits : forall (h : VmMaps) (a : word) (nZ : Z),
  (0 <= nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z ->
  (bv_unsigned a + bv_unsigned (Z_to_bv 64 nZ) <= two_pow_64)%Z.
Proof.
  intros h a nZ H0 H. pose proof (alloc_top_lt h). pose proof (Z_to_bv_le nZ H0). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sys_post {A} (c : Sys A) (i : SyscallInput) (m : Model) (Q : Model -> Prop) : Prop :=
  forall x m' evs, c i m (Ok x m' evs) -> Q m'.

Lemma post_pure {A} (x : A) i m (Q : Model -> Prop) : Q m -> sys_post (pure x) i m Q.
Proof. intros H y m' evs E. hnf in E. injection E as _ <- _. exact H. Qed.
Lemma post_unmodeled {A} i m (Q : Model -> Prop) : sys_post (@unmodeled A) i m Q.
Proof. intros y m' evs E. discriminate E. Qed.
Lemma post_alt {A} (c1 c2 : Sys A) i m Q : sys_post c1 i m Q -> sys_post c2 i m Q -> sys_post (alt c1 c2) i m Q.
Proof. intros H1 H2 y m' evs [E|E]; [exact (H1 _ _ _ E) | exact (H2 _ _ _ E)]. Qed.
Lemma post_bind {A B} (c : Sys A) (k : A -> Sys B) i m Q :
  (forall x m1 evs, c i m (Ok x m1 evs) -> sys_post (k x) i m1 Q) -> sys_post (bind c k) i m Q.
Proof. intros H y m' evs (x & m1 & evs1 & evs2 & H1 & H2 & _). exact (H x m1 evs1 H1 y m' evs2 H2). Qed.
Lemma post_get_model {A} (k : Model -> Sys A) i m Q : sys_post (k m) i m Q -> sys_post (bind get_model k) i m Q.
Proof. intros H y m' evs E. apply bind_get_model in E. exact (H _ _ _ E). Qed.
Lemma post_get_vmmaps {A} (k : VmMaps -> Sys A) i m Q : sys_post (k (m_vmmaps m)) i m Q -> sys_post (bind get_vmmaps k) i m Q.
Proof. intros H y m' evs E. apply bind_get_vmmaps in E. exact (H _ _ _ E). Qed.

Ltac post_step :=
  cbv beta zeta;
  lazymatch goal with
  | |- sys_post (if ?b then _ else _) _ _ _ => let E := fresh "E" in destruct b eqn:E
  | |- sys_post (alt _ _) _ _ _ => apply post_alt
  | |- sys_post (bind get_model _) _ _ _ => apply post_get_model
  | |- sys_post (bind get_vmmaps _) _ _ _ => apply post_get_vmmaps
  | |- sys_post (bind (errno_from _) _) _ _ _ =>
        let Hc := fresh "Hc" in let m1 := fresh "m1" in let ev := fresh "ev" in
        apply post_bind; intros ? m1 ev Hc; apply errno_from_inv in Hc; destruct Hc as (_ & Hc & _); subst m1
  | |- sys_post (bind (choose _) _) _ _ _ =>
        let Hc := fresh "Hc" in let Hp := fresh "Hp" in let m1 := fresh "m1" in let ev := fresh "ev" in
        apply post_bind; intros ? m1 ev Hc; apply choose_inv in Hc; destruct Hc as (Hp & Hc & _); subst m1
  | |- sys_post (bind (modify _) _) _ _ _ =>
        let Hc := fresh "Hc" in let m1 := fresh "m1" in let ev := fresh "ev" in
        apply post_bind; intros ? m1 ev Hc; apply modify_inv in Hc; destruct Hc as (Hc & _); subst m1
  | |- sys_post (bind (set_vmmaps _) _) _ _ _ => unfold set_vmmaps
  | |- sys_post (bind (forget_vm_range _ _) _) _ _ _ => unfold forget_vm_range
  | |- sys_post unmodeled _ _ _ => apply post_unmodeled
  | |- sys_post (pure _) _ _ _ => apply post_pure
  | |- sys_post (err_ret _) _ _ _ => apply post_pure
  | |- sys_post (ret_only _) _ _ _ => apply post_pure
  end.
Ltac post_auto := repeat post_step.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. intros rs. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing : forall flags a n m, m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma m_vmmaps_with_mmap_replacement : forall flags a n m, m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brk_fit : forall i m req,
  vm_fit (m_vmmaps m) -> sys_post (brk_spec req) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m req Hf. unfold brk_spec. post_auto.
  unfold with_brk_next. cbv zeta. rewrite m_vmmaps_forget_vm_ranges.
  change (vm_fit (brk_model_next (m_vmmaps m) req x)).
  unfold vm_fit, brk_model_next. cbn [vm_maps]. fold (fits (brk_maps_next (m_vmmaps m) req x)).
  unfold brk_maps_next.
  destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m)))%Z && (bv_unsigned x <? bv_unsigned (vm_brk (m_vmmaps m)))%Z).
  - (* brk's SHRINK arm cuts through [Mmap.brk_unmap_cut]
       ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mmap.v:430-435]), not a bare
       [maps_subtract], so [apply fits_maps_subtract] does not match the head.  This arm
       follows the model's own proof of the same obligation, the shrink arm of
       [brk_model_next_fit] ([c0dd863a:theories/LinuxProcessSem/Checks/MapsFit.v:129-132]).
       Differences from the source, and nothing else: this tree's lemma is named
       [fits_maps_subtract] where the model's is [maps_subtract_fit]; [x] here is the model's
       [r]; and [m_vmmaps m] here is the model's [h]. *)
    unfold brk_unmap_cut. cbv zeta.
    destruct (page_round_up_Z (bv_unsigned x)
              <? page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))%Z;
      [apply fits_maps_subtract; exact Hf | exact Hf].
  - apply fits_app; [| exact Hf].
    unfold brk_grants. destruct (brk_is_grow req x (vm_brk (m_vmmaps m))) eqn:Eg; [| apply fits_nil].
    (* brk's GROW arm is a PAGE RANGE: [brk_grants] is
       [brk_page_range (page_round_up_Z (bv_unsigned old)) (page_round_up_Z (bv_unsigned r))]
       -- the very shape skcms proves for itself at Asan/AllocSim.v:374 [brk_grants_grow] --
       so [apply fits_cons] does not match the head until [brk_page_range] is unfolded.
       This arm follows the model's proof of the same obligation, the grow arm of
       [brk_model_next_fit] ([c0dd863a:theories/LinuxProcessSem/Checks/MapsFit.v:133-166]).
       Differences from the source, and nothing else: [fits_nil]/[fits_cons]/[fits_app] for
       the model's [maps_fit_*]; this tree's [fits_cons] takes the arithmetic bound FIRST
       and the model's takes it second, so that bracket is flipped; [x] is the model's [r]
       and [m_vmmaps m] its [h]; and [mremap_word_range] is this tree's name for [word_range]. *)
    unfold brk_page_range.
    destruct (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))
              <? page_round_up_Z (bv_unsigned x))%Z eqn:Elh; [| apply fits_nil].
    apply Z.ltb_lt in Elh.
    apply fits_cons; [| apply fits_nil].
    pose proof (mremap_word_range x) as Hr.
    pose proof (mremap_word_range (vm_brk (m_vmmaps m))) as Hb.
    pose proof (page_round_up_Z_nonneg (bv_unsigned (vm_brk (m_vmmaps m))) ltac:(lia)).
    assert (Hhi : (page_round_up_Z (bv_unsigned x) <= two_pow_64)%Z).
    { (* [mremap_word_range] states its bound over [two_pow_64], so the [unfold] runs
         [in *]: unfolded in the goal alone, `lia` has `2 ^ 64` in the goal and
         `two_pow_64` in [Hr]/[Hb] and finds no witness. *)
      unfold page_round_up_Z, page_size, two_pow_64 in *.
      pose proof (Z.div_mod (bv_unsigned x + 4096 - 1) 4096 ltac:(lia)).
      pose proof (Z.mod_pos_bound (bv_unsigned x + 4096 - 1) 4096 ltac:(lia)).
      lia. }
    unfold two_pow_64 in *.
    assert (U : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z).
    { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with (2 ^ 64)%Z. lia. }
    rewrite (U (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))) by lia.
    destruct (Z.eq_dec (page_round_up_Z (bv_unsigned x)
                        - page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))) (2 ^ 64))
      as [He|He].
    + pose proof (bv_unsigned_in_range 64
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned x)
                     - page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))))) as Hsz.
      change (bv_modulus 64) with (2 ^ 64)%Z in Hsz. lia.
    + rewrite (U ((page_round_up_Z (bv_unsigned x)
                   - page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))%Z)) by lia.
      lia.
Qed.

(* [comment removed for export] *)
Lemma munmap_fit : forall i m addr len,
  vm_fit (m_vmmaps m) -> sys_post (munmap_spec addr len) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m addr len Hf. unfold munmap_spec. post_auto; try exact Hf.
  (* [munmap_spec]'s exact arm cuts through [mmap_fixed_destroyed_next]
     ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mmap.v:1679-1685]), whose [vm_maps] is
     [maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)],
     not [map_remove].  There is a bridge in this tree
     ([Asan/MmapSim.v:160] [maps_subtract_exact]), but it is NOT needed: [fits] does not care
     about the exact shape, only that every entry is in range, and [fits_maps_subtract] (:25)
     gives that with no side conditions at all.
     The PARTIAL arm ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mmap.v:2982-2988]) has the same shape: it modifies by
     [with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n)], whose [m_vmmaps] is
     that same [mmap_fixed_destroyed_next] by [m_vmmaps_with_mmap_destroyed] (:129,
     [reflexivity]).  So BOTH model-changing arms close by the same step, and [all:] takes
     them together. *)
  all: apply fits_maps_subtract; exact Hf.
Qed.

(* [comment removed for export] *)
Lemma mprotect_fit : forall i m addr len prot,
  vm_fit (m_vmmaps m) -> sys_post (mprotect_spec addr len prot) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m addr len prot Hf. unfold mprotect_spec. post_auto; exact Hf.
Qed.

(* [comment removed for export] *)
Lemma mremap_fit : forall i m old old_size new_size flags,
  vm_fit (m_vmmaps m) -> sys_post (mremap_spec old old_size new_size flags) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m old old_size new_size flags Hf. unfold mremap_spec.
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)%Z); [post_auto|].
  destruct (negb (bv_unsigned old mod page_size =? 0)%Z); [post_auto; exact Hf|].
  destruct (page_align_is0_b new_size) eqn:Hnew; [post_auto; exact Hf|].
  (* The gate between the two [page_align_is0_b] tests ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mremap.v:798-804]):
     a page-aligned new length over TASK_SIZE is -EINVAL before any VMA is looked up.
     It is an [err_ret] arm, so the model is unchanged and [Hf] carries.  It is
     destructed here, before the next line's [post_auto], so that [post_get_model]
     meets the branch it is written for. *)
  destruct ((TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z) eqn:Etask; [post_auto; exact Hf|].
  destruct (page_align_is0_b old_size) eqn:Hold; [post_auto|].
  apply post_get_model. cbv zeta.
  set (old_nZ := page_round_up_Z (bv_unsigned old_size)). set (new_nZ := page_round_up_Z (bv_unsigned new_size)).
  set (old_n := Z_to_bv 64 old_nZ). set (new_n := Z_to_bv 64 new_nZ).
  pose proof (round_nonneg new_size) as Hn0. fold new_nZ in Hn0.
  pose proof (round_nonneg old_size) as Ho0. fold old_nZ in Ho0.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  pose proof (Z_to_bv_le new_nZ Hn0) as Hnle. fold new_n in Hnle.
  pose proof (mremap_word_range old) as Hor.
  destruct (negb (mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)) eqn:Esrc; [post_auto|].
  apply negb_false_iff in Esrc. apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc _]. apply andb_true_iff in Esrc as [Esrc _]. apply andb_true_iff in Esrc as [Esrc _].
  apply Z.leb_le in Esrc.
  destruct (old_nZ =? new_nZ)%Z; [post_auto; exact Hf|].
  assert (G : forall dst, (bv_unsigned dst + new_nZ <= alloc_top (m_vmmaps m))%Z ->
                vm_fit (m_vmmaps (mremap_model_next m old old_n dst new_n))).
  { intros dst Hd.
    (* same move as [munmap_fit]: [mremap_maps_next]
       ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mremap.v:166-171]) is
       [(dst, new_n) :: maps_subtract (vm_maps h) ...], so [fits_cons] takes the head and
       [fits_maps_subtract] the tail. *)
    change (fits ((dst, new_n) :: maps_subtract (vm_maps (m_vmmaps m))
                    (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))).
    apply fits_cons; [lia | apply fits_maps_subtract; exact Hf]. }
  apply post_alt; [post_auto; exact Hf|].
  destruct (new_nZ <? old_nZ)%Z eqn:Elt.
  - apply Z.ltb_lt in Elt. post_auto. apply G. lia.
  - (* [mremap_inplace_grow_b] is [mremap_inplace_room_b && mremap_final_budget_b]
       ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mremap.v:320-334]), and the grow resolution is a PLAIN
       [if mremap_inplace_room_b …], not an [alt]; the budget is a [choose] inside the
       in-place arm.  The move arm's [choose] predicate is [mremap_dst_ok] ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mremap.v:463-467]), a
       Prop whose SECOND conjunct is [mremap_fresh_b … = true], so the move argument is
       behind a [proj2]. *)
    assert (MOVE : sys_post
              (dst <- choose (fun dst => mremap_dst_ok m old_nZ new_nZ old old_n dst new_n) ;;
               modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
               pure (mremap_move_effect old old_n dst old_nZ new_nZ)) i m (fun m' => vm_fit (m_vmmaps m'))).
    { post_auto. apply G.
      destruct Hp as [_ Hp].
      unfold mremap_fresh_b in Hp. cbv zeta in Hp.
      apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [_ Hp].
      apply Z.leb_le in Hp. exact Hp. }
    destruct (mremap_inplace_room_b m old old_n new_n old_nZ new_nZ) eqn:Eig; [| exact MOVE].
    post_auto. apply G.
    (* [mremap_inplace_room_b] is TWO conjuncts, so one [andb_true_iff] splits it. *)
    unfold mremap_inplace_room_b in Eig. cbv zeta in Eig.
    apply andb_true_iff in Eig as [Eig _].
    apply Z.leb_le in Eig. exact Eig.
Qed.

(* [comment removed for export] *)
Lemma vm_fit_with_vmmaps : forall h m, fits (vm_maps h) -> vm_fit (m_vmmaps (with_vmmaps h m)).
Proof. intros h m H. exact H. Qed.

Lemma mmap_fit : forall i m addr len prot flags fd off,
  vm_fit (m_vmmaps m) -> sys_post (mmap_spec addr len prot flags fd off) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m addr len prot flags fd off Hf. unfold mmap_spec.
  post_auto; try exact Hf.
  all: rewrite ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_replacement, ?m_vmmaps_with_mmap_destroyed.
  all: try exact Hf.
  all: try apply vm_fit_with_vmmaps.
  all: unfold mmap_fixed_rw_next, mmap_fixed_destroyed_next, mmap_fixed_rw_span_next, mmap_fixed_noaccess_span_next; cbn [vm_maps].
  all: try exact Hf.
  all: repeat first [apply fits_maps_subtract | exact Hf | apply fits_cons].
  all: try exact Hf.
  (* [mmap_fixed_overflow] ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mmap.v:1995-1998]) gives four of the
     twelve goals standing here: its [sys_post].  BOTH of its arms are [err_ret] or [ret_only],
     which leave the model alone, so [Hf] carries through each.
     It gets its OWN branch rather than a wider blanket on the line below:
     loosening [all: apply (grant_fits ...)] to tolerate this shape would make it
     match goals it was never written for.  [solve] keeps it honest -- it cannot
     half-apply, so a goal it does not close is left exactly as it was for the line
     below to fail on. *)
  all: try (solve
       [ unfold mmap_fixed_overflow;
         destruct (mmap_fixed_err_addr_b addr (page_round_up_Z (bv_unsigned len)));
         [ apply post_alt; (post_auto; exact Hf) | post_auto; exact Hf ] ]).
  all: apply (grant_fits (m_vmmaps m)); [apply round_nonneg|].
  (* Six of the eight goals standing here carry NEITHER hypothesis the [first]
     below looks for; what they carry instead is [linux_place].
     [solve] keeps this honest: a goal it does not close is left unchanged for the
     [first] to meet. *)
  all: try (solve
       [ match goal with
         | Hp : linux_place _ _ _ _ _ /\ _ |- _ => eapply place_top; [eassumption | exact (proj1 Hp)]
         | Hp : linux_place _ _ _ _ _ |- _ => eapply place_top; [eassumption | exact Hp]
         end ]).
  all: first
    [ match goal with Hp : _ /\ _ /\ (?z <= ?t)%Z /\ _ |- (?z <= ?t)%Z => exact (proj1 (proj2 (proj2 Hp))) end
    | repeat match goal with
             | Hp : ?x = ?y /\ _ |- _ => destruct Hp as [Hp _]
             | Hp : ?x = ?y |- _ => subst x
             end;
      match goal with E : negb (?z <=? ?t)%Z = false |- (?z <= ?t)%Z =>
        apply negb_false_iff in E; apply Z.leb_le in E; exact E end ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem syscall_spec_fit : forall i m eff m' evs,
  vm_fit (m_vmmaps m) -> syscall_spec i m (Ok eff m' evs) -> vm_fit (m_vmmaps m').
Proof.
  intros i m eff m' evs Hf H.
  destruct (wr_sysno (bv_unsigned (in_sysno i))) eqn:E.
  - unfold wr_sysno in E.
    repeat (apply orb_true_iff in E; destruct E as [E|E]); apply Z.eqb_eq in E.
    + apply (syscall_spec_214 _ _ _ E) in H. exact (brk_fit i m _ Hf _ _ _ H).
    + apply (syscall_spec_215 _ _ _ E) in H. exact (munmap_fit i m _ _ Hf _ _ _ H).
    + apply (syscall_spec_216 _ _ _ E) in H. exact (mremap_fit i m _ _ _ _ Hf _ _ _ H).
    + apply (syscall_spec_222 _ _ _ E) in H. exact (mmap_fit i m _ _ _ _ _ _ Hf _ _ _ H).
    + apply (syscall_spec_226 _ _ _ E) in H. exact (mprotect_fit i m _ _ _ Hf _ _ _ H).
  - rewrite (syscall_spec_frames_vm i m eff m' evs E H). exact Hf.
Qed.

Lemma materialize_fit : forall m acc m',
  vm_fit (m_vmmaps m) -> materialize_model_accesses m acc = Some m' -> vm_fit (m_vmmaps m').
Proof.
  intros m acc m' Hf H.
  destruct (materialize_model_accesses_frame m acc m' H) as (_ & Hv & _). rewrite Hv. exact Hf.
Qed.

Lemma init_model_fit : forall reserved brk0 mbase sp lim inp,
  vm_fit (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros. intros a sz []. Qed.
