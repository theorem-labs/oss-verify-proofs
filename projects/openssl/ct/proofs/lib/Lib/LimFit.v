(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the place_declined_b premise of the mmap decline; the freely placed mmap arms; the mmap get_model bind hoisted out of the alt). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import BudgetPremise.
(* Qualified, not imported: [Placement.linux_place_admissible] and the checks'
   [mmap_grant_len_ok] close the freely placed arms of [mmap_fit] below. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Mmap.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import LimBase LimMm LimMmap LimSpec LimMove LimFrame.
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
  (* THE MISSING ARM.  [mmap_fixed_overflow] is a Definition, so a goal
     [sys_post (mmap_fixed_overflow _ _) _ _ _] matches none of the cases above,
     the [lazymatch] fails, and [repeat post_step] simply STOPS — after which the
     next tactic meets a goal it cannot apply to and the error reads "Unable to
     unify … with SyscallEffect", as if an effect-valued hole had been left.
     Unfolding it HERE keeps the walk in one pass, so every branch it opens still
     gets its [eqn:] hypothesis from the [if] case above; unfolding it at the call
     site instead loses those facts and the closing tactic has no bound to use.
     This is the local twin of the model's own [Checks.VmMapsDisjoint.vm_step],
     which carries a general [context [if ?b then _ else _] => destruct b eqn:?]
     for exactly this reason (727298f3:1724-1740). *)
  | |- sys_post (mmap_fixed_overflow _ _) _ _ _ => unfold mmap_fixed_overflow
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
  - (* SHRINK: the cut is now page-granular and guarded ([brk_unmap_cut]) *)
    unfold brk_unmap_cut. cbv zeta.
    destruct (page_round_up_Z (bv_unsigned x)
              <? page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))%Z;
      [apply fits_maps_subtract; exact Hf | exact Hf].
  - apply fits_app; [| exact Hf].
    (* GROW: the grant ledger is now the PAGE range
       [[PAGE_ALIGN(old), PAGE_ALIGN(r))], not the logical [[old, r)]. *)
    unfold brk_grants. destruct (brk_is_grow req x (vm_brk (m_vmmaps m))); [| apply fits_nil].
    unfold brk_page_range.
    destruct (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))
              <? page_round_up_Z (bv_unsigned x))%Z eqn:Elh; [| apply fits_nil].
    apply Z.ltb_lt in Elh.
    apply fits_cons; [| apply fits_nil].
    pose proof (mremap_word_range x) as Hr.
    pose proof (mremap_word_range (vm_brk (m_vmmaps m))) as Hb.
    pose proof (page_round_up_Z_nonneg (bv_unsigned (vm_brk (m_vmmaps m))) (proj1 Hb)) as Hlo0.
    assert (Hhi : (page_round_up_Z (bv_unsigned x) <= two_pow_64)%Z).
    { unfold page_round_up_Z, page_size, two_pow_64 in *.
      pose proof (Z.div_mod (bv_unsigned x + 4096 - 1) 4096 ltac:(lia)).
      pose proof (Z.mod_pos_bound (bv_unsigned x + 4096 - 1) 4096 ltac:(lia)).
      lia. }
    assert (U : forall z, (0 <= z < two_pow_64)%Z -> bv_unsigned (Z_to_bv 64 z) = z).
    { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with two_pow_64. exact Hz. }
    rewrite (U (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))) by lia.
    destruct (Z.eq_dec (page_round_up_Z (bv_unsigned x)
                        - page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))) two_pow_64)
      as [He|He].
    + (* the one corner where the size would wrap: it needs the break's page
         at 0 and the resolution's at 2^64, and the wrapped size is still
         under the bound *)
      pose proof (mremap_word_range
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned x)
                     - page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))))).
      lia.
    + rewrite (U ((page_round_up_Z (bv_unsigned x)
                   - page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))%Z)) by lia.
      lia.
Qed.

(* [comment removed for export] *)
Lemma munmap_fit : forall i m addr len,
  vm_fit (m_vmmaps m) -> sys_post (munmap_spec addr len) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m addr len Hf. unfold munmap_spec. post_auto; try exact Hf.
  (* LPS 75d69e00: the exact arm's ledger is [mmap_fixed_destroyed_next]
     (Sys/Mm/Mmap.v:1488) - the request RANGE cut out of [vm_maps] with
     [maps_subtract] - where f1006fe8's [munmap_spec] removed the whole entry
     based at [addr] with [map_remove], a name its Sys/Mm has no hit for at
     75d69e00 (control: [maps_subtract] fires 41 times in that same file).
     The new partial arm ([munmap_cut_ok], Mmap.v:2729) writes the SAME ledger
     through [with_mmap_destroyed], which delta-unfolds to the exact arm's
     [vm_forget_range lo hi (with_vmmaps ... m)] - that conversion is what
     [m_vmmaps_with_mmap_destroyed] above proves by [reflexivity] - so both
     residual goals are the same term and one [exact] closes both.
     The range is spelled out rather than left to unification because
     [post_step]'s [cbv beta zeta] has already expanded munmap_spec's [let]s,
     and an [exact] of a closed term needs only a conversion check. *)
  all: exact (fits_maps_subtract (vm_maps (m_vmmaps m))
                (bv_unsigned addr)
                (bv_unsigned addr
                 + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
                Hf).
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
  (* LPS 08b1429, carried into 75d69e00 (Sys/Mm/Mremap.v:799-805): a NEW gate sits
     between the two PAGE_ALIGN checks -- a page-aligned new length over TASK_SIZE is
     -EINVAL from [check_mremap_params] before any VMA is looked up.  Without it the
     arm fell through to [page_align_is0_b old_size], the goal was still the [if]
     rather than a [bind], and [post_get_model] below reported
     "Unable to unify Model with word".  Its answer is [err_ret EINVAL], the same
     shape as the gate above it, so it closes the same way.  ct's own Lib/LimSpec.v:376
     spells the premise in exactly this pre-[cbv zeta] form; Lib/LimMove.v:144 and
     Lib/LimMremap.v:42 spell it as [TASK_SIZE <? new_nZ] because both have already
     run [cbv zeta in *].  LimFit was the one file of the four left behind. *)
  destruct (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z; [post_auto; exact Hf|].
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
    (* LPS 75d69e00: [mremap_maps_next] (Sys/Mm/Mremap.v:166-171) gained an
       [old_n] argument and now cuts the source RANGE out of [vm_maps],
       [maps_subtract (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)],
       where f1006fe8's three-argument version removed the whole entry based at
       [old] ([map_remove]).  [Lib/LimMove.v:50-52] already reads it this way. *)
    change (fits ((dst, new_n) :: maps_subtract (vm_maps (m_vmmaps m))
                                    (bv_unsigned old)
                                    (bv_unsigned old + bv_unsigned old_n))).
    apply fits_cons; [lia | apply fits_maps_subtract; exact Hf]. }
  apply post_alt; [post_auto; exact Hf|].
  destruct (new_nZ <? old_nZ)%Z eqn:Elt.
  - apply Z.ltb_lt in Elt. post_auto. apply G. lia.
  - assert (MOVE : sys_post
              (dst <- choose (fun dst => mremap_dst_ok m old_nZ new_nZ old old_n dst new_n) ;;
               modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
               pure (mremap_move_effect old old_n dst old_nZ new_nZ)) i m (fun m' => vm_fit (m_vmmaps m'))).
    { post_auto. apply G.
      (* 75d69e00 Sys/Mm/Mremap.v:840 has [choose (fun dst => mremap_dst_ok ...)]; the
         revision WRAPPED the old predicate, which is now the SECOND conjunct of
         [mremap_dst_ok] (:463-467, [linux_place ... /\ mremap_fresh_b ... = true]).
         Only that conjunct is wanted here.  ct's own Lib/LimMove.v:190 peels it the
         same way, so the donor is in this tree and is self-consistent. *)
      destruct Hp as [_ Hp].
      unfold mremap_fresh_b in Hp. cbv zeta in Hp.
      apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [_ Hp].
      apply Z.leb_le in Hp. exact Hp. }
    (* The GROW arm's [if] is now on [mremap_inplace_room_b], not on
       [mremap_inplace_grow_b]: the model split room from the budget charge,
       because keeping them in one predicate made a failing charge look like
       missing room and offered a move Linux does not make
       (Sys/Mm/Mremap.v:320-334 and :833-843 at LPS 727298f3).  The in-place
       branch is now [choose] on [mremap_final_budget_b] rather than an [alt],
       so there is no [post_alt] to peel; and the bound this proof wants is
       [mremap_inplace_room_b]'s FIRST conjunct, which is the same
       [bv_unsigned old + new_nZ <=? alloc_top h] the old predicate led with. *)
    destruct (mremap_inplace_room_b m old old_n new_n old_nZ new_nZ) eqn:Eroom; [| exact MOVE].
    post_auto. apply G.
    unfold mremap_inplace_room_b in Eroom. cbv zeta in Eroom.
    apply andb_true_iff in Eroom as [Eroom _].
    apply Z.leb_le in Eroom. exact Eroom.
Qed.

(* [comment removed for export] *)
Lemma vm_fit_with_vmmaps : forall h m, fits (vm_maps h) -> vm_fit (m_vmmaps (with_vmmaps h m)).
Proof. intros h m H. exact H. Qed.

(* THE MAP_FIXED OVERFLOW ARM, CONTAINED.  [post_step]'s lazymatch has no case
   for [mmap_fixed_overflow], so [post_auto] STOPS there and the next tactic
   meets a goal it cannot apply to — which reads as "Unable to unify … with
   SyscallEffect", i.e. like an effect-valued hole.  It is not a hole, it is an
   unwalked [alt].  Unfolding it inside [mmap_fit] lets the walk continue but
   drags the arm's branches into the common tail, where the closing [first]
   meets bounds it has no hypothesis for.  So the unfold is contained HERE,
   where the only goals are the overflow arm's own and every one of them leaves
   the model untouched — the spec-side twin of the model's
   [Checks.Sys.Mm.Mmap.check_mmap_fixed_overflow_model] at 727298f3:590. *)
Lemma mmap_fixed_overflow_fit : forall i m addr nZ,
  vm_fit (m_vmmaps m) ->
  sys_post (mmap_fixed_overflow addr nZ) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m addr nZ Hf. unfold mmap_fixed_overflow.
  post_auto; try exact Hf.
Qed.

Lemma mmap_fit : forall i m addr len prot flags fd off,
  vm_fit (m_vmmaps m) -> sys_post (mmap_spec addr len prot flags fd off) i m (fun m' => vm_fit (m_vmmaps m')).
Proof.
  intros i m addr len prot flags fd off Hf. unfold mmap_spec.
  post_auto; try exact Hf.
  all: try (apply mmap_fixed_overflow_fit; exact Hf).
  all: rewrite ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_replacement, ?m_vmmaps_with_mmap_destroyed.
  all: try exact Hf.
  all: try apply vm_fit_with_vmmaps.
  all: unfold mmap_fixed_rw_next, mmap_fixed_destroyed_next, mmap_fixed_rw_span_next, mmap_fixed_noaccess_span_next; cbn [vm_maps].
  all: try exact Hf.
  all: repeat first [apply fits_maps_subtract | exact Hf | apply fits_cons].
  all: try exact Hf.
  all: apply (grant_fits (m_vmmaps m)); [apply round_nonneg|].
  all: first
    [ match goal with Hp : _ /\ _ /\ (?z <= ?t)%Z /\ _ |- (?z <= ?t)%Z => exact (proj1 (proj2 (proj2 Hp))) end
    | repeat match goal with
             | Hp : ?x = ?y /\ _ |- _ => destruct Hp as [Hp _]
             | Hp : ?x = ?y |- _ => subst x
             end;
      match goal with E : negb (?z <=? ?t)%Z = false |- (?z <= ?t)%Z =>
        apply negb_false_iff in E; apply Z.leb_le in E; exact E end
      (* LPS 727298f3: the two freely placed arms [choose] their address by
         [linux_place] (with a noreserve conjunct in the modeled arm, bare in the
         noaccess arm).  The bound [bv_unsigned x + nZ <= alloc_top h] over the
         PLACED address [x] is the third conjunct of
         [Placement.linux_place_admissible]; [w_is0 len = false] gives its
         two length premises. *)
    | match goal with
      | Hp : linux_place ?h ?thp ?hint ?n (bv_unsigned ?x) /\ _, E : w_is0 ?l = false
        |- (bv_unsigned ?x + ?n <= alloc_top ?h)%Z =>
          exact (proj1 (proj2 (proj2 (Placement.linux_place_admissible h thp hint n (bv_unsigned x)
                   (proj1 (LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.mmap_grant_len_ok l E))
                   (proj2 (LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.mmap_grant_len_ok l E))
                   (proj1 Hp)))))
      end
    | match goal with
      | Hp : linux_place ?h ?thp ?hint ?n (bv_unsigned ?x), E : w_is0 ?l = false
        |- (bv_unsigned ?x + ?n <= alloc_top ?h)%Z =>
          exact (proj1 (proj2 (proj2 (Placement.linux_place_admissible h thp hint n (bv_unsigned x)
                   (proj1 (LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.mmap_grant_len_ok l E))
                   (proj2 (LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.mmap_grant_len_ok l E))
                   Hp))))
      end
    ].
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
