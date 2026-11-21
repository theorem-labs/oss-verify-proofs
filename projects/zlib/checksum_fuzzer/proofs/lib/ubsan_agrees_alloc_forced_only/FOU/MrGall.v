(** * FOU.MrGall — malloc returns a block on every path whose allocations are granted

    [Mr.MrFeasSome.gsome] walks [cmalloc] along the answers of ONE kind of run: brk never grows, every
    anonymous mmap and mprotect is granted.  Under memory forced-only a brk that can grow does grow (its
    refusal is spurious), so the filtered run takes the grow branches [gsome] leaves out.  [gall] is
    [gsome] with every brk answer admitted, and every answer of a MAP_FIXED mmap (malloc goes on whether
    the guard page is mapped or not); [cmalloc_gall] is [cmalloc_gsome] over it, the walk proof for
    proof, with the two grow branches of [alloc_meta] added. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint gall {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k =>
      match e with
      | EBrk _ => forall z, gall P (k z)
      | EMmap _ _ _ flags =>
          if Z.land flags MAP_FIXED =? 0 then forall z, is_err z = false -> gall P (k z)
          else forall z, gall P (k z)
      | EMprotect _ _ _ => gall P (k 0)
      | EUndef _ => True
      | EMunmap _ _ => False
      | EPeek _ _ _ => False
      end
  end.

Lemma gall_sbind {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  gall P1 t -> (forall r, P1 r -> gall P (f r)) -> gall P (sbind t f).
Proof.
  revert t. fix IH 1. intros [r|e k]; cbn; intros H Hf.
  - apply Hf. exact H.
  - destruct e; try exact H; try exact I.
    + intros z. apply IH; [apply H | exact Hf].
    + revert H. match goal with |- (if ?c then _ else _) -> _ => destruct c end.
      * intros H z Hz. apply IH; [apply H; exact Hz | exact Hf].
      * intros H z. apply IH; [apply H | exact Hf].
    + apply IH; [exact H | exact Hf].
Qed.

Section Walk.
Context {R : Type} (P : R -> Prop).

Lemma ga_guard tag c (k bail : M R) : gall P k -> gall P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H | exact I]. Qed.

Lemma ga_queue h m st (k : mstate -> M R) bail : (forall st', gall P (k st')) -> gall P (queue h m st k bail).
Proof. intros Hk. unfold queue. apply ga_guard. apply ga_guard. destruct (get_head st h); apply Hk. Qed.

Lemma ga_activate_group m st (k : mstate -> Z -> M R) bail :
  (forall st' z, gall P (k st' z)) -> gall P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply ga_guard. apply Hk. Qed.

Lemma ga_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' m, gall P (k st' (Some m))) -> gall P (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk | exact I]. Qed.

Lemma ga_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' m, gall P (k st' (Some m))) -> gall P (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply ga_am_take. exact Hk. Qed.

Lemma ga_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, gall P (k st' (Some m))) -> gall P (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  match goal with |- gall P (if ?c then _ else _) => destruct c end; [|apply ga_am_carve; exact Hk].
  cbn [gall].
  replace (negb (mprotect_answer_ok 0)) with false by reflexivity.
  replace ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true by reflexivity. cbn iota. apply ga_am_carve. exact Hk.
Qed.

Lemma ga_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, gall P (k st' (Some m))) -> gall P (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [|apply ga_am_finish; exact Hk].
  cbn [gall]. replace (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true by reflexivity.
  intros z Hz.
  destruct (negb _); [exact I|]. rewrite Hz.
  destruct (new_region _ _ _ _) as [st1 rid]. apply ga_am_finish. exact Hk.
Qed.

Lemma ga_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' m, gall P (k st' (Some m))) -> gall P (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else _). clearbody st0.
  destruct (c_free_meta_head (ctx st0)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply ga_am_take; exact Hk|].
  match goal with |- gall P (if ?c then _ else _) => destruct c end; [|apply ga_am_after_brk; exact Hk].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - cbn [gall]. intros cur. destruct (negb (brk0_answer_ok cur)); [exact I|].
    cbn [gall]. intros r.
    destruct (negb (brk_answer_ok cur _ r)); [exact I|].
    destruct (negb (r =? _)); [apply ga_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [exact I|].
    cbn [gall]. replace (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false by reflexivity.
    intros rg. destruct (negb (mmap_fixed_answer_ok _ rg)); [exact I|].
    destruct (new_region _ _ _ _) as [st1 rid]. apply ga_am_after_brk. exact Hk.
  - apply ga_am_after_brk; exact Hk.
  - cbn [gall]. intros r. destruct (negb (brk_answer_ok _ _ r)); [exact I|].
    destruct (negb (r =? _)); [apply ga_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [exact I|].
    apply ga_am_after_brk; exact Hk.
Qed.

Lemma ga_ta_fin st m mask (k : mstate -> Z -> M R) : (forall st' z, gall P (k st' z)) -> gall P (ta_fin st m mask k).
Proof. intros Hk. unfold ta_fin. apply Hk. Qed.

Lemma ga_try_avail sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, gall P (k st' z)) -> gall P (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [|apply Hk].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply ga_ta_fin; exact Hk|].
  match goal with |- gall P (match ?s with Some _ => _ | None => _ end) => destruct s as [[st1 m1]|] end.
  2:{ destruct (m_freed _ =? 0); [apply Hk | exact I]. }
  match goal with |- gall P (let (a, b) := ?x in _) => destruct x as [[st2 m2] mask] end.
  match goal with |- gall P (let (a, b) := ?x in _) => destruct x as [st3 m3] end.
  apply ga_activate_group. intros st4 z. apply ga_guard. apply ga_ta_fin. exact Hk.
Qed.

Lemma ga_ag_tail lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  (forall st', gall P (k st' (Some m))) -> gall P (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma ga_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail :
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1, (forall st' idx, 0 <= idx -> gall P (k1 st' idx)) -> gall P (asr st1 sc1 req1 k1 bail1)) ->
  (forall st' m, gall P (k st' (Some m))) -> gall P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr Hk. unfold alloc_group. apply ga_alloc_meta. intros st1 m. cbv beta iota.
  match goal with |- gall P (if ?c then _ else _) => destruct c end.
  - match goal with |- gall P (let (a, b) := ?x in _) => destruct x as [cnt needed] end.
    cbn [gall]. replace (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true by reflexivity.
    intros z Hz.
    destruct (negb _); [exact I|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st2 rid]. apply ga_ag_tail. intros st'. apply Hk.
  - apply Hasr. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _) as [g|]; [|exact I]. apply ga_ag_tail. intros st''. apply Hk.
Qed.

Lemma ctz32_nonneg_ga first : 0 <= ctz32 first.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma ga_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  (forall st' idx, 0 <= idx -> gall P (k st' idx)) -> gall P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply ga_try_avail. intros st1 first. destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg_ga|].
  apply ga_alloc_group; [exact IH|]. intros st2 g. cbv beta iota. apply ga_queue. intros st4. apply Hk. lia.
Qed.

Lemma ga_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  (forall st' g idx, gall P (k st' (Some (g, idx)))) -> gall P (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl.
  match goal with |- gall P (match ?g with Some _ => _ | None => _ end) => destruct g as [gp|] end.
  - destruct (negb _); [apply Hk|].
    apply ga_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk | exact I].
  - cbn iota. apply ga_alloc_slot. intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk | exact I].
Qed.

End Walk.

Lemma ga_malloc_core lay st n : size_overflows n = false ->
  gall (fun r => exists g idx, snd r = Some (g, idx)) (malloc_core lay st n).
Proof.
  intros Hn. unfold malloc_core. rewrite Hn.
  destruct (MMAP_THRESHOLD <=? n).
  - cbn [gall]. replace (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true by reflexivity.
    intros z Hz.
    destruct (negb _); [exact I|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st1 rid]. apply ga_alloc_meta. intros st3 g. cbv beta iota.
    cbn. eauto.
  - apply ga_malloc_small_ctrl. intros st' g idx. cbn. eauto.
Qed.

Theorem cmalloc_gall cs n : size_overflows n = false -> gall (fun r => snd r <> None) (cmalloc cs n).
Proof.
  intros Hn. unfold cmalloc. eapply gall_sbind; [apply ga_malloc_core; exact Hn|].
  intros [st1 r] (g & idx & E). cbn in E. subst r. cbn. discriminate.
Qed.
