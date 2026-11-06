(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition map_fixed_b (flags : Z) : bool := negb (Z.land flags MAP_FIXED =? 0).

(* [comment removed for export] *)
Definition ev_adm (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => map_fixed_b flags = false -> is_err z = false
  | EMprotect _ _ _ => z = 0
  | _ => True
  end.

Fixpoint sok {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis (EUndef _) _ => True
  | SVis e k => forall z, ev_adm e z -> sok P (k z)
  end.

Lemma sok_ret {R} (P : R -> Prop) r : P r -> sok P (ret r).
Proof. intros H. exact H. Qed.

Lemma sok_vis {R} (P : R -> Prop) e k :
  (forall z, ev_adm e z -> sok P (k z)) -> sok P (SVis e k).
Proof. intros H. destruct e; cbn; auto. Qed.

Lemma sok_undef {R} (P : R -> Prop) w k : sok P (SVis (EUndef w) k).
Proof. exact I. Qed.

Lemma sok_mono {R} (P P' : R -> Prop) : (forall r, P r -> P' r) -> forall t, sok P t -> sok P' t.
Proof.
  intros HP t. induction t as [r | e k IH]; cbn; [apply HP|].
  destruct e; auto; intros H z Hz; apply IH; apply H; exact Hz.
Qed.

Lemma sok_bind {R S} (P : R -> Prop) (Q : S -> Prop) (t : M R) (f : R -> M S) :
  sok P t -> (forall r, P r -> sok Q (f r)) -> sok Q (sbind t f).
Proof.
  induction t as [r | e k IH]; intros Ht Hf; cbn in *.
  - apply Hf. exact Ht.
  - destruct e; cbn in *; auto; intros z Hz; apply IH; auto.
Qed.

(* [comment removed for export] *)
Fixpoint spath {R} (t : M R) (zs : list Z) (r : R) {struct t} : Prop :=
  match t, zs with
  | SRet r0, [] => r = r0
  | SVis (EUndef _) _, _ => False
  | SVis e k, z :: zs' => ev_adm e z /\ spath (k z) zs' r
  | _, _ => False
  end.

Lemma sok_follows {R} (P : R -> Prop) (t : M R) : forall zs r, sok P t -> spath t zs r -> P r.
Proof.
  induction t as [r0 | e k IH]; intros zs r Hs Hp; cbn in *.
  - destruct zs; [subst; exact Hs | destruct Hp].
  - destruct e; destruct zs as [|z zs]; try (exact (False_ind _ Hp));
      destruct Hp as [Hz Hp]; eapply IH; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SOK.
Variable R : Type.
Variable P : R -> Prop.
Local Notation SOK := (sok P) (only parsing).

Lemma sok_guard tag c (k bail : M R) : SOK k -> SOK (guard tag c k bail).
Proof. intros Hk. unfold guard. destruct c; [exact Hk | exact I]. Qed.

Lemma sok_bad_answer (bail : M R) : SOK (bad_answer bail).
Proof. exact I. Qed.

Lemma sok_queue h m st (k : mstate -> M R) bail :
  (forall st', SOK (k st')) -> SOK (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply sok_guard. apply sok_guard.
  destruct (get_head st h); apply Hk.
Qed.

Lemma sok_free_meta m st (k : mstate -> M R) bail :
  (forall st', SOK (k st')) -> SOK (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply sok_queue. exact Hk. Qed.

Lemma sok_activate_group m st (k : mstate -> Z -> M R) bail :
  (forall st' z, SOK (k st' z)) -> SOK (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply sok_guard. apply Hk. Qed.

(* [comment removed for export] *)

Lemma sok_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' m, SOK (k st' (Some m))) -> SOK (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk | exact I]. Qed.

Lemma sok_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' m, SOK (k st' (Some m))) -> SOK (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply sok_am_take. exact Hk. Qed.

Lemma sok_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, SOK (k st' (Some m))) -> SOK (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [| exact I].
  match goal with |- SOK (if ?c then _ else _) => destruct c end; [| apply sok_am_carve; exact Hk].
  apply sok_vis. intros z Hz. cbn in Hz. subst z. cbn [negb mprotect_answer_ok Z.eqb orb].
  apply sok_am_carve. exact Hk.
Qed.

Lemma sok_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, SOK (k st' (Some m))) -> SOK (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [| apply sok_am_finish; exact Hk].
  apply sok_vis. intros z Hz. cbn in Hz. destruct (negb (mmap_answer_ok _ _ z)); [apply sok_bad_answer|].
  rewrite (Hz eq_refl). destruct (new_region _ _ _ _) as [st1 rid]. apply sok_am_finish. exact Hk.
Qed.

Lemma sok_alloc_meta st (k : mstate -> optr -> M R) bail :
  (forall st' m, SOK (k st' (Some m))) -> SOK (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st). clearbody st0.
  destruct (c_free_meta_head (ctx st0)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply sok_am_take; exact Hk|].
  match goal with |- SOK (if ?c then _ else _) => destruct c end; [| apply sok_am_after_brk; exact Hk].
  destruct (c_brk (ctx st0)).
  - (* [comment removed for export] *)
    apply sok_vis. intros cur _. destruct (negb (brk0_answer_ok cur)); [apply sok_bad_answer|].
    apply sok_vis. intros r _. destruct (negb (brk_answer_ok _ _ r)); [apply sok_bad_answer|].
    destruct (negb (r =? _)); [apply sok_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [apply sok_bad_answer|].
    apply sok_vis. intros rg _. destruct (negb (mmap_fixed_answer_ok _ rg)); [apply sok_bad_answer|].
    destruct (new_region _ _ _ _) as [st1 rid]. apply sok_am_after_brk. exact Hk.
  - (* [comment removed for export] *) apply sok_am_after_brk. exact Hk.
  - (* [comment removed for export] *)
    apply sok_vis. intros r _. destruct (negb (brk_answer_ok _ _ r)); [apply sok_bad_answer|].
    destruct (negb (r =? _)); [apply sok_am_after_brk; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [apply sok_bad_answer|].
    apply sok_am_after_brk. exact Hk.
Qed.

(* [comment removed for export] *)

Lemma sok_try_avail sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, SOK (k st' z)) -> SOK (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail.
  destruct (active st sc) as [m|]; [| apply Hk].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply Hk|].
  match goal with |- SOK (match ?s with _ => _ end) => destruct s as [[st1 m1]|] end.
  2:{ destruct (m_freed (get_meta_rec st m) =? 0); [apply Hk | exact I]. }
  match goal with |- SOK (match ?x with _ => _ end) => destruct x as [[st2 m2] mask] end.
  match goal with |- SOK (match ?x with _ => _ end) => destruct x as [st3 m3] end.
  apply sok_activate_group. intros st4 mask4. apply sok_guard. apply Hk.
Qed.

(* [comment removed for export] *)

Lemma sok_ag_tail lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  (forall st' m', SOK (k st' (Some m'))) -> SOK (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma sok_alloc_group lay (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R)
      st sc req (k : mstate -> optr -> M R) bail :
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1,
     (forall st' idx, 0 <= idx -> SOK (k1 st' idx)) -> SOK (rec st1 sc1 req1 k1 bail1)) ->
  (forall st' m, SOK (k st' (Some m))) ->
  SOK (alloc_group R lay rec st sc req k bail).
Proof.
  intros Hrec Hk. unfold alloc_group. apply sok_alloc_meta. intros st1 m.
  cbv beta.
  match goal with |- SOK (if ?c then _ else _) => destruct c end.
  - (* [comment removed for export] *)
    match goal with |- SOK (match ?x with _ => _ end) => destruct x as [cnt needed] end.
    apply sok_vis. intros z Hz. cbn in Hz.
    destruct (negb (mmap_answer_ok _ _ z)); [apply sok_bad_answer|].
    rewrite (Hz eq_refl). destruct (new_region _ _ _ _) as [st2 rid].
    apply sok_ag_tail. exact Hk.
  - (* [comment removed for export] *)
    apply Hrec. intros st' idx Hidx.
    replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [| exact I].
    apply sok_ag_tail. exact Hk.
Qed.

Lemma ctz32_nonneg z : 0 <= ctz32 z.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma sok_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail,
  (forall st' idx, 0 <= idx -> SOK (k st' idx)) -> SOK (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply sok_try_avail. intros st1 first.
  destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply sok_alloc_group.
  - intros st2 sc2 req2 k2 bail2 Hk2. apply IH. exact Hk2.
  - intros st2 g. apply sok_queue. intros st4. apply Hk. lia.
Qed.

(* [comment removed for export] *)

Lemma sok_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail :
  (forall st' g idx, SOK (k st' (Some (g, idx)))) -> SOK (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl. cbv zeta.
  match goal with |- SOK (match active st ?c with _ => _ end) => set (sc := c); clearbody sc end.
  assert (Hslot : SOK (alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail)).
  { apply sok_alloc_slot. intros st' idx Hidx.
    replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' sc); [apply Hk | exact I]. }
  destruct (active st sc) as [gp|]; [| exact Hslot].
  match goal with |- SOK (if ?b then _ else _) => destruct b end; [apply Hk | exact Hslot].
Qed.


(* [comment removed for export] *)

Lemma sok_true' : forall (t : M R), sok (fun _ => True) t.
Proof. induction t as [r | e k IH]; cbn; [exact I|]. destruct e; auto. Qed.

Lemma sok_rd8' st a (k : Z -> M R) : (forall v, SOK (k v)) -> SOK (rd8 st a k).
Proof.
  intros Hk. unfold rd8. destruct (cell_read _ _); [apply Hk|]. cbn. intros z _.
  destruct (peek_answer_ok z); [apply Hk | exact I].
Qed.

Lemma sok_rd16' st a (k : Z -> M R) : (forall v, SOK (k v)) -> SOK (rd16 st a k).
Proof. intros Hk. unfold rd16. apply sok_rd8'. intros v0. apply sok_rd8'. intros v1. apply Hk. Qed.

Lemma sok_rd32' st a (k : Z -> M R) : (forall v, SOK (k v)) -> SOK (rd32 st a k).
Proof. intros Hk. unfold rd32. do 4 (apply sok_rd8'; intros ?). apply Hk. Qed.

(* [comment removed for export] *)
Ltac sok_crush Hk :=
  repeat first
    [ exact I
    | apply Hk
    | apply sok_guard
    | apply sok_rd8'; intros ?
    | apply sok_rd16'; intros ?
    | apply sok_rd32'; intros ?
    | match goal with |- sok _ (match ?x with _ => _ end) => destruct x end
    | progress (cbv zeta beta) ].

Lemma sok_get_meta st p (k : aptr -> Z -> Z -> M R) bail :
  (forall m off idx, SOK (k m off idx)) -> SOK (get_meta st p k bail).
Proof. intros Hk. unfold get_meta. sok_crush Hk. Qed.

Lemma sok_get_nominal_size st p e (k : Z -> M R) bail :
  (forall sz, SOK (k sz)) -> SOK (get_nominal_size st p e k bail).
Proof. intros Hk. unfold get_nominal_size. sok_crush Hk. Qed.

End SOK.

Definition SOMEP {A B : Type} (x : A * option B) : Prop :=
  match snd x with Some _ => True | None => False end.

Theorem malloc_core_sok lay st n :
  size_overflows n = false -> sok SOMEP (malloc_core lay st n).
Proof.
  intros Hov. unfold malloc_core. rewrite Hov.
  destruct (MMAP_THRESHOLD <=? n).
  - apply sok_vis. intros z Hz. cbn in Hz. destruct (negb (mmap_answer_ok _ _ z)); [apply sok_bad_answer|].
    rewrite (Hz eq_refl). destruct (new_region _ _ _ _) as [st1 rid].
    apply sok_alloc_meta. intros st3 g. exact I.
  - apply sok_malloc_small_ctrl. intros st' g idx. exact I.
Qed.

Theorem cmalloc_sok cs n :
  size_overflows n = false -> sok SOMEP (cmalloc cs n).
Proof.
  intros Hov. unfold cmalloc. eapply sok_bind; [apply malloc_core_sok; exact Hov|].
  intros [st1 [[g idx]|]] H; cbn in H |- *; [exact I | exact H].
Qed.

(* [comment removed for export] *)
Lemma sok_rd8 {R} (P : R -> Prop) st a (k : Z -> M R) : (forall v, sok P (k v)) -> sok P (rd8 st a k).
Proof.
  intros Hk. unfold rd8. destruct (cell_read _ _); [apply Hk|]. cbn. intros z _.
  destruct (peek_answer_ok z); [apply Hk | exact I].
Qed.

Lemma sok_rd16 {R} (P : R -> Prop) st a (k : Z -> M R) : (forall v, sok P (k v)) -> sok P (rd16 st a k).
Proof. intros Hk. unfold rd16. apply sok_rd8. intros v0. apply sok_rd8. intros v1. apply Hk. Qed.

Theorem malloc_sok st n :
  size_overflows n = false -> sok SOMEP (malloc st n).
Proof.
  intros Hov. unfold malloc. eapply sok_bind; [apply malloc_core_sok; exact Hov|].
  intros [st1 [[g idx]|]] H; cbn in H; [| destruct H].
  unfold enframe_full, enframe_read_off. apply sok_rd8. intros b3.
  destruct (negb (b3 =? 0)).
  - apply sok_rd16. intros o16. destruct (enframe_at _ _ _ _ _). exact I.
  - destruct (enframe_at _ _ _ _ _). exact I.
Qed.

Lemma sok_true {R} (t : M R) : sok (fun _ => True) t.
Proof. apply sok_true'. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ISSOME {A : Type} (x : option A) : Prop :=
  match x with Some _ => True | None => False end.

Lemma realloc_hdr_sok st p : sok ISSOME (realloc_hdr st p).
Proof.
  unfold realloc_hdr. apply sok_get_meta. intros m off idx.
  destruct (slot_start _ _); [| exact I].
  apply sok_get_nominal_size. intros sz. exact I.
Qed.

(* [comment removed for export] *)
Fixpoint xsok {R} (P : R -> Prop) (t : MX R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis (XE (EUndef _)) _ => True
  | SVis (XE e) k => forall z, ev_adm e z -> xsok P (k z)
  | SVis (XMremap _ _ _ _) k => forall z, xsok P (k z)
  end.

Lemma xsok_XE {R} (P : R -> Prop) e k :
  (forall z, ev_adm e z -> xsok P (k z)) -> xsok P (SVis (XE e) k).
Proof. intros H. destruct e; cbn; auto. Qed.

Lemma xsok_xlift {R} (P : R -> Prop) (t : M R) : sok P t -> xsok P (xlift t).
Proof.
  induction t as [r | e k IH]; cbn; intros H; [exact H|].
  destruct e; cbn in *; auto.
Qed.

Lemma xsok_bind {R S} (P : R -> Prop) (Q : S -> Prop) (t : MX R) (f : R -> MX S) :
  xsok P t -> (forall r, P r -> xsok Q (f r)) -> xsok Q (sbind t f).
Proof.
  induction t as [r | e k IH]; intros Ht Hf; cbn in *.
  - apply Hf. exact Ht.
  - destruct e as [e|a ol nl fl]; [destruct e|]; cbn in *; auto; intros z Hz; apply IH; auto.
Qed.

Lemma xsok_mono {R} (P P' : R -> Prop) : (forall r, P r -> P' r) -> forall t, xsok P t -> xsok P' t.
Proof.
  intros HP t. induction t as [r | e k IH]; cbn; [apply HP|].
  destruct e as [e|a ol nl fl]; [destruct e|]; auto; intros H z Hz; apply IH; apply H; exact Hz.
Qed.

(* [comment removed for export] *)
Lemma xsok_xprun {O R} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O) (P : R -> Prop) :
  forall (t : MX R) o, xsok P t -> xsok (fun x => P (snd x)) (xprun pans pupd o t).
Proof.
  induction t as [r | e k IH]; intros o H; cbn in *; [exact H|].
  unfold xprun. cbn [eruns].
  destruct e as [e|a ol nl fl]; cbn [xpsel].
  - destruct e; cbn in H |- *; try (intros z Hz; apply IH; auto).
    + (* [comment removed for export] *) apply IH. apply H. exact I.
    + exact I.
  - intros z. apply IH. apply H.
Qed.

Lemma realloc_move_sok st p n :
  size_overflows n = false -> xsok SOMEP (realloc_move st p n).
Proof.
  intros Hov. unfold realloc_move.
  eapply xsok_bind; [apply xsok_xlift; apply malloc_sok; exact Hov|].
  intros [st1 [q|]] H; cbn in H; [| destruct H].
  eapply xsok_bind; [apply xsok_xlift; apply sok_true|].
  intros st2 _. exact I.
Qed.

Theorem realloc_sok st p n :
  size_overflows n = false -> xsok SOMEP (realloc st p n).
Proof.
  intros Hov. unfold realloc. destruct p as [p|]; [| apply xsok_xlift; apply malloc_sok; exact Hov].
  rewrite Hov.
  eapply xsok_bind; [apply xsok_xlift; apply realloc_hdr_sok|].
  intros [[[g idx] osz]|] H; cbn in H; [| destruct H]. cbv beta zeta.
  match goal with |- xsok _ (if ?c then _ else _) => destruct c end; [exact I|].
  match goal with |- xsok _ (if ?c then _ else _) => destruct c end; [| apply realloc_move_sok; exact Hov].
  unfold xguard. match goal with |- xsok _ (if ?c then _ else _) => destruct c end; [| exact I].
  match goal with |- xsok _ (if ?c then _ else _) => destruct c end; [exact I|].
  match goal with |- xsok _ (if ?c then _ else _) => destruct c end; [apply realloc_move_sok; exact Hov|].
  cbn. intros r. destruct (negb (mremap_answer_ok _ _ _ _ r)); [exact I|].
  destruct (is_err r); [apply realloc_move_sok; exact Hov | exact I].
Qed.

End RC__.
