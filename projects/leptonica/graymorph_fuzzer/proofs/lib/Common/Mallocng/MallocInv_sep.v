(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_slot_range : forall k, cvalid k ->
  LOCKA + 8 <= caddr k /\ caddr k + clen k <= CTX_END /\ 0 < clen k <= 8.
Proof.
  intros k Hk; destruct k; cbn in *; unfold C_SECRET, C_INIT, C_CTR, C_FMH, C_AM, C_AMC, C_AAC, C_SHIFT,
    C_AHEAD, C_ATAIL, C_AAREAS, C_SEQ, C_BRK, C_ACTIVE, C_USAGE, C_USEQ, C_BOUNCE, LOCKA, CTX_END; llia.
Qed.

Lemma ctx_slot_disj : forall k k', cvalid k -> cvalid k' -> k <> k' ->
  caddr k + clen k <= caddr k' \/ caddr k' + clen k' <= caddr k.
Proof.
  intros k k' Hk Hk' Hne; destruct k, k'; cbn in *;
  unfold C_SECRET, C_INIT, C_CTR, C_FMH, C_AM, C_AMC, C_AAC, C_SHIFT,
    C_AHEAD, C_ATAIL, C_AAREAS, C_SEQ, C_BRK, C_ACTIVE, C_USAGE, C_USEQ, C_BOUNCE in *;
  first [ llia
        | exfalso; apply Hne; reflexivity
        | (* [comment removed for export] *)
          match goal with
          | [ H : ?C ?i <> ?C ?j |- _ ] => assert (i <> j) by (intros E; apply H; rewrite E; reflexivity); llia
          end ].
Qed.

Lemma cupd_same : forall c k v, cupd c k v k = v.
Proof. intros c k v. unfold cupd. destruct (cslot_eq_dec k k); [reflexivity | contradiction]. Qed.

Lemma cupd_other : forall c k v k', k' <> k -> cupd c k v k' = c k'.
Proof. intros c k v k' Hne. unfold cupd. destruct (cslot_eq_dec k' k); [contradiction | reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mfield_range : forall fl, 0 <= moff fl /\ moff fl + mlen fl <= 40 /\ 0 < mlen fl <= 8.
Proof. intros fl; destruct fl; cbn; llia. Qed.

Lemma mfield_disj : forall fl fl', fl <> fl' ->
  moff fl + mlen fl <= moff fl' \/ moff fl' + mlen fl' <= moff fl.
Proof. intros fl fl' Hne; destruct fl, fl'; cbn; try llia; contradiction. Qed.

Lemma mupd_same : forall mt fl v, mt_f (mupd mt fl v) fl = v.
Proof. intros mt fl v. unfold mupd. rewrite mt_f_MT. destruct (mfield_eq_dec fl fl); [reflexivity | contradiction]. Qed.

Lemma mupd_other : forall mt fl v fl', fl' <> fl -> mt_f (mupd mt fl v) fl' = mt_f mt fl'.
Proof. intros mt fl v fl' Hne. unfold mupd. rewrite mt_f_MT. destruct (mfield_eq_dec fl' fl); [contradiction | reflexivity]. Qed.

Lemma mupd_role : forall mt fl v, mt_role (mupd mt fl v) = mt_role mt.
Proof. reflexivity. Qed.

Lemma aupd_same : forall g ma mt, aupd g ma mt ma = Some mt.
Proof. intros g ma mt. unfold aupd. destruct (Z.eq_dec ma ma); [reflexivity | contradiction]. Qed.

Lemma aupd_other : forall g ma mt x, x <> ma -> aupd g ma mt x = g x.
Proof. intros g ma mt x Hne. unfold aupd. destruct (Z.eq_dec x ma); [contradiction | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma meta_addr_range : forall pg k, 0 <= k < 101 ->
  pg + 24 <= meta_addr pg k /\ meta_addr pg k + 40 <= pg + 4096.
Proof. intros pg k Hk. unfold meta_addr. llia. Qed.

Lemma meta_addr_disj : forall pg k k', 0 <= k -> 0 <= k' -> k <> k' ->
  meta_addr pg k + 40 <= meta_addr pg k' \/ meta_addr pg k' + 40 <= meta_addr pg k.
Proof. intros pg k k' Hk Hk' Hne. unfold meta_addr. llia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma size_classes_pos : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof. unfold size_classes. repeat (constructor; [llia|]). constructor. Qed.

Lemma size_class_bound : forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros sc Hsc. unfold size_class.
  assert (Hlt : (Z.to_nat sc < length size_classes)%nat) by (cbn; llia).
  exact (proj1 (Forall_nth _ _) size_classes_pos (Z.to_nat sc) 0 Hlt).
Qed.

Lemma w_sc_range : forall w, 0 <= w_sc w < 64.
Proof. intros w. unfold w_sc. apply Z.mod_pos_bound. llia. Qed.

Lemma w_last_range : forall w, 0 <= w_last w < 32.
Proof. intros w. unfold w_last. apply Z.mod_pos_bound. llia. Qed.

Lemma stride_ge16 : forall mt, 0 <= mt_w32 mt ->
  (mt_sc mt < 48 \/ (mt_sc mt = 63 /\ mt_last mt = 0 /\ 0 < mt_maplen mt)) -> 16 <= mt_stride mt.
Proof.
  intros mt Hw0 Hsc. unfold mt_stride. unfold mt_sc in *.
  pose proof (w_sc_range (mt_w32 mt)) as Hr.
  destruct ((mt_maplen mt =? 0) || negb (mt_last mt =? 0)) eqn:E.
  - destruct Hsc as [H | (H & Hl & Hm)].
    + pose proof (size_class_bound (w_sc (mt_w32 mt)) ltac:(llia)). llia.
    + exfalso.
      apply Bool.orb_true_iff in E. destruct E as [E|E].
      * apply Z.eqb_eq in E. llia.
      * apply Bool.negb_true_iff in E. apply Z.eqb_neq in E. llia.
  - apply Bool.orb_false_iff in E. destruct E as [E1 E2]. apply Z.eqb_neq in E1.
    unfold mt_maplen, w_maplen in *.
    assert (0 <= mt_w32 mt / 4096) by (apply Z.div_pos; llia).
    destruct Hsc as [H1 | (H1 & Hl & Hm)]; lnia.
Qed.

Lemma stride_16 : forall mt, exists q, mt_stride mt = 16 * q.
Proof.
  intros mt. unfold mt_stride.
  destruct ((mt_maplen mt =? 0) || negb (mt_last mt =? 0)).
  - exists (size_class (mt_sc mt)). reflexivity.
  - exists (mt_maplen mt * 256 - 1). llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_ctx (A : astate) (c : ctx_rec) : astate :=
  AST c (a_areas A) (a_meta A) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) (a_xmaps A).
Definition set_meta (A : astate) (g : mmap_t) : astate :=
  AST (a_ctx A) (a_areas A) g (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) (a_xmaps A).

Definition actx_upd (A : astate) (k : cslot) (v : Z) : astate := set_ctx A (cupd (a_ctx A) k v).
Definition ameta_upd (A : astate) (ma : Z) (mt : meta_rec) : astate := set_meta A (aupd (a_meta A) ma mt).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_areas (A : astate) (lo hi : Z) : Prop :=
  exists pg, In pg (a_areas A) /\ pg <= lo /\ hi <= pg + 4096.
Definition in_roots (A : astate) (lo hi : Z) : Prop :=
  exists mr mtr aibr slr, a_meta A mr = Some mtr /\ mt_role mtr = RGroup aibr slr /\ 0 < mt_maplen mtr /\
    mt_mem mtr <= lo /\ hi <= mt_mem mtr + grp_map_len mtr.

Section Where.
  Variable A : astate.
  Hypothesis HW : WF A.

  Lemma has_ctx_where : forall f, has_ctx A f ->
    LOCKA + 8 <= f_a f /\ f_a f + f_n f <= CTX_END /\ 0 < f_n f <= 8.
  Proof.
    intros f (k & Hk & ->). cbn. apply ctx_slot_range. exact Hk.
  Qed.

  Lemma has_area_where : forall f, has_area A f ->
    in_areas A (f_a f) (f_a f + f_n f) /\ 0 < f_n f <= 8.
  Proof.
    intros f (pg & Hpg & ->). cbn. split; [|llia]. exists pg. split; [exact Hpg | llia].
  Qed.

  Lemma has_meta_where : forall f, has_meta A f ->
    in_areas A (f_a f) (f_a f + f_n f) /\ 0 < f_n f <= 8.
  Proof.
    intros f (ma & mt & fl & Hma & ->). cbn.
    pose proof (mfield_range fl) as Hfl.
    destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg & k & Hpg & Hk & ->).
    pose proof (meta_addr_range pg k Hk). split; [|llia].
    exists pg. split; [exact Hpg | llia].
  Qed.

  (* [comment removed for export] *)
  Lemma slot_fields_where : forall ma mt aib slots i st f,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    nth_error slots i = Some st -> In f (slot_fields mt (Z.of_nat i) st) ->
    gext_lo mt + 12 <= f_a f /\ f_a f + f_n f <= gext_hi mt + 1 /\ 0 < f_n f <= 8.
  Proof.
    intros ma mt aib slots i st f Hma Hr Hi Hf.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    assert (Hi' : (i < length slots)%nat) by (apply (proj1 (nth_error_Some slots i)); rewrite Hi; discriminate).
    assert (HiZ : 0 <= Z.of_nat i < mt_cnt mt) by llia.
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as Hstride.
    unfold gext_lo, gext_hi. unfold slot_fields, slot_fields_g in Hf.
    set (p0 := slot_start_g (mt_mem mt) (mt_stride mt) (Z.of_nat i)) in *.
    set (e := slot_end_g (mt_mem mt) (mt_stride mt) (Z.of_nat i)) in *.
    assert (Hp0 : p0 = mt_mem mt + 16 + Z.of_nat i * mt_stride mt) by reflexivity.
    assert (He : e = mt_mem mt + 16 + Z.of_nat i * mt_stride mt + mt_stride mt - 4) by reflexivity.
    assert (Hslot : mt_mem mt + 16 <= p0 /\ p0 + mt_stride mt <= mt_mem mt + 16 + mt_cnt mt * mt_stride mt).
    { rewrite Hp0. split; [lnia|]. 
      assert (Z.of_nat i * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by lnia. llia. }
    apply in_app_iff in Hf. destruct Hf as [Hf | Hf].
    { destruct Hf as [<- | [<- | []]]; cbn; llia. }
    destruct st as [ | | off n | ch].
    - destruct Hf.
    - destruct Hf.
    - pose proof (wf_live A HW ma mt aib slots (Z.of_nat i) off n Hma Hr ltac:(rewrite Nat2Z.id; exact Hi) ltac:(llia))
        as (Hoff & Hn & Hfit2 & Hoff16 & _).
      set (p := p0 + 16 * off) in *. set (rsv := e - p - n) in *.
      assert (Hrsv : 0 <= rsv) by (subst rsv e p; llia).
      repeat (apply in_app_iff in Hf; destruct Hf as [Hf | Hf]).
      + destruct (off =? 0) eqn:E; [destruct Hf|]. apply Z.eqb_neq in E.
        destruct Hf as [<- | [<- | [<- | []]]]; cbn; subst p; llia.
      + destruct Hf as [<- | [<- | []]]; cbn; subst p; llia.
      + destruct (rsv <? 5) eqn:E; [destruct Hf|]. apply Z.ltb_ge in E.
        destruct Hf as [<- | [<- | []]]; cbn; llia.
      + destruct (rsv =? 0) eqn:E; [destruct Hf|]. apply Z.eqb_neq in E.
        destruct Hf as [<- | []]; cbn; subst rsv p; llia.
    - destruct Hf as [<- | [<- | []]]; cbn; llia.
  Qed.

  Lemma has_grp_where : forall f, has_grp A f ->
    (exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
       gext_lo mt <= f_a f /\ f_a f + f_n f <= gext_hi mt + 1) /\ 0 < f_n f <= 8.
  Proof.
    intros f (ma & mt & aib & slots & Hma & Hr & Hf).
    destruct Hf as [Hf | (i & st & Hi & Hf)].
    - destruct (wf_grp A HW ma mt aib slots Hma Hr) as
        (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
      pose proof (stride_ge16 mt ltac:(llia) Hsc) as Hstride.
      assert (0 <= mt_cnt mt * mt_stride mt) by lnia.
      destruct Hf as [<- | [<- | []]]; cbn; unfold gext_lo, gext_hi; (split; [|llia]);
        exists ma, mt, aib, slots; repeat split; try assumption; llia.
    - pose proof (slot_fields_where ma mt aib slots i st f Hma Hr Hi Hf) as (H1 & H2 & H3).
      split; [|exact H3]. exists ma, mt, aib, slots. repeat split; try assumption; llia.
  Qed.

  Lemma has_grp_root : forall f, has_grp A f -> in_roots A (f_a f) (f_a f + f_n f).
  Proof.
    intros f Hf. destruct (has_grp_where f Hf) as ((ma & mt & aib & slots & Hma & Hr & Hlo & Hhi) & _).
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hrlo & Hrhi & _).
    exists mr, mtr, aibr, slr. repeat split; try assumption; llia.
  Qed.

  (* [comment removed for export] *)
  Lemma has_where : forall f, has A f ->
    0 < f_n f <= 8 /\
    ( (has_ctx A f /\ LOCKA + 8 <= f_a f /\ f_a f + f_n f <= CTX_END)
      \/ ((has_area A f \/ has_meta A f) /\ in_areas A (f_a f) (f_a f + f_n f))
      \/ (has_grp A f /\ in_roots A (f_a f) (f_a f + f_n f)) ).
  Proof.
    intros f [Hf | [Hf | [Hf | Hf]]].
    - pose proof (has_ctx_where f Hf). split; [llia|]. left. split; [exact Hf | llia].
    - pose proof (has_area_where f Hf) as [H1 H2]. split; [exact H2|]. right; left. split; [left; exact Hf | exact H1].
    - pose proof (has_meta_where f Hf) as [H1 H2]. split; [exact H2|]. right; left. split; [right; exact Hf | exact H1].
    - pose proof (has_grp_where f Hf) as [_ H2]. split; [exact H2|]. right; right. split; [exact Hf | apply has_grp_root; exact Hf].
  Qed.
End Where.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ranges.
  Variable A : astate.
  Hypothesis HW : WF A.

  Lemma in_areas_heap : forall lo hi, in_areas A lo hi -> lo <= hi ->
    heap_range lo hi.
  Proof.
    intros lo hi (pg & Hpg & Hlo & Hhi) Hle.
    destruct (wf_areas_al A HW pg Hpg) as [_ (H1 & H2 & H3 & H4)]. unfold heap_range. llia.
  Qed.

  Lemma in_roots_heap : forall lo hi, in_roots A lo hi -> lo <= hi -> heap_range lo hi.
  Proof.
    intros lo hi (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi) Hle.
    destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg).
    destruct (Hpg Hml) as [_ (H1 & H2 & H3 & H4)]. unfold heap_range. llia.
  Qed.

  Lemma has_addr : forall f, has A f ->
    0 < f_n f <= 8 /\ 0x1000 <= f_a f /\ f_a f + f_n f <= alloc_ceiling /\
    ((LOCKA + 8 <= f_a f /\ f_a f + f_n f <= CTX_END /\ has_ctx A f) \/
     (heap_range (f_a f) (f_a f + f_n f) /\ ~ has_ctx A f \/ heap_range (f_a f) (f_a f + f_n f))).
  Proof.
    intros f Hf. destruct (has_where A HW f Hf) as [Hn [ (Hc & H1 & H2) | [ (Hc & Hin) | (Hc & Hin) ] ]].
    - unfold LOCKA, CTX_END in *. ceil. split; [llia|]. split; [llia|]. split; [llia|].
      left. split; [llia|]. split; [llia|]. exact Hc.
    - pose proof (in_areas_heap _ _ Hin ltac:(llia)) as Hh. unfold heap_range in Hh.
      split; [llia|]. split; [llia|]. split; [llia|]. right. right. unfold heap_range. llia.
    - pose proof (in_roots_heap _ _ Hin ltac:(llia)) as Hh. unfold heap_range in Hh.
      split; [llia|]. split; [llia|]. split; [llia|]. right. right. unfold heap_range. llia.
  Qed.

  Lemma facts_addr : forall x b, facts A x b -> 0x1000 <= x < alloc_ceiling.
  Proof.
    intros x b (f & Hf & [Hx ->]). pose proof (has_addr f Hf) as (Hn & H1 & H2 & _). llia.
  Qed.

  Lemma facts_addr64 : forall x b, facts A x b -> 0 <= x < 2^64.
  Proof. intros x b H. pose proof (facts_addr x b H). ceil. llia. Qed.

  Lemma dom_addr : forall x, dom A x -> 0x1000 <= x < alloc_ceiling.
  Proof.
    intros x [ (pg & Hpg & Hx) | [ (ma & mt & aib & slots & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx) ] ].
    - destruct (wf_areas_al A HW pg Hpg) as [_ (H1 & H2 & H3 & H4)]. llia.
    - destruct (wf_grp A HW ma mt aib slots Hma Hr) as
        (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg).
      destruct (Hpg Hml) as [_ (H1 & H2 & H3 & H4)]. llia.
    - destruct (wf_pages_al A HW pg Hpg) as [_ (H1 & H2 & H3 & H4)]. llia.
  Qed.

  Lemma dom_addr64 : forall x, dom A x -> 0 <= x < 2^64.
  Proof. intros x H. pose proof (dom_addr x H). ceil. llia. Qed.

  (* [comment removed for export] *)
  Lemma nonctx_avoids_ctx : forall f, has A f -> ~ has_ctx A f ->
    f_a f + f_n f <= IMG_LO \/ IMG_HI <= f_a f.
  Proof.
    intros f Hf Hnc. destruct (has_addr f Hf) as (Hn & _ & _ & [ (H1 & H2 & Hc) | [ (Hh & _) | Hh ] ]);
      [ exact (False_ind _ (Hnc Hc)) | unfold heap_range in Hh; llia | unfold heap_range in Hh; llia ].
  Qed.
End Ranges.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Updates.
  Variable A : astate.
  Hypothesis HW : WF A.

  Lemma heap_avoids_ctx : forall lo hi, heap_range lo hi ->
    forall k, cvalid k -> hi <= caddr k \/ caddr k + clen k <= lo.
  Proof.
    intros lo hi (H1 & H2 & H3 & H4) k Hk. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3).
    unfold LOCKA, CTX_END in *. llia.
  Qed.

  Lemma nonctx_fact_avoids_ctx : forall f,
    has_area A f \/ has_meta A f \/ has_grp A f ->
    forall k, cvalid k -> f_a f + f_n f <= caddr k \/ caddr k + clen k <= f_a f.
  Proof.
    intros f Hf k Hk.
    assert (Hh : heap_range (f_a f) (f_a f + f_n f)).
    { destruct Hf as [Hf | [Hf | Hf]].
      - destruct (has_area_where A f Hf) as [Hin Hn]. apply (in_areas_heap A HW); [exact Hin | llia].
      - destruct (has_meta_where A HW f Hf) as [Hin Hn]. apply (in_areas_heap A HW); [exact Hin | llia].
      - pose proof (has_grp_where A HW f Hf) as [_ Hn].
        apply (in_roots_heap A HW); [apply (has_grp_root A HW); exact Hf | llia]. }
    exact (heap_avoids_ctx _ _ Hh k Hk).
  Qed.

  (* [comment removed for export] *)
  Lemma has_actx_upd : forall k v f,
    cvalid k -> k <> KSecret ->
    has (actx_upd A k v) f ->
    f = FCT (caddr k) (clen k) v \/
    (has A f /\ (f_a f + f_n f <= caddr k \/ caddr k + clen k <= f_a f)).
  Proof.
    intros k v f Hk Hks Hf.
    destruct Hf as [ (k' & Hk' & ->) | Hrest ]; cbn in *.
    - destruct (cslot_eq_dec k' k) as [-> | Hne].
      + left. rewrite cupd_same. reflexivity.
      + right. rewrite cupd_other by exact Hne. split.
        * left. exists k'. split; [exact Hk' | reflexivity].
        * cbn. destruct (ctx_slot_disj k' k Hk' Hk Hne); llia.
    - assert (Hold : has_area A f \/ has_meta A f \/ has_grp A f).
      { destruct Hrest as [ (pg & Hpg & ->) | [Hm | Hg] ].
        - left. exists pg. split; [exact Hpg|]. unfold actx_upd, set_ctx. cbn.
          rewrite cupd_other by (intros E; apply Hks; symmetry; exact E). reflexivity.
        - right; left. exact Hm.
        - right; right. exact Hg. }
      right. split.
      + right. exact Hold.
      + apply nonctx_fact_avoids_ctx; [exact Hold | exact Hk].
  Qed.

  Lemma dom_actx_upd : forall k v x, dom (actx_upd A k v) x <-> dom A x.
  Proof. intros k v x. unfold dom, actx_upd, set_ctx. cbn. tauto. Qed.

  (* [comment removed for export] *)
  Lemma rep_cupd : forall m k v,
    Rep A m -> cvalid k -> k <> KSecret -> 0 <= v ->
    Rep (actx_upd A k v) (wbytes m (Z_to_bv 64 (caddr k)) (Z_to_le_bytes (Z.to_nat (clen k)) v)).
  Proof.
    intros m k v HR Hk Hks Hv.
    pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    apply (rep_write A); [exact HR | llia | rewrite length_Z_to_le_bytes; llia | | | exact (facts_addr64 A HW)].
    - intros x b (f & Hf & [Hx ->]). rewrite length_Z_to_le_bytes.
      destruct (has_actx_upd k v f Hk Hks Hf) as [-> | [Hold Hdisj]]; cbn in *.
      + left. split; [llia|]. rewrite nth_Z_to_le_bytes; [| exact Hv | llia]. rewrite Z2Nat.id by llia. reflexivity.
      + right. split; [llia|]. exists f. split; [exact Hold | split; [llia | reflexivity]].
    - intros x Hx. apply (proj1 (dom_actx_upd k v x)). exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_read_ctx : forall m k,
    Rep A m -> cvalid k -> 0 <= a_ctx A k ->
    exists bs, rdn ml_segs m (Z_to_bv 64 (caddr k)) (Z.to_nat (clen k)) = Some bs /\
               length bs = Z.to_nat (clen k) /\
               bytes_le_to_Z bs = a_ctx A k mod 2 ^ (8 * clen k).
  Proof.
    intros m k HR Hk Hv. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    destruct (rep_read A m HR (caddr k) (Z.to_nat (clen k)) (a_ctx A k)) as (bs & H1 & H2 & H3);
      [ | llia | llia | exact Hv |].
    - left. exists k. split; [exact Hk|]. rewrite Z2Nat.id by llia. reflexivity.
    - exists bs. rewrite Z2Nat.id in H3 by llia. auto.
  Qed.
End Updates.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pages_disj : forall p q, page_aligned p -> page_aligned q -> p <> q ->
  p + 4096 <= q \/ q + 4096 <= p.
Proof.
  intros p q Hp Hq Hne. unfold page_aligned in *.
  pose proof (Z.div_mod p 4096 ltac:(llia)). pose proof (Z.div_mod q 4096 ltac:(llia)).
  assert (p / 4096 <> q / 4096) by (intros E; apply Hne; llia). lnia.
Qed.

Lemma mupd_mem : forall mt fl v, fl <> FMem -> mt_mem (mupd mt fl v) = mt_mem mt.
Proof. intros. unfold mt_mem. apply mupd_other. congruence. Qed.
Lemma mupd_w32 : forall mt fl v, fl <> FW32 -> mt_w32 (mupd mt fl v) = mt_w32 mt.
Proof. intros. unfold mt_w32. apply mupd_other. congruence. Qed.

Lemma stride_ext : forall mt mt', mt_mem mt' = mt_mem mt -> mt_w32 mt' = mt_w32 mt -> mt_stride mt' = mt_stride mt.
Proof. intros mt mt' Hm Hw. unfold mt_stride, mt_maplen, mt_last, mt_sc. rewrite Hw. reflexivity. Qed.

Lemma slot_fields_ext : forall mt mt' i st, mt_mem mt' = mt_mem mt -> mt_w32 mt' = mt_w32 mt ->
  slot_fields mt' i st = slot_fields mt i st.
Proof.
  intros mt mt' i st Hm Hw. unfold slot_fields. rewrite (stride_ext mt mt' Hm Hw), Hm. reflexivity.
Qed.

Lemma gext_ext : forall mt mt', mt_mem mt' = mt_mem mt -> mt_w32 mt' = mt_w32 mt ->
  gext_lo mt' = gext_lo mt /\ gext_hi mt' = gext_hi mt.
Proof.
  intros mt mt' Hm Hw. unfold gext_lo, gext_hi, mt_cnt, mt_last. rewrite (stride_ext mt mt' Hm Hw), Hm, Hw. split; reflexivity.
Qed.

Section MetaUpd.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variable ma : Z.
  Variable mt : meta_rec.
  Hypothesis Hma : a_meta A ma = Some mt.

  Lemma meta_in_area : exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ ma = meta_addr pg k.
  Proof. apply (proj1 (wf_meta_dom A HW ma)). rewrite Hma. discriminate. Qed.

  (* [comment removed for export] *)
  Lemma nonmeta_avoid_meta : forall f, has_ctx A f \/ has_area A f \/ has_grp A f ->
    f_a f + f_n f <= ma \/ ma + 40 <= f_a f.
  Proof.
    intros f Hf. destruct meta_in_area as (pg & k & Hpg & Hk & Ema).
    pose proof (meta_addr_range pg k Hk) as Hmr.
    destruct (wf_areas_al A HW pg Hpg) as [Hal Hhr].
    destruct Hf as [Hc | [Har | Hg]].
    - pose proof (has_ctx_where A f Hc) as (C1 & C2 & C3).
      destruct Hc as (k' & Hk' & ->). cbn in *.
      destruct (heap_avoids_ctx pg (pg + 4096) Hhr k' Hk'); llia.
    - destruct Har as (pg' & Hpg' & ->). cbn.
      destruct (Z.eq_dec pg' pg) as [-> | Hne]; [llia|].
      destruct (wf_areas_al A HW pg' Hpg') as [Hal' _].
      destruct (pages_disj pg pg' Hal Hal' ltac:(congruence)); llia.
    - pose proof (has_grp_where A HW f Hg) as ((mg & mtg & aib & slots & Hmg & Hrg & Hlo & Hhi) & Hn).
      destruct (wf_grp_root A HW mg mtg aib slots Hmg Hrg) as (mr & mtr & aibr & slr & Hmr' & Hrr & Hml & Hrlo & Hrhi & _).
      destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpg Hmr' Hrr Hml); llia.
  Qed.

  Lemma other_meta_avoid_meta : forall ma' mt' fl', a_meta A ma' = Some mt' -> ma' <> ma ->
    ma' + moff fl' + mlen fl' <= ma \/ ma + 40 <= ma' + moff fl'.
  Proof.
    intros ma' mt' fl' Hma' Hne. destruct meta_in_area as (pg & k & Hpg & Hk & Ema).
    pose proof (meta_addr_range pg k Hk) as Hmr. pose proof (mfield_range fl') as Hfl.
    destruct (wf_areas_al A HW pg Hpg) as [Hal Hhr].
    destruct (proj1 (wf_meta_dom A HW ma') ltac:(rewrite Hma'; discriminate)) as (pg' & k' & Hpg' & Hk' & ->).
    pose proof (meta_addr_range pg' k' Hk') as Hmr'.
    destruct (Z.eq_dec pg' pg) as [-> | Hnep].
    - assert (k' <> k) by (intros ->; apply Hne; symmetry; exact Ema).
      destruct (meta_addr_disj pg k k' ltac:(llia) ltac:(llia) ltac:(congruence)); llia.
    - destruct (wf_areas_al A HW pg' Hpg') as [Hal' _].
      destruct (pages_disj pg pg' Hal Hal' ltac:(congruence)); llia.
  Qed.

  (* [comment removed for export] *)
  Lemma has_ameta_upd_field : forall fl v f,
    (fl <> FMem /\ fl <> FW32) ->
    has (ameta_upd A ma (mupd mt fl v)) f ->
    f = FCT (ma + moff fl) (mlen fl) v \/
    (has A f /\ (f_a f + f_n f <= ma + moff fl \/ ma + moff fl + mlen fl <= f_a f)).
  Proof.
    intros fl v f [Hf1 Hf2] Hf. pose proof (mfield_range fl) as Hfl.
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - right. split; [left; exact Hc|].
      destruct (nonmeta_avoid_meta f (or_introl Hc)); llia.
    - right. split; [right; left; exact Har|].
      destruct (nonmeta_avoid_meta f (or_intror (or_introl Har))); llia.
    - destruct Hm as (ma' & mt' & fl' & Hma' & ->). unfold ameta_upd, set_meta in Hma'. cbn in Hma'.
      destruct (Z.eq_dec ma' ma) as [-> | Hne].
      + rewrite aupd_same in Hma'. injection Hma' as <-.
        destruct (mfield_eq_dec fl' fl) as [-> | Hnf].
        * left. rewrite mupd_same. reflexivity.
        * right. rewrite mupd_other by exact Hnf. split.
          -- right; right; left. exists ma, mt, fl'. split; [exact Hma | reflexivity].
          -- cbn. destruct (mfield_disj fl' fl Hnf); llia.
      + rewrite aupd_other in Hma' by exact Hne. right. split.
        * right; right; left. exists ma', mt', fl'. split; [exact Hma' | reflexivity].
        * cbn. pose proof (mfield_range fl'). destruct (other_meta_avoid_meta ma' mt' fl' Hma' Hne); llia.
    - destruct Hg as (ma' & mt' & aib & slots & Hma' & Hr' & Hin). unfold ameta_upd, set_meta in Hma'. cbn in Hma'.
      assert (Hold : has_grp A f).
      { destruct (Z.eq_dec ma' ma) as [-> | Hne].
        + rewrite aupd_same in Hma'. injection Hma' as <-. cbn in Hr'.
          exists ma, mt, aib, slots. split; [exact Hma | split; [exact Hr' |]].
          unfold grp_hdr_fields in *. rewrite (mupd_mem mt fl v Hf1) in Hin.
          destruct Hin as [Hin | (i & st & Hi & Hin)]; [left; exact Hin | right].
          exists i, st. split; [exact Hi|].
          rewrite <- (slot_fields_ext mt (mupd mt fl v) (Z.of_nat i) st); [exact Hin | apply mupd_mem; exact Hf1 | apply mupd_w32; exact Hf2].
        + rewrite aupd_other in Hma' by exact Hne. exists ma', mt', aib, slots. split; [exact Hma' | split; [exact Hr' | exact Hin]]. }
      right. split; [right; right; right; exact Hold|].
      destruct (nonmeta_avoid_meta f (or_intror (or_intror Hold))); llia.
  Qed.

  Lemma dom_ameta_upd_field : forall fl v x, (fl <> FMem /\ fl <> FW32) ->
    dom (ameta_upd A ma (mupd mt fl v)) x -> dom A x.
  Proof.
    intros fl v x [Hf1 Hf2] [Ha | [(ma' & mt' & aib & slots & Hma' & Hr' & Hml & Hx) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
    unfold ameta_upd, set_meta in Hma'. cbn in Hma'.
    destruct (Z.eq_dec ma' ma) as [-> | Hne].
    - rewrite aupd_same in Hma'. injection Hma' as <-. cbn in Hr'.
      unfold grp_map_len, mt_maplen in *. rewrite (mupd_w32 mt fl v Hf2), (mupd_mem mt fl v Hf1) in *.
      exists ma, mt, aib, slots. auto.
    - rewrite aupd_other in Hma' by exact Hne. exists ma', mt', aib, slots. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_mupd : forall m fl v,
    Rep A m -> (fl <> FMem /\ fl <> FW32) -> 0 <= v ->
    Rep (ameta_upd A ma (mupd mt fl v)) (wbytes m (Z_to_bv 64 (ma + moff fl)) (Z_to_le_bytes (Z.to_nat (mlen fl)) v)).
  Proof.
    intros m fl v HR Hfl Hv. pose proof (mfield_range fl) as Hr.
    destruct meta_in_area as (pg & k & Hpg & Hk & Ema). pose proof (meta_addr_range pg k Hk).
    destruct (wf_areas_al A HW pg Hpg) as [_ (Hh1 & Hh2 & Hh3 & Hh4)]. ceil.
    apply (rep_write A); [exact HR | llia | rewrite length_Z_to_le_bytes; llia | | | exact (facts_addr64 A HW)].
    - intros x b (f & Hf & [Hx ->]). rewrite length_Z_to_le_bytes.
      destruct (has_ameta_upd_field fl v f Hfl Hf) as [-> | [Hold Hdisj]]; cbn in *.
      + left. split; [llia|]. rewrite nth_Z_to_le_bytes; [| exact Hv | llia]. rewrite Z2Nat.id by llia. reflexivity.
      + right. split; [llia|]. exists f. split; [exact Hold | split; [llia | reflexivity]].
    - intros x Hx. exact (dom_ameta_upd_field fl v x Hfl Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma rep_read_meta : forall m fl,
    Rep A m -> 0 <= mt_f mt fl ->
    exists bs, rdn ml_segs m (Z_to_bv 64 (ma + moff fl)) (Z.to_nat (mlen fl)) = Some bs /\
               length bs = Z.to_nat (mlen fl) /\
               bytes_le_to_Z bs = mt_f mt fl mod 2 ^ (8 * mlen fl).
  Proof.
    intros m fl HR Hv. pose proof (mfield_range fl) as Hr.
    destruct meta_in_area as (pg & k & Hpg & Hk & Ema). pose proof (meta_addr_range pg k Hk).
    destruct (wf_areas_al A HW pg Hpg) as [_ (Hh1 & Hh2 & Hh3 & Hh4)]. ceil.
    destruct (rep_read A m HR (ma + moff fl) (Z.to_nat (mlen fl)) (mt_f mt fl)) as (bs & H1 & H2 & H3);
      [ | llia | llia | exact Hv |].
    - right; right; left. exists ma, mt, fl. rewrite Z2Nat.id by llia. split; [exact Hma | reflexivity].
    - exists bs. rewrite Z2Nat.id in H3 by llia. auto.
  Qed.
End MetaUpd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Spans.
  Variable A : astate.
  Hypothesis HW : WF A.

  (* [comment removed for export] *)
  Lemma slot_fact_bounds : forall ma mt aib slots i st f,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    nth_error slots i = Some st -> In f (slot_fields mt (Z.of_nat i) st) ->
    slot_start mt (Z.of_nat i) - 4 <= f_a f /\ f_a f + f_n f <= slot_end mt (Z.of_nat i) + 1.
  Proof.
    intros ma mt aib slots i st f Hma Hr Hi Hf.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as Hstride.
    unfold slot_fields, slot_fields_g in Hf. unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
    set (S := mt_stride mt) in *. set (M := mt_mem mt) in *.
    apply in_app_iff in Hf. destruct Hf as [Hf | Hf].
    { destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia. }
    destruct st as [ | | off n | ch].
    - destruct Hf.
    - destruct Hf.
    - pose proof (wf_live A HW ma mt aib slots (Z.of_nat i) off n Hma Hr ltac:(rewrite Nat2Z.id; exact Hi) ltac:(llia))
        as (Hoff & Hn & Hfit2 & Hoff16 & _). fold S in Hfit2.
      repeat (apply in_app_iff in Hf; destruct Hf as [Hf | Hf]).
      + destruct (off =? 0) eqn:E; [destruct Hf|]. apply Z.eqb_neq in E.
        destruct Hf as [<- | [<- | [<- | []]]]; cbn [f_a f_n]; llia.
      + destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia.
      + destruct (M + 16 + Z.of_nat i * S + S - 4 - (M + 16 + Z.of_nat i * S + 16 * off) - n <? 5) eqn:E; [destruct Hf|].
        apply Z.ltb_ge in E.
        destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia.
      + destruct (M + 16 + Z.of_nat i * S + S - 4 - (M + 16 + Z.of_nat i * S + 16 * off) - n =? 0) eqn:E; [destruct Hf|].
        apply Z.eqb_neq in E.
        destruct Hf as [<- | []]; cbn [f_a f_n]; llia.
    - destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia.
  Qed.

  Lemma slots_disjoint : forall M S i j, 16 <= S -> 0 <= i -> 0 <= j -> i < j ->
    M + 16 + i * S + S <= M + 16 + j * S.
  Proof. intros M S i j HS Hi Hj Hlt. lnia. Qed.

  (* [comment removed for export] *)
  Lemma span_clear : forall ma mt aib slots i st,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    nth_error slots (Z.to_nat i) = Some st -> 0 <= i -> (st = SIdle \/ st = STaken) ->
    forall f, has A f -> f_a f + f_n f <= slot_start mt i - 3 \/ slot_end mt i <= f_a f.
  Proof.
    intros ma mt aib slots i st Hma Hr Hi Hi0 Hst f Hf.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as Hstride.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    (* [comment removed for export] *)
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hrlo & Hrhi & Hself).
    unfold gext_lo, gext_hi in Hrlo, Hrhi.
    assert (Hprod : 0 <= i * mt_stride mt) by lnia.
    assert (Hspan : mt_mem mt + 16 <= slot_start mt i /\ slot_end mt i + 4 <= mt_mem mt + 16 + mt_cnt mt * mt_stride mt).
    { unfold slot_start, slot_end, slot_start_g, slot_end_g. split; [lnia|].
      assert (i * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by lnia. llia. }
    pose proof (has_addr A HW f Hf) as (Hfn & Hf1 & Hf2 & Hfw).
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - (* [comment removed for export] *) destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as
        (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpgr).
      destruct (Hpgr Hml) as [_ Hheap]. pose proof (has_ctx_where A f Hc) as (C1 & C2 & C3).
      destruct Hc as (k & Hk & ->). cbn in *.
      destruct (heap_avoids_ctx _ _ Hheap k Hk); llia.
    - (* [comment removed for export] *) destruct Har as (pg & Hpga & ->). cbn in *.
      destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); llia.
    - (* [comment removed for export] *) destruct Hm as (ma' & mt' & fl & Hma' & ->). cbn in *.
      pose proof (mfield_range fl).
      destruct (proj1 (wf_meta_dom A HW ma') ltac:(rewrite Hma'; discriminate)) as (pg & k & Hpga & Hk & ->).
      pose proof (meta_addr_range pg k Hk).
      destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); llia.
    - (* [comment removed for export] *)
      destruct Hg as (ma' & mt' & aib' & slots' & Hma' & Hr' & Hin).
      destruct (Z.eq_dec ma' ma) as [-> | Hne].
      + rewrite Hma in Hma'. injection Hma' as <-. rewrite Hr in Hr'. injection Hr' as <- <-.
        destruct Hin as [Hin | (i' & st' & Hi' & Hin)].
        * (* [comment removed for export] *) destruct Hin as [<- | [<- | []]]; cbn; llia.
        * destruct (Nat.eq_dec i' (Z.to_nat i)) as [-> | Hne'].
          -- rewrite Hi in Hi'. injection Hi' as <-. rewrite Z2Nat.id in Hin by llia.
             unfold slot_fields, slot_fields_g in Hin. apply in_app_iff in Hin.
             destruct Hin as [Hin | Hin]; [| destruct Hst as [-> | ->]; destruct Hin].
             unfold slot_start, slot_end.
             destruct Hin as [<- | [<- | []]]; cbn; llia.
          -- pose proof (slot_fact_bounds ma mt aib slots i' st' f Hma Hr Hi' Hin) as (B1 & B2).
             unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
             assert (Hi'lt : (i' < length slots)%nat) by (apply (proj1 (nth_error_Some slots i')); rewrite Hi'; discriminate).
             destruct (Nat.lt_ge_cases i' (Z.to_nat i)) as [Hlt | Hge].
             ++ left. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) (Z.of_nat i') i Hstride ltac:(llia) Hi0 ltac:(llia)). llia.
             ++ right. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i (Z.of_nat i') Hstride Hi0 ltac:(llia) ltac:(llia)). llia.
      + (* [comment removed for export] *)
        pose proof (has_grp_where A HW f ltac:(exists ma', mt', aib', slots'; auto)) as ((mg & mtg & aibg & slg & Hmg & Hrg & Hglo & Hghi) & _).
        (* [comment removed for export] *)
        clear mg mtg aibg slg Hmg Hrg Hglo Hghi.
        assert (Hfin : gext_lo mt' <= f_a f /\ f_a f + f_n f <= gext_hi mt' + 1).
        { destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as
            (Hw32' & _ & Hsc' & Hlen' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
          pose proof (stride_ge16 mt' ltac:(llia) Hsc') as Hstride'.
          destruct Hin as [Hin | (i' & st' & Hi' & Hin)].
          - unfold gext_lo, gext_hi. assert (0 <= mt_cnt mt' * mt_stride mt') by lnia.
            destruct Hin as [<- | [<- | []]]; cbn; llia.
          - pose proof (slot_fields_where A HW ma' mt' aib' slots' i' st' f Hma' Hr' Hi' Hin). llia. }
        destruct (wf_laminar A HW ma mt aib slots ma' mt' aib' slots' Hma Hr Hma' Hr' ltac:(congruence))
          as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
        * unfold gext_lo, gext_hi in *. llia.
        * unfold gext_lo, gext_hi in *. llia.
        * (* [comment removed for export] *)
          assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as E; destruct Hst as [-> | ->]; discriminate).
          unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
          assert (Hjlt : (Z.to_nat j < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat j))); rewrite Hj; discriminate).
          destruct (Z.lt_ge_cases j i) as [Hlt | Hge].
          -- left. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) j i Hstride Hj0 Hi0 Hlt). llia.
          -- right. pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i j Hstride Hi0 Hj0 ltac:(llia)). llia.
        * (* [comment removed for export] *)
          destruct (wf_grp A HW ma' mt' aib' slots' Hma' Hr') as
            (Hw32' & _ & Hsc' & Hlen' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
          pose proof (stride_ge16 mt' ltac:(llia) Hsc') as Hstride'.
          unfold gext_lo, gext_hi in Hjlo, Hjhi.
          destruct Hin as [Hin | (i' & st' & Hi' & Hin)].
          -- left. unfold slot_start, slot_start_g in Hjlo.
             assert (0 <= j * mt_stride mt') by lnia.
             destruct Hin as [<- | [<- | []]]; cbn; llia.
          -- pose proof (slot_fact_bounds ma' mt' aib' slots' i' st' f Hma' Hr' Hi' Hin) as (B1 & B2).
             unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
             assert (Hi'lt : (i' < length slots')%nat) by (apply (proj1 (nth_error_Some slots' i')); rewrite Hi'; discriminate).
             destruct (Z.lt_total (Z.of_nat i') j) as [Hlt | [Heq | Hgt]].
             ++ left. pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') (Z.of_nat i') j Hstride' ltac:(llia) Hj0 Hlt). llia.
             ++ (* [comment removed for export] *)
                rewrite <- Heq, Nat2Z.id in Hj. rewrite Hj in Hi'. injection Hi' as <-.
                unfold slot_fields, slot_fields_g in Hin. apply in_app_iff in Hin.
                destruct Hin as [[<- | [<- | []]] | [<- | [<- | []]]]; cbn [f_a f_n]; unfold slot_start_g, slot_end_g; llia.
             ++ right. pose proof (slots_disjoint (mt_mem mt') (mt_stride mt') j (Z.of_nat i') Hstride' Hj0 ltac:(llia) Hgt). llia.
  Qed.
End Spans.

End WithLayout.
