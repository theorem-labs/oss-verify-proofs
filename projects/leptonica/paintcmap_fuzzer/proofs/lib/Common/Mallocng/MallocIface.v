(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger AllocIface PureModel.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_live MallocInv_tables MallocInv_steps MallocInv_coh
  MallocInv_repw MallocInv_env MallocInv_auxv MallocInv_vm MallocInv_ops.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition alloc_globals (a : word) : Prop := LOCKA <= bv_unsigned a < CTX_END.
Definition in_ro (a : word) : Prop := IMG_LO <= bv_unsigned a < RW_LO.
Definition in_rw (a : word) : Prop := RW_LO <= bv_unsigned a < IMG_HI.
Definition in_image (a : word) : Prop := IMG_LO <= bv_unsigned a < IMG_HI.
(* [comment removed for export] *)
Definition grantable (a : word) : Prop :=
  0x1000 <= bv_unsigned a < alloc_ceiling /\ ~ in_image a.
Definition errno_slot (a : word) : Prop := ERRNO <= bv_unsigned a < ERRNO + 4.
(* [comment removed for export] *)
Definition MMAP_THRESHOLD : Z := 131052.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition covered (vm : VmMaps) (a : Z) : Prop :=
  exists b l, In (b, l) (vm_maps vm) /\ bv_unsigned b <= a < bv_unsigned b + bv_unsigned l.

(* [comment removed for export] *)
Definition ACT48 (A : astate) : Prop := forall c, ~ (0 <= c < 48) -> a_active A c = [].

Record minv (A : astate) (m : word -> option byte) (vm : VmMaps) : Prop := {
  mi_wf : WF A;
  mi_rep : Rep A m;
  mi_vm : VMok A vm;
  (* [comment removed for export] *)
  mi_lock : forall i, 0 <= i < 8 -> m (Z_to_bv 64 (LOCKA + i)) = None;
  (* [comment removed for export] *)
  mi_coh : Coh A m vm;
  (* [comment removed for export] *)
  mi_act : ACT48 A
}.

Definition mlive (A : astate) (p : word) : option Z := a_live A (bv_unsigned p).
Definition mowned (A : astate) (a : word) : Prop := owned_of A (bv_unsigned a).

(* [comment removed for export] *)
Definition mfresh (A : astate) (k : Z) : Prop :=
  (exists l : list Z, NoDup l /\ Z.of_nat (length l) <= k /\
     forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> In ma l) /\
  (forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt = 63 \/ (mt_last mt = 0 /\ exists off, slots = [SLive off 65536])) /\
  (Z.of_nat (length (a_areas A)) <= 1 /\ a_xmaps A = []).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_globals_owned : forall A a, alloc_globals a -> mowned A a.
Proof. intros A a H. unfold mowned, owned_of, alloc_globals, LOCKA, CTX_END in *. left. llia. Qed.

Lemma at_uZ : forall (p : word) i, 0 <= bv_unsigned p + i < 2^64 -> bv_unsigned (at_ p i) = bv_unsigned p + i.
Proof. intros p i H. unfold at_. apply u_lit. exact H. Qed.

Lemma m_live_hull : forall A m vm p n, minv A m vm -> mlive A p = Some n ->
  0 <= n /\ bv_unsigned p mod 16 = 0 /\ bv_unsigned p + round16 n <= alloc_ceiling /\
  forall i, 0 <= i < round16 n ->
    mowned A (at_ p i) /\ m (at_ p i) <> None /\ ~ in_ro (at_ p i) /\ ~ in_rw (at_ p i).
Proof.
  intros A m vm p n [HW HR HV HC HK] Hl. unfold mlive in Hl.
  apply (proj1 (wf_live_map A HW _ _)) in Hl.
  destruct Hl as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
  destruct (live_geom A HW ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & Hq & Hn & Ho & Hfit & Hal & Hpal & G1 & G2 & G3 & G4 & G5 & G6 & G7).
  rewrite <- Ep in *. pose proof (round16_ge n). ceil.
  split; [exact Hn|]. split; [exact Hpal|]. split; [ceil; llia|].
  assert (Hd : forall j, 0 <= j < round16 n -> dom A (bv_unsigned p + j)).
  { intros j Hj. destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & _).
    right; left. exists mr, mtr, aibr, slr. split; [exact Hmr|]. split; [exact Hrr|]. split; [exact Hml|]. unfold gext_lo, gext_hi in *. llia. }
  intros j Hj. unfold mowned, in_ro, in_rw. rewrite !at_uZ by llia.
  split; [right; apply Hd; exact Hj|]. split; [| llia].
  unfold at_. apply (rep_dom A m HR). apply Hd. exact Hj.
Qed.

Lemma m_live_disjoint : forall A m vm p n q k, minv A m vm ->
  mlive A p = Some n -> mlive A q = Some k -> p <> q ->
  bv_unsigned p + round16 n <= bv_unsigned q \/ bv_unsigned q + round16 k <= bv_unsigned p.
Proof.
  intros A m vm p n q k [HW HR HV HC HK] Hp Hq Hpq. unfold mlive in *.
  apply (proj1 (wf_live_map A HW _ _)) in Hp. apply (proj1 (wf_live_map A HW _ _)) in Hq.
  destruct Hp as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
  destruct Hq as (ma' & mt' & aib' & slots' & i' & off' & Hma' & Hr' & Hi0' & Hi' & Eq).
  rewrite Ep, Eq.
  apply (live_disjoint A HW ma mt aib slots i off n ma' mt' aib' slots' i' off' k); try assumption.
  destruct (Z.eq_dec ma ma') as [<- | Hne]; [right | left; exact Hne].
  intros <-. apply Hpq. apply bv_eq. rewrite Ep, Eq.
  rewrite Hma in Hma'. injection Hma' as <-. rewrite Hr in Hr'. injection Hr' as <- <-.
  rewrite Hi in Hi'. injection Hi' as <- <-. reflexivity.
Qed.

Lemma m_live_not_globals : forall A m vm p n i, minv A m vm -> mlive A p = Some n ->
  0 <= i < round16 n -> ~ alloc_globals (at_ p i).
Proof.
  intros A m vm p n i HM Hl Hi Hg.
  destruct (m_live_hull A m vm p n HM Hl) as (_ & _ & _ & Hh).
  destruct (Hh i Hi) as (_ & _ & Hro & Hrw). apply Hrw. unfold alloc_globals, in_rw in *. llia.
Qed.

Lemma m_owned_where : forall A m vm a, minv A m vm -> mowned A a ->
  alloc_globals a \/ (grantable a /\ m a <> None).
Proof.
  intros A m vm a [HW HR HV HC HK] [Hg | Hd].
  - left. unfold alloc_globals, LOCKA, CTX_END in *. llia.
  - right. pose proof (dom_addr A HW _ Hd) as Ha.
    assert (Hh : 0x1000 <= bv_unsigned a /\ (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a)).
    { destruct Hd as [(pg & Hpg & Hx) | [(ma & mt & aib & slots & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx)]].
      - destruct (wf_areas_al A HW pg Hpg) as [_ (H1 & H2 & H3 & H4)]. llia.
      - destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpg).
        destruct (Hpg Hml) as [_ (H1 & H2 & H3 & H4)]. llia.
      - destruct (wf_pages_al A HW pg Hpg) as [_ (H1 & H2 & H3 & H4)]. llia. }
    split; [| rewrite <- (Z_to_bv_bv_unsigned 64 a); apply (rep_dom A m HR); exact Hd].
    unfold grantable, in_image. llia.
Qed.

Lemma m_frame : forall A m m' vm, minv A m vm ->
  (forall a, mowned A a ->
     (forall p n, mlive A p = Some n -> ~ (bv_unsigned p <= bv_unsigned a < bv_unsigned p + n)) ->
     m' a = m a) ->
  (forall a, mowned A a -> m a <> None -> m' a <> None) ->
  (forall a, grantable a -> m' a <> None -> m a <> None) ->
  minv A m' vm.
Proof.
  intros A m m' vm [HW HR HV HC HK H48] Hag Hkeep Hnew. constructor; [exact HW | | exact HV | | | exact H48].
  3:{ apply (coh_frame A m m' vm HK). intros a Hr Hi Hm'. apply Hnew; [| exact Hm']. unfold grantable, in_image. split; [exact Hr | exact Hi]. }
  - constructor.
    + intros x b (f & Hf & Hfb). pose proof Hfb as [Hx ->].
      pose proof (has_addr A HW f Hf) as (Hn & H1 & H2 & Hw).
      assert (Hown : mowned A (Z_to_bv 64 x)).
      { unfold mowned. rewrite uZ by (ceil; llia).
        destruct Hw as [(C1 & C2 & _) | [ (_ & Hnc) | Hh ]].
        - left. unfold LOCKA, CTX_END in *. llia.
        - (* [comment removed for export] *) right.
          destruct Hf as [Hc | [Har | [Hm | Hg]]]; [exact (False_ind _ (Hnc Hc)) | | |].
          + destruct Har as (pg & Hpg & ->). cbn in *. left. exists pg. split; [exact Hpg | llia].
          + destruct (has_meta_where A HW _ Hm) as [(pg & Hpg & Hlo & Hhi) _]. left. exists pg. split; [exact Hpg | cbn in *; llia].
          + destruct (has_grp_root A HW _ Hg) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi).
            right; left. exists mr, mtr, aibr, slr. repeat split; auto; cbn in *; llia.
        - right.
          destruct Hf as [Hc | [Har | [Hm | Hg]]].
          + exfalso. pose proof (has_ctx_where A f Hc). unfold heap_range, LOCKA, CTX_END in *. llia.
          + destruct Har as (pg & Hpg & ->). cbn in *. left. exists pg. split; [exact Hpg | llia].
          + destruct (has_meta_where A HW _ Hm) as [(pg & Hpg & Hlo & Hhi) _]. left. exists pg. split; [exact Hpg | cbn in *; llia].
          + destruct (has_grp_root A HW _ Hg) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi).
            right; left. exists mr, mtr, aibr, slr. repeat split; auto; cbn in *; llia. }
      rewrite <- (rep_facts A m HR x (byte_of (f_v f) (x - f_a f))); [| exists f; auto].
      apply mbyte_ext. apply Hag; [exact Hown|].
      intros p n Hl. unfold mlive in Hl. apply (proj1 (wf_live_map A HW _ _)) in Hl.
      destruct Hl as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
      rewrite uZ by (ceil; llia).
      pose proof (live_clear A HW ma mt aib slots i off n Hma Hr Hi0 Hi f Hf) as Hcl. cbn in Hcl. rewrite <- Ep in Hcl. llia.
    + intros x Hx. pose proof (dom_addr A HW x Hx).
      apply Hkeep; [| apply (rep_dom A m HR); exact Hx]. unfold mowned. rewrite uZ by (ceil; llia). right. exact Hx.
  - intros i Hi. rewrite Hag; [apply HC; exact Hi | |].
    + unfold mowned, owned_of. left. unfold LOCKA, CTX_END. rewrite uZ by llia. llia.
    + intros p n Hl Hin. unfold mlive in Hl. apply (proj1 (wf_live_map A HW _ _)) in Hl.
      destruct Hl as (ma & mt & aib & slots & j & off & Hma & Hr & Hj0 & Hj & Ep).
      destruct (live_geom A HW ma mt aib slots j off n Hma Hr Hj0 Hj) as (q & _ & Hn & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      rewrite <- Ep in *. unfold LOCKA in Hin. rewrite uZ in Hin by llia. pose proof (round16_ge n). llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma WF_A0 : WF A0.
Proof.
  assert (Hdll : dll A0 []) by (intros k x H; destruct k; discriminate).
  constructor; cbn.
  all: try (intros; discriminate).
  all: try (intros; llia).
  all: try (unfold ctx0; llia).
  all: try exact Hdll.
  - constructor.
  - intros ma. split; [intros H; exfalso; apply H; reflexivity | intros (pg & k & [] & _)].
  - unfold ctx0. intros _. repeat split; auto.
  - constructor.
  - intros _. split; [intros [] | intros (mt & H & _); discriminate].
  - intros _. constructor.
  - intros _ _. exact Hdll.
  - intros p n. split; [discriminate | intros (ma & mt & aib & slots & i & off & H & _); discriminate].
  - intros _. repeat split; reflexivity.
Qed.

Lemma Rep_A0 : forall m, (forall a, LOCKA <= bv_unsigned a < CTX_END -> m a = None) -> Rep A0 m.
Proof.
  intros m Hm. constructor.
  - intros x b (f & Hf & [Hx ->]).
    destruct Hf as [(k & Hk & ->) | [(pg & [] & _) | [(ma & mt & fl & H & _) | (ma & mt & aib & slots & H & _)]]]; try discriminate.
    cbn in *. pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    replace (byte_of 0 (x - caddr k)) with 0 by (unfold byte_of; rewrite Z.div_0_l by llia; reflexivity).
    apply mbyte_ctx_image; [unfold LOCKA, CTX_END; llia|]. apply Hm. rewrite uZ by llia. llia.
  - intros x [(pg & [] & _) | [(ma & mt & aib & slots & H & _) | (pg & [] & _)]]; discriminate.
Qed.

Lemma VMok_A0 : forall h,
  vm_maps h = [] -> vm_noaccess h = [] -> vm_reserved h = segments_reserved ml_segs ->
  vm_start_brk h = vm_brk h -> valid_brk ml_segs (vm_brk h) -> alloc_top h = alloc_ceiling ->
  VMok A0 h.
Proof. exact VMok_init. Qed.

(* [comment removed for export] *)
Lemma minv_init : forall m h,
  vm_maps h = [] -> vm_noaccess h = [] -> vm_reserved h = segments_reserved ml_segs ->
  vm_start_brk h = vm_brk h -> valid_brk ml_segs (vm_brk h) -> alloc_top h = alloc_ceiling ->
  (forall a, LOCKA <= bv_unsigned a < CTX_END -> m a = None) ->
  (forall a, grantable a -> m a = None) ->
  minv A0 m h.
Proof.
  intros m h Hm Hn Hr Hsb Hbrk Htop Hctx Hheap. constructor.
  - apply WF_A0.
  - apply Rep_A0. exact Hctx.
  - apply VMok_A0; assumption.
  - intros i Hi. apply Hctx. pose proof layout_nums. rewrite uZ by lia. lia.
  - apply coh_init. intros a Hr' Hi. apply Hheap. unfold grantable, in_image. split; [exact Hr' | exact Hi].
  - intros c Hc. reflexivity.
Qed.

Lemma mfresh_A0 : mfresh A0 0.
Proof.
  split; [| split].
  - exists []. split; [constructor|]. split; [cbn; llia|]. intros ma mt aib slots H. discriminate.
  - intros ma mt aib slots H. discriminate.
  - split; [cbn; llia | reflexivity].
Qed.

Lemma mfresh_mono : forall A k k', mfresh A k -> k <= k' -> mfresh A k'.
Proof.
  intros A k k' [(l & H1 & H2 & H3) H4] Hle. split; [| exact H4]. exists l. repeat split; auto. llia.
Qed.

Lemma m_init_owned : forall a, mowned A0 a <-> alloc_globals a.
Proof.
  intros a. split; [| apply m_globals_owned].
  intros [Hg | Hd]; [exact Hg|].
  destruct Hd as [(pg & Hin & _) | [(ma & mt & aib & slots & Hma & _) | (pg & Hin & _)]]; [destruct Hin | discriminate | destruct Hin].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint treach {T : Type} (t : itree T) (Q : T -> mstate -> Prop) : Prop :=
  match t with
  | TRet a s => Q a s
  | TCrash => False
  | TBrk req vm kf ko =>
      (brk_grow_ok_vm vm req req = false /\ treach kf Q) \/ (brk_grow_ok_vm vm req req = true /\ treach ko Q)
  | TMmap k len vm kf ko =>
      (mmap_refusable_k k vm (page_round_up_Z (bv_unsigned len)) = true /\ treach kf Q)
      \/ exists a, mmap_grant_ok k vm a (page_round_up_Z (bv_unsigned len)) = true /\ treach (ko a) Q
  | TMmapFixed addr len k1 k2 k3 => treach k2 Q
  | TMprot addr len vm kf ko =>
      (mprot_ok_vm vm addr (page_round_up len) = false /\ treach kf Q)
      \/ (mprot_ok_vm vm addr (page_round_up len) = true /\ treach ko Q)
  end.

Lemma treach_mono : forall {T} (t : itree T) (Q Q' : T -> mstate -> Prop),
  (forall a s, Q a s -> Q' a s) -> treach t Q -> treach t Q'.
Proof.
  intros T t; induction t; intros Q Q' HQ Hr; cbn in *.
  - apply HQ. exact Hr.
  - exact Hr.
  - destruct Hr as [[Hb Hr] | [Hb Hr]]; [left; split; [exact Hb | eapply IHt1; eauto] | right; split; [exact Hb | eapply IHt2; eauto]].
  - destruct Hr as [[Hrf Hr] | (a & Hg & Hr)]; [left; split; [exact Hrf | eapply IHt; eauto] | right; exists a; split; [exact Hg | eapply H; eauto]].
  - eapply IHt2; eauto.
  - destruct Hr as [[Hb Hr] | [Hb Hr]]; [left; split; [exact Hb | eapply IHt1; eauto] | right; split; [exact Hb | eapply IHt2; eauto]].
Qed.

Lemma treach_bind : forall {T U} (t : itree T) (f : T -> M U) (Q : T -> mstate -> Prop) (Q' : U -> mstate -> Prop),
  treach t Q -> (forall a s, Q a s -> treach (f a s) Q') -> treach (tbind t f) Q'.
Proof.
  intros T U t; induction t; intros f Q Q' Hr Hf; cbn in *.
  - apply Hf. exact Hr.
  - exact Hr.
  - destruct Hr as [[Hb Hr] | [Hb Hr]]; [left; split; [exact Hb | eapply IHt1; eauto] | right; split; [exact Hb | eapply IHt2; eauto]].
  - destruct Hr as [[Hrf Hr] | (a & Hg & Hr)]; [left; split; [exact Hrf | eapply IHt; eauto] | right; exists a; split; [exact Hg | eapply H; eauto]].
  - eapply IHt2; eauto.
  - destruct Hr as [[Hb Hr] | [Hb Hr]]; [left; split; [exact Hb | eapply IHt1; eauto] | right; split; [exact Hb | eapply IHt2; eauto]].
Qed.

(* [comment removed for export] *)
Lemma tshape_from_leaf : forall {T} (t : itree T) (L : T -> mstate -> TSet) tr,
  tshape t L tr -> tr = [] \/ exists a s, L a s tr.
Proof.
  intros T t; induction t; intros L tr Ht; cbn in *.
  - right. exists a, s. exact Ht.
  - left. exact Ht.
  - destruct Ht as [[_ Ht] | [_ Ht]]; eauto.
  - destruct Ht as [[_ Ht] | (a & _ & Ht)]; eauto.
  - eauto.
  - destruct Ht as [[_ Ht] | [_ Ht]]; eauto.
Qed.

(* [comment removed for export] *)
Lemma tshape_sup : forall {T} (t : itree T) (L : T -> mstate -> TSet) (S : TSet),
  treach t (fun a s => t_eq (L a s) S) -> forall tr, S tr -> tshape t L tr.
Proof.
  intros T t; induction t; intros L S Hr tr Htr; cbn in *.
  - apply (proj2 (Hr tr)). exact Htr.
  - destruct Hr.
  - destruct Hr as [[Hb Hr] | [Hb Hr]]; [left; split; [exact Hb | eapply IHt1; eauto] | right; split; [exact Hb | eapply IHt2; eauto]].
  - destruct Hr as [[Hrf Hr] | (a & Hg & Hr)]; [left; split; [exact Hrf | eapply IHt; eauto] | right; exists a; split; [exact Hg | eapply H; eauto]].
  - eapply IHt2; eauto.
  - destruct Hr as [[Hb Hr] | [Hb Hr]]; [left; split; [exact Hb | eapply IHt1; eauto] | right; split; [exact Hb | eapply IHt2; eauto]].
Qed.

(* [comment removed for export] *)
Lemma tshape_alt2 : forall {T} (t : itree T) (L : T -> mstate -> TSet) (S1 S2 : TSet),
  S1 [] ->
  (forall a s, t_eq (L a s) S1 \/ t_eq (L a s) S2) ->
  treach t (fun a s => t_eq (L a s) S1) -> treach t (fun a s => t_eq (L a s) S2) ->
  t_eq (tshape t L) (t_alt2 S1 S2).
Proof.
  intros T t L S1 S2 Hnil HL H1 H2 tr. unfold t_alt2. split.
  - intros Ht. destruct (tshape_from_leaf t L tr Ht) as [-> | (a & s & Hl)]; [left; exact Hnil|].
    destruct (HL a s) as [E | E]; [left | right]; apply (proj1 (E tr)); exact Hl.
  - intros [Htr | Htr]; [eapply (tshape_sup t L S1 H1) | eapply (tshape_sup t L S2 H2)]; exact Htr.
Qed.

(* [comment removed for export] *)
Lemma tsafe_tshape_leaf : forall {T} (t : itree T) (P : T -> mstate -> Prop) (L : T -> mstate -> TSet) tr,
  tsafe t P -> tshape t L tr -> exists a s, P a s /\ L a s tr.
Proof.
  intros T t; induction t; intros P L tr Hs Ht; cbn in *.
  - exists a, s. split; assumption.
  - destruct Hs.
  - destruct Hs as [H1 H2]. destruct Ht as [[Hb Ht] | [Hb Ht]]; [eapply IHt1; eauto | eapply IHt2; eauto].
  - destruct Hs as [H1 H2]. destruct Ht as [[Hrf Ht] | (a & Hg & Ht)]; [eapply IHt; eauto | eapply H; eauto].
  - eapply IHt2; eauto.
  - destruct Hs as [H1 H2]. destruct Ht as [[Hb Ht] | [Hb Ht]]; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

(* [comment removed for export] *)
Lemma tshape_const_rz : forall {fx : FPState} {T} (t : itree T) (S : TSet) (P : T -> mstate -> Prop) C,
  tsafe t P -> realizes ml_segs C (tshape t (fun _ _ => S)) -> realizes ml_segs C S.
Proof.
  intros fx T t S P C Hs Hr.
  destruct (tsafe_tshape_leaf t P (fun _ _ => S) [] Hs (realizes_nonempty _ _ _ Hr)) as (a & s & _ & Hnil).
  eapply rz_conseq; [exact Hr | apply (tshape_const t S P Hnil Hs)].
Qed.

(* [comment removed for export] *)
Lemma tsafe_treach_leaf : forall {T} (t : itree T) (P Q : T -> mstate -> Prop),
  tsafe t P -> treach t Q -> exists a s, P a s /\ Q a s.
Proof.
  intros T t; induction t; intros P Q Hs Hr; cbn in *.
  - exists a, s. split; assumption.
  - destruct Hr.
  - destruct Hs as [H1 H2]. destruct Hr as [[Hb Hr] | [Hb Hr]]; [eapply IHt1; eauto | eapply IHt2; eauto].
  - destruct Hs as [H1 H2]. destruct Hr as [[Hrf Hr] | (a & Hg & Hr)]; [eapply IHt; eauto | eapply H; eauto].
  - eapply IHt2; eauto.
  - destruct Hs as [H1 H2]. destruct Hr as [[Hb Hr] | [Hb Hr]]; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

(* [comment removed for export] *)
Lemma tshape_alt2_rz : forall {fx : FPState} {T} (t : itree T) (L : T -> mstate -> TSet) (S1 S2 : TSet) (P : T -> mstate -> Prop) C,
  tsafe t P -> (forall a s, P a s -> L a s []) ->
  (forall a s, t_eq (L a s) S1 \/ t_eq (L a s) S2) ->
  treach t (fun a s => t_eq (L a s) S1) -> treach t (fun a s => t_eq (L a s) S2) ->
  realizes ml_segs C (tshape t L) -> realizes ml_segs C (t_alt2 S1 S2).
Proof.
  intros fx T t L S1 S2 P C Hs Hnil HL H1 H2 Hr.
  destruct (tsafe_treach_leaf t P _ Hs H1) as (a & s & HP & E).
  pose proof (proj1 (E []) (Hnil a s HP)) as Hnil1.
  eapply rz_conseq; [exact Hr | apply (tshape_alt2 t L S1 S2 Hnil1 HL H1 H2)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma minv_agree : forall A m m' vm,
  minv A m vm -> (forall a : word, bv_unsigned a < alloc_ceiling -> m' a = m a) -> minv A m' vm.
Proof.
  intros A m m' vm [HW HR HV HC HK H48] Hag. constructor; [exact HW | | exact HV | | exact (coh_agree A m m' vm HK Hag) | exact H48].
  - constructor.
    + intros x b Hf. rewrite <- (rep_facts A m HR x b Hf). apply mbyte_ext. apply Hag.
      pose proof (facts_addr A HW x b Hf). rewrite uZ by (ceil; llia). llia.
    + intros x Hd. rewrite Hag; [apply (rep_dom A m HR); exact Hd|].
      pose proof (dom_addr A HW x Hd). rewrite uZ by (ceil; llia). llia.
  - intros i Hi. rewrite Hag; [apply HC; exact Hi|]. unfold LOCKA. rewrite uZ by llia. ceil. llia.
Qed.

(* [comment removed for export] *)
Definition call_state (mm : word -> option byte) (md : Model) (sp : word) : mstate :=
  MS mm (m_vmmaps md) (bv_unsigned sp - ALLOC_STACK) (bv_unsigned sp).

(* [comment removed for export] *)
Definition zslot (mt : meta_rec) : Prop := 48 <= mt_sc mt \/ mt_stride mt < 16 * size_class (mt_sc mt).
Definition zgroup (A : astate) (p : Z) : Prop :=
  exists ma mt aib slots j off n, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ 0 <= j /\
    nth_error slots (Z.to_nat j) = Some (SLive off n) /\ p = slot_start mt j + 16 * off /\ zslot mt.

(* [comment removed for export] *)
Definition vm_fixed (h h' : VmMaps) : Prop :=
  vm_limit h' = vm_limit h /\ alloc_top h' = alloc_top h /\ vm_init_sp h' = vm_init_sp h /\ vm_reserved h' = vm_reserved h.

(* [comment removed for export] *)
Definition free_post (A : astate) (p : word) (s : mstate) : unit -> mstate -> Prop :=
  fun _ s' => exists A',
    minv A' (ms_mem s') (ms_vm s') /\ ms_lo s' = ms_lo s /\ ms_hi s' = ms_hi s /\
    mlive A' p = None /\ (forall q, q <> p -> mlive A' q = mlive A q) /\
    (forall a : word, ~ mowned A a -> ~ mowned A' a -> ~ errno_slot a -> ms_mem s' a = ms_mem s a) /\
    (forall q k i, mlive A' q = Some k -> 0 <= i < k -> ms_mem s' (at_ q i) = ms_mem s (at_ q i)) /\
    (forall a : word, ms_mem s a <> None -> mowned A a \/ ms_mem s' a <> None) /\
    vm_fixed (ms_vm s) (ms_vm s') /\ vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s).

Definition malloc_post (A : astate) (n : Z) (s : mstate) : word -> mstate -> Prop :=
  fun res s' => exists A',
    minv A' (ms_mem s') (ms_vm s') /\ ms_lo s' = ms_lo s /\ ms_hi s' = ms_hi s /\
    ( (res = Z_to_bv 64 0 /\ (forall q, mlive A' q = mlive A q))
      \/ (bv_unsigned res <> 0 /\ mlive A res = None /\ mlive A' res = Some n /\
          (forall q, q <> res -> mlive A' q = mlive A q) /\
          (forall i, 0 <= i < round16 n -> mowned A (at_ res i) \/ ms_mem s (at_ res i) = None) /\
          (zgroup A' (bv_unsigned res) -> forall i, 0 <= i < n -> ms_mem s' (at_ res i) = Some (Z_to_bv 8 0))) ) /\
    (forall a : word, ~ mowned A a -> ~ mowned A' a -> ~ errno_slot a -> ms_mem s' a = ms_mem s a) /\
    (forall q k i, mlive A q = Some k -> 0 <= i < k -> ms_mem s' (at_ q i) = ms_mem s (at_ q i)) /\
    (forall a : word, ms_mem s a <> None -> bv_unsigned a < IMG_HI \/ mowned A a \/ ms_mem s' a <> None) /\
    vm_fixed (ms_vm s) (ms_vm s').

(* [comment removed for export] *)
Record call_env (A : astate) (s : mstate) (sp0 : word) (argv envp : list (list byte)) : Prop := {
  ce_inv : minv A (ms_mem s) (ms_vm s);
  ce_win : WIN s;
  ce_env : EnvOK sp0 argv envp s
}.

End WithLayout.
