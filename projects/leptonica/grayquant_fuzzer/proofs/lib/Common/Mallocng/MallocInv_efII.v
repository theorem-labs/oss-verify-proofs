(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_usage MallocInv_ops
  MallocInv_enframe MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_freetop.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

Lemma upd_ext : forall s s', ms_vm s' = ms_vm s -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s -> s' = upd s (ms_mem s') (ms_vm s).
Proof. intros [m h lo hi] [m' h' lo' hi']; cbn; intros -> -> ->; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma taken_span_nolive : forall A g mt aib slots i p n x,
  WF A -> a_meta A g = Some mt -> mt_role mt = RGroup aib slots ->
  nth_error slots (Z.to_nat i) = Some STaken -> 0 <= i ->
  a_live A p = Some n -> p <= x < p + n ->
  ~ (slot_start mt i - 4 <= x < slot_end mt i).
Proof.
  intros A g mt aib slots i p n x HW Hg Hr Hi Hi0 Hp Hx Hin.
  apply (proj1 (wf_live_map A HW p n)) in Hp.
  destruct Hp as (mb & mtb & aibb & slb & j & off & Hmb & Hrb & Hj0 & Hj & ->).
  destruct (live_geom A HW mb mtb aibb slb j off n Hmb Hrb Hj0 Hj) as (q & Hq & Hn & Hoff & Hfit & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (round16_ge n) as Hr16.
  destruct (wf_grp A HW g mt aib slots Hg Hr) as (Hw32 & _ & Hsc & Hlen & _). pose proof (stride_ge16 mt ltac:(lia) Hsc) as HS.
  destruct (wf_grp A HW mb mtb aibb slb Hmb Hrb) as (Hw32b & _ & Hscb & Hlenb & _). pose proof (stride_ge16 mtb ltac:(lia) Hscb) as HSb.
  assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
  pose proof (w_last_range (mt_w32 mt)) as Hl.
  assert (Hic : i + 1 <= mt_cnt mt) by (unfold mt_cnt, mt_last in *; lia).
  assert (Gi : gext_lo mt + 16 <= slot_start mt i /\ slot_end mt i <= gext_hi mt + 4).
  { unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g.
    assert (0 <= i * mt_stride mt /\ i * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by nia. lia. }
  destruct (Z.eq_dec g mb) as [<- | Hne].
  - rewrite Hg in Hmb. injection Hmb as <-. rewrite Hr in Hrb. injection Hrb as <- <-.
    destruct (Z.lt_total j i) as [Hlt | [-> | Hgt]].
    + pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) j i HS Hj0 Hi0 Hlt). unfold slot_start, slot_end, slot_start_g, slot_end_g in *. lia.
    + rewrite Hi in Hj. discriminate.
    + pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i j HS Hi0 Hj0 Hgt). unfold slot_start, slot_end, slot_start_g, slot_end_g in *. lia.
  - destruct (wf_laminar A HW g mt aib slots mb mtb aibb slb Hg Hr Hmb Hrb Hne)
      as [Hd | [Hd | [ (k & ch & Hk0 & Hk & Hklo & Hkhi) | (k & ch & Hk0 & Hk & Hklo & Hkhi) ]]].
    + unfold gext_lo, gext_hi in *. lia.
    + unfold gext_lo, gext_hi in *. lia.
    + (* [comment removed for export] *)
      assert (Hki : k <> i) by (intros ->; rewrite Hi in Hk; discriminate).
      unfold slot_start, slot_end, slot_start_g, slot_end_g, gext_lo, gext_hi in *.
      destruct (Z.lt_total k i) as [Hlt | [E | Hgt]]; [| exact (Hki E) |].
      * pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) k i HS Hk0 Hi0 Hlt). lia.
      * pose proof (slots_disjoint (mt_mem mt) (mt_stride mt) i k HS Hi0 Hk0 Hgt). lia.
    + (* [comment removed for export] *)
      assert (Hkj : k <> j) by (intros ->; rewrite Hj in Hk; discriminate).
      unfold slot_start, slot_end, slot_start_g, slot_end_g, gext_lo, gext_hi in *.
      destruct (Z.lt_total k j) as [Hlt | [E | Hgt]]; [| exact (Hkj E) |].
      * pose proof (slots_disjoint (mt_mem mtb) (mt_stride mtb) k j HSb Hk0 Hj0 Hlt). lia.
      * pose proof (slots_disjoint (mt_mem mtb) (mt_stride mtb) j k HSb Hj0 Hk0 Hgt). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EnframeII.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (g : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i nn : Z) (ctr : word).
  Hypothesis Hg : a_meta A g = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hnn : 0 <= nn /\ nn + 4 <= mt_stride mt /\ mt_stride mt - nn < 2^20.

  Theorem enframe_II : forall (k : word -> M R) P,
    (forall (off : Z) s', 0 <= off <= (mt_stride mt - nn - 4) / 16 ->
       let p := slot_start mt i + 16 * off in
       let A' := slot_set A g i (SLive off nn) (lupd (a_live A) p (Some nn)) in
       II sp0 argv envp cb D A' s' -> ntframe A s s' ->
       (forall a : word, u a < slot_start mt i - 3 \/ slot_end mt i <= u a -> ms_mem s' a = ms_mem s a) ->
       (forall a : word, p <= u a < p + nn -> ms_mem s' a = ms_mem s a) ->
       tsafe (k (Z_to_bv 64 p) s') P) ->
    tsafe ((x <- m_enframe (Z_to_bv 64 g) (Z_to_bv 64 i) (Z_to_bv 64 nn) ctr ;; k x) s) P.
  Proof.
    intros k P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG]. pose proof (envok_rodata _ _ _ _ HE) as HRO.
    apply (enframe_ok A s g mt aib slots i nn ctr HW HR HWIN HRO Hg Hr Hi Hi0 Hnn k P).
    intros off s' Hoff. cbv zeta. intros HW' HR' HWIN' Hvm Hlo Hhi HRO' Hfr Hpay.
    set (p := mt_mem mt + 16 + i * mt_stride mt + 16 * off) in *.
    set (A' := slot_set A g i (SLive off nn) (lupd (a_live A) p (Some nn))) in *.
    change (mt_mem mt + 16 + i * mt_stride mt) with (slot_start mt i) in *.
    change (slot_start mt i + mt_stride mt - 4) with (slot_end mt i) in *.
    pose proof (upd_ext s s' Hvm Hlo Hhi) as Es.
    assert (Gd : forall x, slot_start mt i - 4 <= x < slot_end mt i + 4 -> dom A x).
    { intros x Hx. destruct (wf_grp A HW g mt aib slots Hg Hr) as (Hw32 & _ & Hsc & Hlen & _). pose proof (stride_ge16 mt ltac:(lia) Hsc) as HS.
      assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
      pose proof (w_last_range (mt_w32 mt)) as Hl. assert (Hic : i + 1 <= mt_cnt mt) by (unfold mt_cnt, mt_last in *; lia).
      apply (grp_dom A g mt aib slots x HW Hg Hr). unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g in *.
      assert (0 <= i * mt_stride mt /\ i * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by nia. lia. }
    assert (FRM : forall a : word, ms_mem s' a = ms_mem s a \/ (slot_start mt i - 4 <= u a < slot_end mt i /\ dom A (u a))).
    { intros a. destruct (Z.lt_ge_cases (u a) (slot_start mt i - 3)) as [H1 | H1]; [left; apply Hfr; left; exact H1|].
      destruct (Z.lt_ge_cases (u a) (slot_end mt i)) as [H2 | H2]; [| left; apply Hfr; right; exact H2].
      right. split; [lia|]. apply Gd. lia. }
    assert (A'_meta : forall x, a_meta A' x = if Z.eq_dec x g then Some (MT (mt_f mt) (RGroup aib (list_set slots (Z.to_nat i) (SLive off nn)))) else a_meta A x).
    { intros x. unfold A', slot_set. rewrite Hg, Hr. cbn [a_meta set_live ameta_upd set_meta]. unfold aupd. reflexivity. }
    assert (DOM' : forall x, dom A x -> dom A' x).
    { intros x Hd. unfold dom. replace (a_areas A') with (a_areas A) by (unfold A', slot_set; rewrite Hg, Hr; reflexivity).
      replace (a_pages A') with (a_pages A) by (unfold A', slot_set; rewrite Hg, Hr; reflexivity).
      destruct Hd as [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      destruct (Z.eq_dec y g) as [-> | Hne].
      - rewrite Hg in Hy. injection Hy as <-. rewrite Hr in Hry. injection Hry as <- <-.
        eexists g, _, aib, _. rewrite A'_meta. destruct (Z.eq_dec g g); [| contradiction]. split; [reflexivity|]. split; [reflexivity|]. exact (conj Hml Hx).
      - exists y, mty, aiby, sly. rewrite A'_meta. destruct (Z.eq_dec y g); [contradiction|]. auto. }
    apply HK; [exact Hoff | | | exact Hfr | exact Hpay].
    - (* [comment removed for export] *)
      rewrite Es. apply II_intro.
      + apply (IS_mem sp0 argv envp cb A A' s (ms_mem s') HI HW' HR').
        * intros a. destruct (FRM a) as [E | [_ Hd]]; [left; exact E | right; exact (dom_mzone A _ HW Hd)].
        * intros a Ha. destruct (FRM a) as [E | [_ Hd]]; [left; rewrite <- E; exact Ha | left].
          rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (rep_dom A _ HR _ Hd).
      + cbn [ms_vm upd]. apply (VMok_transfer A A' (ms_vm s) (ii_vm HII)); try (unfold A', slot_set; rewrite Hg, Hr; reflexivity).
        * intros x mtx aibx slx Hx Hrx Hml. rewrite A'_meta in Hx. destruct (Z.eq_dec x g) as [-> | Hne].
          -- injection Hx as <-. exists mt, aib, slots. auto.
          -- exists mtx, aibx, slx. auto.
        * intros x mt0 aib0 sl0 Hx0 Hr0 Hml. rewrite A'_meta. destruct (Z.eq_dec x g) as [-> | Hne].
          -- rewrite Hg in Hx0. injection Hx0 as <-. eexists _, aib, _. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
          -- exists mt0, aib0, sl0. auto.
      + apply (AvOK_transfer A A' (ii_av HII)); try (unfold A', slot_set; rewrite Hg, Hr; reflexivity).
        intros x mt' Hx Hrl. rewrite A'_meta in Hx. destruct (Z.eq_dec x g) as [-> | Hne]; [injection Hx as <-; cbn in Hrl; discriminate | exists mt'; auto].
      + apply (UsOK_transfer A A' (ii_us HII)); [unfold A', slot_set; rewrite Hg, Hr; reflexivity | intros; unfold A', slot_set; rewrite Hg, Hr; reflexivity |].
        intros c x. unfold meta_usage. rewrite A'_meta. destruct (Z.eq_dec x g) as [-> | Hne]; [| reflexivity]. rewrite Hg, Hr. reflexivity.
      + apply (deads_transfer A A' D (ii_dd HII)). intros x. rewrite A'_meta. destruct (Z.eq_dec x g) as [-> | Hne]; [| tauto].
        rewrite Hg. split; intros (mt' & Hx & Hrl); injection Hx as <-; [cbn in Hrl; discriminate | rewrite Hr in Hrl; discriminate].
    - (* [comment removed for export] *)
      rewrite Es. constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd]; try reflexivity.
      + intros a Hno. destruct (FRM a) as [E | [_ Hd]]; [exact E | exfalso; exact (Hno (or_intror Hd))].
      + intros q n a Hq Hqa. destruct (FRM a) as [E | [Hin _]]; [exact E | exfalso].
        exact (taken_span_nolive A g mt aib slots i q n (u a) HW Hg Hr Hi Hi0 Hq Hqa Hin).
      + intros a Ha. destruct (FRM a) as [E | [_ Hd]]; [rewrite E; exact Ha|].
        rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (rep_dom A' _ HR' _ (DOM' _ Hd)).
  Qed.
End EnframeII.

End WithLayout.
