(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_vmops MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_hints MallocInv_sc
  MallocInv_ameta_iface MallocInv_ameta5 MallocInv_ntpost
  MallocInv_aslot_iface MallocInv_ametax_iface MallocInv_malloc_iface MallocInv_agm2 MallocInv_mal1 MallocInv_mal3 MallocInv_mal4 MallocInv_mal5 MallocIfaceX.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_okW : alloc_slot_specW -> malloc_specW.
Proof.
  intros AS W R sp0 argv envp cb A s sp n K P HII Hxm Hact Hlock Hn HL.
  rewrite m_malloc_eq. unfold wlit, MMAP_THRESHOLD_W, wlit.
  rewrite c_ltu_Z by (clear - Hn; lia). replace (n <? 0x7fffffffffffefff) with true by (symmetry; apply Z.ltb_lt; clear - Hn; lia). cbv beta iota.
  rewrite c_ltu_Z by (clear - Hn; lia).
  destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hsmall | Hbig].
  - replace (n <? 131052) with true by (symmetry; apply Z.ltb_lt; clear - Hsmall; unfold MMAP_THRESHOLD in Hsmall; lia). cbv beta iota.
    apply (mal_small_ok W AS sp0 argv envp cb A s sp n K P HII Hxm Hact ltac:(clear - Hn Hsmall; lia)). exact HL.
  - replace (n <? 131052) with false by (symmetry; apply Z.ltb_ge; clear - Hbig; unfold MMAP_THRESHOLD in Hbig; lia). cbv beta iota.
    apply (mal_big_ok W sp0 argv envp cb A s sp n K P HII Hxm Hact ltac:(clear - Hn Hbig; lia)). exact HL.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma II_of_call_env : forall A s sp0 argv envp cb,
  call_env A s sp0 argv envp -> GRD cb (ms_mem s) -> II sp0 argv envp cb [] A s.
Proof.
  intros A s sp0 argv envp cb [HM HWIN HE] Hcb. pose proof HM as [HW HR HV HL HC H48]. pose proof HC as [Ccov Cnd Cus Cav].
  apply II_intro.
  - constructor; [exact HW | exact HR | exact (covm_of_coh _ _ _ HC) | exact HWIN | exact HE | exact Hcb].
  - exact HV.
  - exact Cav.
  - exact Cus.
  - intros x. split; [| intros []]. intros (mt' & Hx & Hrl). exact (Cnd x mt' Hx Hrl).
Qed.

Lemma minv_of_II : forall sp0 argv envp cb A s,
  II sp0 argv envp cb [] A s -> ACT48 A -> minv A (ms_mem s) (ms_vm s).
Proof.
  intros sp0 argv envp cb A s HII H48. pose proof (ii_is HII) as HIS. pose proof HIS as [HW HR HC HWIN HE HG].
  constructor; [exact HW | exact HR | exact (ii_vm HII) | exact (eo_lock _ _ _ _ HE) | | exact H48].
  constructor; [exact HC | | exact (ii_us HII) | exact (ii_av HII)].
  intros x mtx Hx Hrl. exact (proj1 (ii_dd HII x) (ex_intro _ mtx (conj Hx Hrl))).
Qed.

Lemma malloc_leafX : forall sp0 argv envp cb A s n s' A' (res : word),
  II sp0 argv envp cb [] A s ->
  II sp0 argv envp cb [] A' s' -> FR A s A' s' -> a_xmaps A' = [] -> ACT48 A' ->
  malloc_vm A n s s' -> malloc_rel A A' n res (ms_mem s) s' ->
  (* [comment removed for export] *)
  malloc_growS n A A' s s' -> (u res = 0 -> malloc_noroomS sp0 argv envp cb n A s) ->
  malloc_postX A n s res s'.
Proof.
  intros sp0 argv envp cb A s n s' A' res HII HII' HFR Hxm' H48' HVM HREL HGS HNS.
  pose proof (ii_is HII) as [HW _ _ _ _ _].
  pose proof (ii_is HII') as HIS'. pose proof HIS' as [HW' HR' HC' HWIN' HE' HG']. pose proof layout_nums as LN.
  pose proof HFR as [Flo Fhi Fown Fmem Flive Flm Fmap Flim].
  exists A'. split; [exact Hxm'|]. split; [exact (minv_of_II sp0 argv envp cb A' s' HII' H48')|].
  split; [exact Flo|]. split; [exact Fhi|]. split; [| split; [| split; [| split]]].
  - destruct HREL as [[H0 HF] | (Hnz & g & idx & off & HO)].
    + left. split; [apply bv_eq; rewrite H0; reflexivity|]. intros q. unfold mlive. rewrite (mf_live _ _ _ HF). reflexivity.
    + right. split; [exact Hnz|]. split; [exact (mo_fresh _ _ _ _ _ _ _ _ _ HO)|].
      pose proof (mo_live _ _ _ _ _ _ _ _ _ HO (u res)) as HL'. destruct (Z.eq_dec (u res) (u res)); [| contradiction].
      destruct (live_heap A' (u res) n HW' HL') as (Hn0 & Hlo & Hce & Himg & Hdom). ceil. pose proof (round16_ge n) as R16.
      assert (Eat : forall i, 0 <= i < round16 n -> u (at_ res i) = u res + i) by (intros i Hi; unfold at_; rewrite uZ by lia; reflexivity).
      split; [unfold mlive; exact HL'|].
      split. { intros q Hq. unfold mlive. rewrite (mo_live _ _ _ _ _ _ _ _ _ HO). destruct (Z.eq_dec (u q) (u res)) as [E | NE]; [exfalso; apply Hq; apply bv_eq; exact E | reflexivity]. }
      split.
      * (* [comment removed for export] *)
        intros i Hi. pose proof (Hdom (u res + i) ltac:(lia)) as Hd'.
        destruct (mk_newdom _ _ _ (mo_keep _ _ _ _ _ _ _ _ _ HO) (u res + i) Hd') as [Hd | [Hnone | (pg & Hpg & Hx)]].
        -- left. right. rewrite (Eat i Hi). exact Hd.
        -- right. rewrite <- (Eat i Hi), Z_to_bv_bv_unsigned in Hnone. exact Hnone.
        -- exfalso.
           pose proof (proj1 (wf_live_map A' HW' _ _) HL') as (ma & mt & aib & slots & j & off' & Hma & Hr & Hj0 & Hj & Ep).
           destruct (live_geom A' HW' ma mt aib slots j off' n Hma Hr Hj0 Hj) as (q & Hq & _ & Ho & Hfit & _ & _ & G1 & G2 & G3 & G4 & G5 & G6 & G7).
           rewrite <- Ep in *.
           destruct (wf_grp_root A' HW' ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Rlo & Rhi & _).
           destruct Hpg as [Hpg | Hpg].
           ++ destruct (wf_disj_area_grp A' HW' pg mr mtr aibr slr Hpg Hmr Hrr Hml); lia.
           ++ destruct (wf_disj_page_grp A' HW' pg mr mtr aibr slr Hpg Hmr Hrr Hml); lia.
      * intros Hz i Hi. apply (mo_zero _ _ _ _ _ _ _ _ _ HO Hz). rewrite (Eat i) by lia. lia.
  - intros a Ho Ho' Herr. apply (Fmem a); [intros H; exact (Ho' H) | exact Herr].
  - intros q k i Hq Hi. destruct (live_heap A (u q) k HW Hq) as (Hk0 & Hlo & Hce & Himg & _). ceil. pose proof (round16_ge k).
    assert (Ea : u (at_ q i) = u q + i) by (unfold at_; rewrite uZ by lia; reflexivity).
    apply (Flm (u q) k (at_ q i) Hq). rewrite Ea. lia.
  - intros a Ha. right; right. exact (Fmap a Ha).
  - split; [exact (mv_fixed _ _ _ _ HVM)|]. split; [exact HGS|].
    (* [comment removed for export] *)
    intros H0. exact (snoroom_noroomX _ _ _ _ _ _ _ _ _ _ _ (HNS H0)).
Qed.

Theorem malloc_okX : alloc_slot_specW ->
  forall A s (sp0 : word) argv envp (sp : word) (n : Z),
    call_env A s sp0 argv envp -> a_xmaps A = [] -> 0 <= n < 2^61 ->
    tsafe (m_malloc sp (Z_to_bv 64 n) s) (malloc_postX A n s).
Proof.
  intros AS A s sp0 argv envp sp n HE Hxm Hn.
  destruct (guard_read (ms_mem s)) as (cb & Hcb & _).
  pose proof (II_of_call_env A s sp0 argv envp cb HE Hcb) as HII. pose proof HE as [HM HWIN HEnv]. pose proof HM as [HW HR HV HL HC H48].
  apply (tsafe_leaves_of_cps (m_malloc sp (Z_to_bv 64 n)) s). intros K' P' HK'.
  apply tsafe_of_tsall.
  apply (malloc_okW AS WAll word sp0 argv envp cb A s sp n K' P' HII Hxm H48 HL Hn).
  intros s' A' res HII' HFR Hxm' H48' Hlock' HVM HREL _ _ HGS HNS. apply tsall_of_tsafe. apply HK'.
  refine (malloc_leafX sp0 argv envp cb A s n s' A' res HII HII' HFR Hxm' H48' HVM HREL HGS (HNS _)).
  intros HWF. discriminate HWF.
Qed.

Theorem malloc_ok : alloc_slot_specW ->
  forall A s (sp0 : word) argv envp (sp : word) (n : Z),
    call_env A s sp0 argv envp -> a_xmaps A = [] -> 0 <= n < 2^61 ->
    tsafe (m_malloc sp (Z_to_bv 64 n) s) (malloc_post A n s).
Proof.
  intros AS A s sp0 argv envp sp n HE Hxm Hn.
  eapply tsafe_mono; [| exact (malloc_okX AS A s sp0 argv envp sp n HE Hxm Hn)].
  intros r s' H. exact (malloc_postX_post A n s r s' H).
Qed.

End WithLayout.
