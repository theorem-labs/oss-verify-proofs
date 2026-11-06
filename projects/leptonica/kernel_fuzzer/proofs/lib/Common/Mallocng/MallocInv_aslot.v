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
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf7 MallocInv_wf8 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm
  MallocInv_coh MallocInv_ops MallocInv_usage MallocInv_hints MallocInv_sc MallocInv_sc3 MallocInv_ameta_iface MallocInv_ametax_iface MallocInv_ametax
  MallocInv_ameta5 MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_nt1 MallocInv_ntfm MallocInv_take MallocInv_tav_iface MallocInv_tav6
  MallocInv_agrp_iface MallocInv_agm1 MallocInv_agm3 MallocInv_aslot_iface MallocInv_aspieces MallocInv_agtail MallocInv_agroot MallocInv_agnest MallocInv_agnest2
  MallocInv_aslot1 MallocInv_vmfree MallocSureLedger MallocSureInv MallocSureGrow MallocSureCap MallocSureCredit MallocSurePot
  MallocInv_take MallocInv_ntfm MallocInv_agroot MallocInv_agnest MallocInv_tav6.
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

Definition alloc_slot_specI : Prop :=
  forall (fuel : nat) (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (sc req : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    0 <= sc < 48 -> 0 <= req -> req + 4 <= 16 * size_class sc ->
    4 - nest_rank sc <= Z.of_nat fuel ->
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_fail A A' sc (ms_mem s) -> aslot_vm A sc s s' ->
       (W = WOk -> inoroom A s (4 - nest_rank sc)) ->
       (* [comment removed for export] *)
       aslot_growS sc A A' s s' -> (W <> WFail -> aslot_noroomS sp0 argv envp cb sc A s) ->
       tsall W (K wm1 s') P) ->
    (forall s' A' (g idx : Z) mt aib slots,
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_ok A A' sc req g idx (ms_mem s) s' -> gnew A A' (ms_mem s) -> aslot_vm A sc s s' ->
       a_ctx A' (KActive sc) = g -> g = hd 0 (a_active A' sc) -> a_active A' sc <> [] ->
       a_meta A' g = Some mt -> mt_role mt = RGroup aib slots -> mt_sc mt = sc ->
       0 <= idx <= mt_last mt -> nth_error slots (Z.to_nat idx) = Some STaken ->
       req + 4 <= mt_stride mt ->
       (16 * size_class sc <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (req + 20))) ->
       (W = WFail -> aslot_had_idle A) ->
       (* [comment removed for export] *)
       aslot_growS sc A A' s s' ->
       tsall W (K (Z_to_bv 64 idx) s') P) ->
    tsall W ((x <- m_alloc_slot fuel sp (Z_to_bv 64 sc) (Z_to_bv 64 req) ;; K x) s) P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s7_word : forall sc, 0 <= sc < 64 -> v_add A_LOCK (v_slli (Z_to_bv 64 sc) 3) = Z_to_bv 64 (LOCKA + 8 * sc).
Proof. intros sc Hsc. rewrite A_LOCK_eq, v_slli_Z, v_add_Z by lia. f_equal. change (2^3) with 8. lia. Qed.

Lemma pm_word : forall sc, at_ (Z_to_bv 64 (LOCKA + 8 * sc)) 88 = Z_to_bv 64 (caddr (KActive sc)).
Proof. intros sc. rewrite at_Z, caddr_active. apply f_equal. lia. Qed.

Lemma us_word : forall sc, at_ (Z_to_bv 64 (LOCKA + 8 * sc)) 472 = Z_to_bv 64 (caddr (KUsage sc)).
Proof. intros sc. rewrite at_Z, caddr_usage. apply f_equal. lia. Qed.

Lemma tab_word : forall sc, 0 <= sc < 64 -> v_add A_SIZE_CLASSES (v_slli (Z_to_bv 64 sc) 1) = Z_to_bv 64 (T_SIZE_CLASSES + 2 * sc).
Proof. intros sc Hsc. rewrite A_SIZE_CLASSES_eq, v_slli_Z, v_add_Z by lia. f_equal. change (2^1) with 2. lia. Qed.

Lemma size_word : forall szc, 0 <= szc < 2^40 -> v_slli (Z_to_bv 64 szc) 4 = Z_to_bv 64 (16 * szc).
Proof. intros szc H. rewrite v_slli_Z by lia. f_equal. change (2^4) with 16. lia. Qed.

(* [comment removed for export] *)
Lemma stc_plus12 : forall n16, 0 <= n16 -> size_to_class_z (16 * n16 + 12) = size_to_class_z (16 * n16).
Proof.
  intros n16 Hn. unfold size_to_class_z.
  replace ((16 * n16 + 12 + 3) / 16) with n16 by (apply Z.div_unique with (r := 15); lia).
  replace ((16 * n16 + 3) / 16) with n16 by (apply Z.div_unique with (r := 3); lia). reflexivity.
Qed.

Lemma stc_small : forall n16, 0 <= n16 < 10 -> size_to_class_z (16 * n16) = n16.
Proof.
  intros n16 Hn. unfold size_to_class_z. replace ((16 * n16 + 3) / 16) with n16 by (apply Z.div_unique with (r := 3); lia).
  destruct (Z.ltb_spec n16 10); [reflexivity | lia].
Qed.

Lemma size_class_small : forall j, 0 <= j < 10 -> size_class j = j + 1.
Proof.
  intros j Hj.
  assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.



Lemma c_lts_wm1_w0' : c_lts wm1 w0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nest_class : forall sc c0 cnt1 n16 J,
  0 <= sc < 48 -> In c0 (cnt_cands sc) -> cnt1 = cnt1_of (16 * size_class sc) c0 -> n16 = size_class sc * cnt1 ->
  16 * n16 + 16 <= 2048 -> J = size_to_class_z (16 * n16) ->
  nest_rank sc < nest_rank J /\ (J = 15 \/ J = 19 \/ J = 23) /\ 0 <= J < 48 /\
  10 <= n16 < 8191 /\ J = stc n16 /\ 16 * n16 + 16 <= 16 * size_class J.
Proof.
  intros sc c0 cnt1 n16 J Hsc Hc0 Hc1 Hn HJs HJ. pose proof (size_class_range sc Hsc) as SZC.
  pose proof (cnt_facts sc c0 Hsc Hc0) as CF. cbv zeta in CF. rewrite <- Hc1 in CF. destruct CF as (C1 & _).
  assert (Hn1 : 1 <= n16) by (subst n16; nia).
  assert (NT : nest_target sc c0 = Some J).
  { unfold nest_target. cbv zeta. rewrite <- Hc1. replace (16 * size_class sc * cnt1) with (16 * n16) by lia.
    rewrite (proj2 (Z.leb_le _ _) HJs). f_equal. rewrite stc_plus12 by lia. symmetry. exact HJ. }
  destruct (nest_rank_ok sc c0 J Hsc Hc0 NT) as [Hrk HJ15]. pose proof (size_class_15_19_23 J HJ15) as (HJr & _ & _).
  assert (Hn10 : 10 <= n16).
  { destruct (Z_lt_le_dec n16 10) as [Hl|Hl]; [| exact Hl]. exfalso. rewrite (stc_small n16) in HJ by lia. lia. }
  destruct (stc_facts n16 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & Hlt & Est).
  assert (EJ : J = stc n16) by (rewrite HJ, <- Est; reflexivity).
  split; [exact Hrk|]. split; [exact HJ15|]. split; [exact HJr|]. split; [lia|]. split; [exact EJ|]. rewrite EJ. lia.
Qed.

(* [comment removed for export] *)
Lemma nest_stride : forall A gj mt aib slots j x, WF A ->
  a_meta A gj = Some mt -> mt_role mt = RGroup aib slots -> mt_sc mt = j -> (j = 15 \/ j = 19 \/ j = 23) -> 64 <= x ->
  (16 * size_class j <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z x)) ->
  mt_stride mt = 16 * size_class j.
Proof.
  intros A gj mt aib slots j x HW Hmt Hrl Hscj Hj15 Hx Hstr.
  pose proof (size_class_15_19_23 j Hj15) as (_ & S127 & S31).
  assert (SG : mt_last mt = 0 -> 0 < mt_maplen mt -> mt_stride mt <= 16 * size_class j).
  { intros Hl Hml. destruct (wf_single A HW gj mt aib slots Hmt Hrl Hl Hml ltac:(rewrite Hscj; lia)) as [H|H]; rewrite Hscj in H; lia. }
  destruct Hstr as [H | (Hl & Hml & E)].
  - unfold mt_stride in *. rewrite Hscj in *. destruct ((mt_maplen mt =? 0) || negb (mt_last mt =? 0))%bool eqn:C; [reflexivity|].
    apply Bool.orb_false_iff in C. destruct C as [C1 C2]. apply Z.eqb_neq in C1. apply Bool.negb_false_iff in C2. apply Z.eqb_eq in C2.
    pose proof (SG C2 ltac:(unfold mt_maplen in *; pose proof (Z.div_pos (mt_w32 mt) 4096); lia)). lia.
  - exfalso. pose proof (SG Hl Hml).
    destruct (page_round_up_Z_spec x ltac:(lia)) as [B M].
    assert (4096 <= page_round_up_Z x).
    { set (r := page_round_up_Z x) in *. pose proof (Z.div_mod r 4096 ltac:(lia)) as DM.
      assert (Hq : 1 <= r / 4096) by (destruct (Z_lt_le_dec (r / 4096) 1); [exfalso; assert (r / 4096 = 0) by (pose proof (Z.div_pos r 4096); lia); lia | lia]). clear - DM M Hq. nia. }
    lia.
Qed.

(* [comment removed for export] *)
Lemma fmA_dead : forall B g fl h t, WF B -> a_freelist B = fl -> h = hd g fl -> t = last fl g ->
  forall x mt, x <> g -> a_meta B x = Some mt -> mt_role mt = RDead -> a_meta (fmA B g fl h t) x = Some mt.
Proof.
  intros B g fl h t HW Hfl Hh Ht x mt Hxg Hx Hr. rewrite (fmA_meta_other B g fl h t x Hxg), Hx. cbn [option_map]. f_equal.
  apply (rl_nonfree B HW g fl h t Hfl Hh Ht x mt Hx); [| exact Hxg]. rewrite Hr. discriminate.
Qed.

(* [comment removed for export] *)
Lemma tv_spare : forall A A1 sc, tavrel A A1 sc -> spare A1 = spare A.
Proof.
  intros A A1 sc TV. apply spare_same; [exact (tv_fl _ _ _ TV)|].
  apply (tv_ctx _ _ _ TV KAmc); [exact I | discriminate | intros H; exact H].
Qed.

Lemma fmA_spare : forall B g h t, spare B <= spare (fmA B g (a_freelist B) h t).
Proof.
  intros B g h t. unfold spare. rewrite fmA_freelist, length_app. cbn [length].
  replace (a_ctx (fmA B g (a_freelist B) h t) KAmc) with (a_ctx B KAmc) by reflexivity. lia.
Qed.

Lemma agfail_spare : forall A A' m, agfail A A' m -> spare A <= spare A'.
Proof.
  intros A A' m AGF. unfold spare. rewrite (af_fl _ _ _ AGF), length_app. cbn [length].
  rewrite (af_ctx _ _ _ AGF KAmc I ltac:(discriminate) ltac:(intros H; exact H)). lia.
Qed.

Lemma aghand_spare : forall A A' m p L, aghand A A' m p L -> spare A' = spare A.
Proof.
  intros A A' m p L AH. apply spare_same; [exact (ah_fl _ _ _ _ _ AH)|].
  apply (ah_ctx _ _ _ _ _ AH KAmc); [exact I | intros H; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem alloc_slot_okI : alloc_slot_specI.
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros W R sp0 argv envp cb D A s sp sc req K P HII Hsc Hreq Hfit Hfuel HF HS.
  { exfalso. pose proof (nest_rank_range sc). cbn [Z.of_nat] in Hfuel. lia. }
  pose proof (ii_is HII) as HIS. pose proof HIS as [HW HR HC HWIN HE HG].
  pose proof (envok_rodata _ _ _ _ HE) as HRO. pose proof (envok_statics _ _ _ _ HE) as HST.
  pose proof (nest_rank_range sc) as Hnr. pose proof (size_class_range sc Hsc) as SZC.
  pose proof (grp_cap_ge sc) as Hgc.   (* [comment removed for export] *)
  rewrite m_alloc_slot_unfold.
  (* [comment removed for export] *)
  treassoc. eapply (tw_det W m_canary_load s _ P (A_SSP, le_val cb) s).
  { intros K' P' HK'. apply ts_canary_load; [exact HST | exact HWIN |]. intros cb' Hcb'. unfold GRD in HG. rewrite HG in Hcb'. injection Hcb' as <-. exact HK'. }
  cbv beta iota zeta. rewrite (s7_word sc) by lia. rewrite pm_word, us_word.
  (* [comment removed for export] *)
  treassoc. treassoc.
  eapply (tw_det W _ s _ P (Z_to_bv 64 (a_ctx A (KActive sc))) s).
  { intros K' P' HK'. eapply (ts_ld_ctx A s (KActive sc)); [exact HR | exact HWIN | cbn; lia | reflexivity | | exact HK'].
    rewrite (wf_act_head A HW sc Hsc). destruct (a_active A sc) as [|g0 l] eqn:E; [cbn; lia|]. cbn [hd].
    destruct (wf_act_mem A HW sc g0 ltac:(rewrite E; left; reflexivity)) as (mt0 & aib0 & sl0 & H0 & _). pose proof (meta_facts A g0 mt0 HW H0). ceil. lia. }
  (* [comment removed for export] *)
  treassoc.
  eapply (tw_lift W _ s (fun ta s1 => exists A1, II sp0 argv envp cb D A1 s1 /\ ntframe A s s1 /\ tavrel A A1 sc /\
            (a_active A1 sc = [] -> ring_dry A sc) /\
            ((ta = None /\ a_active A1 sc = []) \/
             (exists g mt aib slots, ta = Some (Z_to_bv 64 g, w32 (mt_avail mt)) /\ a_active A1 sc <> [] /\ g = hd 0 (a_active A1 sc) /\
                a_meta A1 g = Some mt /\ mt_role mt = RGroup aib slots /\ mt_avail mt <> 0)))).
  { intros K' P' HK'. apply (try_avail_okD _ sp0 argv envp cb D A s sc K' P' HII Hsc).
    - intros s1 A1 H1 H2 H3 H4 HD. apply HK'. exists A1. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [intros _; exact HD|]. left. auto.
    - intros s1 A1 g mt aib slots H1 H2 H3 H4 H5 H6 H7 H8. apply HK'. exists A1. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [intros E; exfalso; exact (H4 E)|]. right. exists g, mt, aib, slots. auto 10. }
  intros ta s1 (A1 & HII1 & NF1 & TV & HDRY & CASES).
  pose proof (ii_is HII1) as HIS1. pose proof HIS1 as [HW1 HR1 HC1 HWIN1 HE1 HG1].
  (* [comment removed for export] *)
  assert (G01 : sgrow 0 0 0 A A1 (ms_vm s) (ms_vm s1)) by (apply sgrow_same; [exact (nf_vm _ _ _ NF1) | exact (tv_areas _ _ _ TV) | rewrite (tv_spare _ _ _ TV); apply Z.le_refl]).
  (* [comment removed for export] *)
  assert (P01 : pgrow 0 A A1 (ms_vm s) (ms_vm s1))
    by (apply pgrow_pot; [exact (nf_vm _ _ _ NF1) | exact (tav_pot A A1 sc HW HW1 TV HDRY) | rewrite (tv_spare _ _ _ TV); apply Z.le_refl]).
  pose proof (acostS_ge sc Hsc) as (HcT & HcG & HcF).
  destruct CASES as [(-> & Hact1) | (g & mt & aib & slots & -> & Hne1 & Hhd & Hg & Hrg & Hav)].
  2: { (* [comment removed for export] *)
    cbv beta iota.
    eapply (tw_lift W _ s1 (fun r s2 => r = Z_to_bv 64 (ctz32 (mt_avail mt)) /\ II sp0 argv envp cb D (tkA A1 g mt aib slots (ctz32 (mt_avail mt))) s2 /\ ntframe A1 s1 s2)).
    { intros K' P' HK'. apply (ts_as_take sp0 argv envp cb D A1 s1 HII1 sc g mt aib slots Hsc Hne1 Hhd Hg Hrg Hav K' P').
      intros s2 H1 H2 _ _ _. apply HK'. auto. }
    intros r s2 (-> & HII2 & NF2).
    pose proof (take_leaf sp0 argv envp cb D A s A1 s1 sc Hsc HII1 NF1 TV g mt aib slots req s2 Hne1 Hhd Hg Hrg Hav Hfit HII2 NF2)
      as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
    (* [comment removed for export] *)
    treassoc. pose proof (ii_is HII2) as [_ _ _ HWIN2 _ HG2].
    eapply (tw_det W _ s2 _ P tt s2); [intros K' P' HK'; apply (ts_canary_check s2 cb); [exact HWIN2 | exact HG2 | exact HK'] |].
    apply tw_bind_ret.
    apply (HS s2 _ g (ctz32 (mt_avail mt)) _ aib _ HII2 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 (or_introl F14)); [intros _; exact F15 |].
    (* [comment removed for export] *)
    unfold aslot_growS. split.
    { apply (sgrow_weaken 0 0 0); [| clear - Hnr Hgc; lia | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia| clear - Hnr Hgc; lia].
      replace 0 with (0 + 0) by reflexivity. apply (sgrow_trans _ _ _ _ _ _ A A1 _ _ _ _ G01).
      apply sgrow_same; [exact (nf_vm _ _ _ NF2) | reflexivity | apply Z.le_refl]. }
    (* [comment removed for export] *)
    apply (pgrow_weaken (0 + 16 * size_class sc)); [| exact HcT].
    apply (pgrow_trans _ _ A A1 _ _ _ _ P01).
    pose proof (take_facts sp0 argv envp cb D A1 s1 HII1 sc g mt aib slots Hsc Hg Hrg Hav) as (_ & Hi32 & Hbit).
    pose proof (tk_slot_idle A1 HW1 sc g mt aib slots (ctz32 (mt_avail mt)) Hsc Hhd Hne1 Hg Hrg ltac:(clear - Hi32; lia) Hbit) as Hidle.
    assert (PT : pot A1 <= pot (tkA A1 g mt aib slots (ctz32 (mt_avail mt))) + 16 * size_class sc).
    { apply (pot_take A1 (tkA A1 g mt aib slots (ctz32 (mt_avail mt))) sc g mt aib slots (Z.to_nat (ctz32 (mt_avail mt))) STaken HW1 Hsc (fun c => eq_refl) Hne1 Hhd Hg Hrg Hidle ltac:(discriminate)).
      - exact (slots_of_grp _ g _ aib _ (tkA_meta_same A1 g mt aib slots (ctz32 (mt_avail mt))) (tk_mt_role mt aib slots (ctz32 (mt_avail mt)))).
      - intros x Hx. exact (tkA_meta_other A1 g mt aib slots (ctz32 (mt_avail mt)) x Hx). }
    exact (pgrow_take _ A1 _ _ _ (nf_vm _ _ _ NF2) PT (Z.le_refl _)). }
  (* [comment removed for export] *)
  cbv beta iota. rewrite (tab_word sc) by lia.
  (* [comment removed for export] *)
  treassoc.
  eapply (tw_det W _ s1 _ P (Z_to_bv 64 (size_class sc)) s1).
  { intros K' P' HK'. eapply ts_lhu_size_class; [exact (envok_rodata _ _ _ _ HE1) | exact HWIN1 | exact Hsc | exact HK']. }
  rewrite (size_word (size_class sc)) by lia.
  (* [comment removed for export] *)
  treassoc.
  apply (alloc_meta_okX W R sp0 argv envp cb D A1 s1 (at_ sp (-64)) _ P HII1).
  { (* [comment removed for export] *)
    intros s2 A2 HII2 FR2 GS2 AM2 Hxm2 DOM2 SP0 AR2 NB GR2 NBS. rewrite is0_Z by lia. change (0 =? 0) with true. cbv iota. apply tw_bind_ret.
    pose proof (ii_is HII2) as [_ _ _ HWIN2 _ HG2].
    treassoc. eapply (tw_det W _ s2 _ P tt s2); [intros K' P' HK'; apply (ts_canary_check s2 cb); [exact HWIN2 | exact HG2 | exact HK'] |].
    apply tw_bind_ret.
    destruct (amfail_leaf sp0 argv envp cb D A s A1 s1 sc Hsc NF1 TV A2 s2 HII2 FR2 GS2 AM2 Hxm2 DOM2 SP0 AR2) as (F1 & F2 & F3 & F4).
    apply (HF s2 A2 HII2 F1 F2 F3); [intros HWk; exact (F4 (NB HWk)) | |].
    - (* [comment removed for export] *)
      unfold aslot_growS. split.
      { apply (sgrow_weaken (0 + 1) (0 + 8192) (0 + 0)); [| clear - Hnr Hgc; lia | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia| clear - Hnr Hgc; lia].
        apply (sgrow_trans _ _ _ _ _ _ A A1 A2 _ _ _ G01).
        exact (sgrow_am_fail A1 A2 _ _ GR2 SP0 AR2 (spare_nn A2 (is_wf _ _ _ _ _ _ (ii_is HII2)))). }
      (* [comment removed for export] *)
      apply (pgrow_weaken (0 + 8192)); [| clear - HcF; lia].
      apply (pgrow_trans _ _ A A1 A2 _ _ _ P01). apply (pgrow_am_fail A1 A2 _ _ (proj1 (proj2 GR2)) SP0).
      apply (pot_keep_meta A1 A2 HW1 (fun c _ => gs_active _ _ GS2 c)).
      intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [exact (gs_grp _ _ GS2 x mtx aibx slx Hx Hrx) | exact Hrx].
    - (* [comment removed for export] *)
      intros HWnf. unfold aslot_noroomS. exists D, A1, s1. split; [exact HII1|].
      split; [apply (sgrow_weaken 0 0 0); [exact G01 | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia| clear - Hnr Hgc; lia]|].
      split; [rewrite (tv_xmaps _ _ _ TV); clear; lia | left; exact (NBS HWnf)]. }
  (* [comment removed for export] *)
  intros s2 A2 m HII2 FR2 GM2 AM2 Hxm2 DELTA2 SPARE GR2.
  (* [comment removed for export] *)
  assert (G02 : sgrow 1 8192 1 A A2 (ms_vm s) (ms_vm s2)).
  { replace 1 with (0 + 1) by reflexivity. replace 8192 with (0 + 8192) by reflexivity.
    apply (sgrow_trans _ _ _ _ _ _ A A1 A2 _ _ _ G01). exact (sgrow_am A1 A2 _ _ (m - 24) GR2 SPARE). }
  (* [comment removed for export] *)
  assert (P02 : pgrow META_COST A A2 (ms_vm s) (ms_vm s2)).
  { replace META_COST with (0 + META_COST) by reflexivity. apply (pgrow_trans _ _ A A1 A2 _ _ _ P01).
    apply (pgrow_am A1 A2 _ _ (m - 24) (proj1 (proj2 GR2)) SPARE).
    apply (pot_keep_meta A1 A2 HW1 (fun c _ => gs_active _ _ (gm_gsame _ _ _ _ GM2) c)).
    intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [exact (gs_grp _ _ (gm_gsame _ _ _ _ GM2) x mtx aibx slx Hx Hrx) | exact Hrx]. }
  assert (X02 : a_xmaps A2 = a_xmaps A) by (rewrite Hxm2; exact (tv_xmaps _ _ _ TV)).
  pose proof (ii_is HII2) as HIS2. pose proof HIS2 as [HW2 HR2 HC2 HWIN2 HE2 HG2].
  destruct (gm_meta _ _ _ _ GM2) as (md & Hmd2 & Hrd & Hmd0). pose proof (gm_fresh _ _ _ _ GM2) as HmD.
  pose proof (gm_lo _ _ _ _ GM2) as Hmlo. pose proof (gm_hi _ _ _ _ GM2) as Hmhi. ceil.
  assert (Hact2 : a_active A2 sc = []) by (rewrite (gs_active _ _ (gm_gsame _ _ _ _ GM2) sc); exact Hact1).
  rewrite is0_Z by lia. replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  (* [comment removed for export] *)
  assert (HUS : 0 <= a_ctx A2 (KUsage sc) < 2^47) by (rewrite (ii_us HII2 sc Hsc); exact (usage_of_range A2 sc HW2)).
  treassoc. eapply (tw_det W _ s2 _ P (Z_to_bv 64 (a_ctx A2 (KUsage sc))) s2).
  { intros K' P' HK'. eapply (ts_ld_ctx A2 s2 (KUsage sc)); [exact HR2 | exact HWIN2 | cbn; lia | reflexivity | lia | exact HK']. }
  set (usage := a_ctx A2 (KUsage sc)) in *.
  (* [comment removed for export] *)
  treassoc. rewrite A_PAGE_SIZE_eq. eapply (tw_ld_pagesize W sp0 argv envp cb A2); [exact HIS2|].
  (* [comment removed for export] *)
  treassoc.
  eapply (tw_lift W _ s2 (fun c s' => s' = s2 /\ exists c0, c = Z_to_bv 64 c0 /\ In c0 (cnt_cands sc) /\ 1 <= c0 <= 32 /\
                                       (c0 = 1 -> sc mod 4 = 3 /\ (2032 < 16 * size_class sc -> (16 * size_class sc + 16) mod 4096 = 0)))).
  { intros K' P' HK'. apply (as_cnt_ok _ sp0 argv envp cb (m :: D) A2 s2 sc usage (16 * size_class sc) K' P' HII2 Hsc eq_refl ltac:(lia)).
    intros c0 H1 H2 H3 H4. apply HK'. split; [reflexivity|]. exists c0. auto. }
  intros c s2' (-> & c0 & -> & Hc0 & Hc0r & Hc01).
  rewrite (cnt1_word c0 (size_class sc) Hc0r SZC).
  pose proof (cnt_facts sc c0 Hsc Hc0) as CF. cbv zeta in CF.
  set (cnt1 := cnt1_of (16 * size_class sc) c0) in *. destruct CF as (C1 & C20 & C2 & Cn2 & Cs).
  rewrite (nest_test_word (size_class sc) cnt1 SZC C1). rewrite (v_mul_Z (16 * size_class sc) cnt1).
  destruct (Z.leb_spec (16 * size_class sc * cnt1 + 16) 2048) as [Hsmall | Hbig].
  - (* [comment removed for export] *)
    rewrite as_nested_unfold. unfold wlit. rewrite !v_addi_Z, !v_srli_Z by lia.
    replace (16 * size_class sc * cnt1 / 2^4) with (size_class sc * cnt1) by (change (2^4) with 16; rewrite <- (Z.div_mul (size_class sc * cnt1) 16) at 1 by lia; f_equal; lia).
    set (n16 := size_class sc * cnt1) in *. set (J := size_to_class_z (16 * n16)).
    destruct (nest_class sc c0 cnt1 n16 J Hsc Hc0 eq_refl eq_refl ltac:(lia) eq_refl) as (Hrk & HJ15 & HJr & Hn16 & EJ & HfitJ).
    pose proof (nest_rank_range J) as HnrJ.
    pose proof (grp_cap_nest sc J (proj1 (proj2 (size_class_15_19_23 J HJ15)))) as HgcJ.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (HaJ : META_COST + acostS J <= acostS sc).
    { pose proof (proj1 (proj2 (size_class_15_19_23 J HJ15))) as HJ127.
      rewrite (acostS_small sc), (acostS_small J); [unfold META_COST; clear - Hrk Hnr HnrJ; lia | clear - HJ127; lia | clear - Hsmall C1 SZC; nia]. }
    rewrite c_ltu_Z by lia. replace (16 * size_class sc * cnt1 + 12 <? 157) with false by (symmetry; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    treassoc.
    eapply (tw_det W _ s2 _ P (Z_to_bv 64 J) s2).
    { intros K' P' HK'. rewrite EJ in HK'. eapply ts_size_to_class_big; [exact (envok_rodata _ _ _ _ HE2) | exact HWIN2 | lia | exact HK']. }
    rewrite (sextw_small J) by lia.
    (* [comment removed for export] *)
    treassoc.
    apply (IH W R sp0 argv envp cb (m :: D) A2 s2 (at_ sp (-144)) J (16 * size_class sc * cnt1 + 12) _ P HII2 HJr ltac:(lia) ltac:(lia) ltac:(lia)).
    + (* [comment removed for export] *)
      intros s3 A3 HII3 FR3 AF3 AV3 NR3 GR3 NRS3. rewrite c_lts_wm1_w0'. cbv iota.
      pose proof (ak_dead _ _ _ _ (af_keep _ _ _ _ AF3) m md Hmd2 Hrd) as Hmd3.
      pose proof (is_wf _ _ _ _ _ _ (ii_is HII3)) as HW3.
      treassoc.
      eapply (tw_lift W _ s3 (fun _ s4 => II sp0 argv envp cb D (fmA A3 m (a_freelist A3) (hd m (a_freelist A3)) (last (a_freelist A3) m)) s4 /\ ntframe A3 s3 s4)).
      { intros K' P' HK'. apply (ts_free_meta_ag sp0 argv envp cb D A3 s3 m md HII3 HmD Hmd3 Hrd). intros s4 H1 H2. apply HK'. auto. }
      intros uu s4 (HII4 & NF4). apply tw_bind_ret.
      pose proof (ii_is HII4) as [_ _ _ HWIN4 _ HG4].
      treassoc. eapply (tw_det W _ s4 _ P tt s4); [intros K' P' HK'; apply (ts_canary_check s4 cb); [exact HWIN4 | exact HG4 | exact HK'] |].
      apply tw_bind_ret.
      set (A4 := fmA A3 m (a_freelist A3) (hd m (a_freelist A3)) (last (a_freelist A3) m)) in *.
      destruct (nestfail_leaf sp0 argv envp cb D A s A1 s1 sc HII Hsc HII1 NF1 TV A2 s2 m FR2 GM2 AM2 Hxm2 SPARE J A3 s3 A4 s4 HJr Hrk HII3 FR3 AF3 AV3 NF4
                  (fmA_live _ _ _ _ _) 
                  (fmA_group A3 HW3 m md _ _ _ Hmd3 Hrd eq_refl eq_refl eq_refl)
                  (fmA_group_inv A3 HW3 m _ _ _ eq_refl eq_refl eq_refl)
                  (dom_fmA A3 m md _ _ _ Hmd3 Hrd)
                  (fmA_active _ _ _ _ _) (fmA_xmaps _ _ _ _ _) (fmA_areas _ _ _ _ _)
                  (fmA_ctx_other A3 m _ _ _ KAmc ltac:(discriminate) ltac:(intros c; discriminate))
                  (fmA_freelist _ _ _ _ _)
                  (fmA_dead A3 m _ _ _ HW3 eq_refl eq_refl eq_refl))
        as (F1 & F2 & F3 & F4).
      apply (HF s4 A4 HII4 F1 F2 F3); [intros HWk; exact (F4 (NR3 HWk) (DELTA2 HWk)) | |].
      * (* [comment removed for export] *)
        unfold aslot_growS in *. destruct GR3 as [GR3 PR3]. split.
        { apply (sgrow_weaken (1 + (5 - nest_rank J) + 0) (8192 + ((4 - nest_rank J) * 8192 + grp_cap J) + 0) (1 + (4 - nest_rank J) + 0));
            [| clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia| clear - Hrk Hnr HnrJ HgcJ; lia].
          apply (sgrow_trans _ _ _ _ _ _ A A3 A4 (ms_vm s) (ms_vm s3) (ms_vm s4)); [exact (sgrow_trans _ _ _ _ _ _ A A2 A3 _ _ _ G02 GR3) |].
          apply sgrow_same; [exact (nf_vm _ _ _ NF4) | unfold A4; apply fmA_areas | unfold A4; apply fmA_spare]. }
        (* [comment removed for export] *)
        apply (pgrow_weaken (META_COST + acostS J + 0)); [| clear - HaJ; lia].
        apply (pgrow_trans _ _ A A3 A4 (ms_vm s) (ms_vm s3) (ms_vm s4)); [exact (pgrow_trans _ _ A A2 A3 _ _ _ P02 PR3) |].
        apply pgrow_pot; [exact (nf_vm _ _ _ NF4) | | unfold A4; apply fmA_spare].
        rewrite (pot_keep_meta A3 A4 HW3 (fun c _ => eq_refl)); [apply Z.le_refl|].
        intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [| exact Hrx].
        exact (fmA_group A3 HW3 m md _ _ _ Hmd3 Hrd eq_refl eq_refl eq_refl x mtx aibx slx Hx Hrx).
      * (* [comment removed for export] *)
        intros HWnf. unfold aslot_noroomS in *.
        apply (snoroom_weaken _ _ _ _ (1 + (4 - nest_rank J)) (8192 + ((4 - nest_rank J) * 8192 + grp_cap J)) (1 + (4 - nest_rank J)) (0 + 0) (grp_cap J));
          [| clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia | clear; lia | exact HgcJ].
        apply (snoroom_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ A s A2 s2 G02); [rewrite X02; clear; lia | exact (NRS3 HWnf)].
    + (* [comment removed for export] *)
      intros s3 A3 gj idx mt aib slots HII3 FR3 AO3 GN3 AV3 Hctx3 Hhd3 Hne3 Hmt3 Hrl3 Hsc3 Hidx3 Hslot3 Hreq3 Hstr3 HOOK3 GR3.
      pose proof (is_wf _ _ _ _ _ _ (ii_is HII3)) as HW3. pose proof (w_last_range (mt_w32 mt)) as Hlr. change (w_last (mt_w32 mt)) with (mt_last mt) in Hlr.
      rewrite w0_eq, c_lts_Z by lia. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      assert (H64 : 64 <= 16 * size_class sc * cnt1 + 12 + 20) by lia.
      pose proof (nest_stride A3 gj mt aib slots J _ HW3 Hmt3 Hrl3 Hsc3 HJ15 H64 Hstr3) as Hstride.
      pose proof (ak_dead _ _ _ _ (ao_keep _ _ _ _ _ _ _ _ AO3) m md Hmd2 Hrd) as Hmd3.
      assert (Hact3 : a_active A3 sc = []).
      { rewrite (ak_act _ _ _ _ (ao_keep _ _ _ _ _ _ _ _ AO3) sc ltac:(intros E; rewrite E in Hrk; lia) ltac:(lia)). exact Hact2. }
      eapply (tw_lift W _ s3 (fun r s4 => r = Z_to_bv 64 0 /\ exists ab, 0 <= ab < 256 /\ ms_vm s4 = ms_vm s3 /\
                 II sp0 argv envp cb D (nestA A3 sc m J gj mt aib slots idx cnt1 ab) s4 /\ FR A3 s3 (nestA A3 sc m J gj mt aib slots idx cnt1 ab) s4)).
      { intros K' P' HK'.
        apply (ts_nest_rest sp0 argv envp cb D A3 s3 sc m md J gj mt aib slots idx cnt1 HII3 Hmd3 Hrd Hmd0 HmD Hsc Hact3 HJr Hctx3 Hmt3 Hrl3 Hsc3 Hidx3 Hslot3 Hstride
                 ltac:(lia) ltac:(lia) Hsmall K' P').
        intros ab s4 Hab Hvm4 HII4 FR4. apply HK'. split; [reflexivity|]. exists ab. auto. }
      intros r s4 (-> & ab & Hab & Hvm4 & HII4 & FR4).
      pose proof (ii_is HII4) as [_ _ _ HWIN4 _ HG4].
      treassoc. eapply (tw_det W _ s4 _ P tt s4); [intros K' P' HK'; apply (ts_canary_check s4 cb); [exact HWIN4 | exact HG4 | exact HK'] |].
      apply tw_bind_ret.
      destruct (nestok_leaf sp0 argv envp cb D A s A1 s1 sc Hsc HII1 NF1 TV Hact1 A2 s2 m FR2 GM2 AM2 Hxm2 SPARE md J gj idx mt aib slots cnt1 req A3 s3
                  Hmd2 Hrd Hmd0 HJ15 Hrk ltac:(lia) ltac:(lia) Hsmall ltac:(lia) HII3 FR3 AO3 GN3 AV3 Hmt3 Hrl3 Hsc3 Hidx3 Hslot3 Hstr3 ab s4 Hab HII4 FR4 Hvm4)
        as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
      apply (HS s4 _ m 0 _ _ _ HII4 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 (or_introl N14)); [intros HWf; apply N15; exact (HOOK3 HWf) |].
      (* [comment removed for export] *)
      unfold aslot_growS in *. destruct GR3 as [GR3 PR3]. split.
      { apply (sgrow_weaken (1 + (5 - nest_rank J) + 0) (8192 + ((4 - nest_rank J) * 8192 + grp_cap J) + 0) (1 + (4 - nest_rank J) + 0));
          [| clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia | clear - Hrk Hnr HnrJ HgcJ; lia| clear - Hrk Hnr HnrJ HgcJ; lia].
        apply (sgrow_trans _ _ _ _ _ _ A A3 _ (ms_vm s) (ms_vm s3) (ms_vm s4)); [exact (sgrow_trans _ _ _ _ _ _ A A2 A3 _ _ _ G02 GR3) |].
        apply sgrow_same; [exact Hvm4 | reflexivity | apply Z.le_refl]. }
      (* [comment removed for export] *)
      apply (pgrow_weaken (META_COST + acostS J + 0)); [| clear - HaJ; lia].
      apply (pgrow_trans _ _ A A3 _ (ms_vm s) (ms_vm s3) (ms_vm s4)); [exact (pgrow_trans _ _ A A2 A3 _ _ _ P02 PR3) |].
      apply pgrow_pot; [exact Hvm4 | | apply Z.le_refl].
      pose proof (pot_enqueue A3 (nestA A3 sc m J gj mt aib slots idx cnt1 ab) sc HW3 Hsc Hact3
                    (fun c _ Hne => nestA_active_other A3 sc m J gj mt aib slots idx cnt1 ab c Hne)) as PE.
      pose proof (credval_range (nestA A3 sc m J gj mt aib slots idx cnt1 ab) sc Hsc) as CR.
      assert (PE' : pot A3 + credval (nestA A3 sc m J gj mt aib slots idx cnt1 ab) sc <= pot (nestA A3 sc m J gj mt aib slots idx cnt1 ab)); [apply PE | clear - PE' CR; lia].
      intros x mtx aibx slx Hx Hrx _.
      assert (Hxm : x <> m) by (intros ->; rewrite Hmd3 in Hx; injection Hx as <-; rewrite Hrd in Hrx; discriminate Hrx).
      destruct (Z.eq_dec x gj) as [-> | Hxg].
      { rewrite Hmt3 in Hx. injection Hx as <-. rewrite Hrl3 in Hrx. injection Hrx as <- <-.
        rewrite (slots_of_grp _ gj _ _ _ (nestA_gj A3 sc m md J gj mt aib slots idx cnt1 Hmd3 Hrd Hact3 Hmt3 Hrl3 Hsc3 Hidx3 Hstride ab) eq_refl).
        apply (count_idle_set3 slots (Z.to_nat idx) STaken); [exact Hslot3 | discriminate | discriminate | discriminate | discriminate]. }
      unfold slots_of. rewrite (nestA_old A3 sc m J gj mt aib slots idx cnt1 Hact3 ab x Hxm Hxg), Hx, Hrx. reflexivity.
  - (* [comment removed for export] *)
    apply (ag_mmap_ok W R sp0 argv envp cb D A2 s2 sc req m usage (16 * size_class sc) cnt1 md _ P HII2 Hmd2 Hrd Hmd0 HmD Hsc Hact2 eq_refl Hreq Hfit
             ltac:(lia) C1 C20 ltac:(lia)).
    { intros Hc1. assert (Hc01' : c0 = 1) by (unfold cnt1, cnt1_of in Hc1; destruct (c0 =? 1) eqn:E; [apply Z.eqb_eq in E; exact E | lia]).
      destruct (Hc01 Hc01') as [M3 M4096]. split; [exact M3|]. apply M4096. lia. }
    + (* [comment removed for export] *)
      intros s3 A3 HII3 FR3 Hvm3 AGF NRm NRmS.
      pose proof (ii_is HII3) as [_ _ _ HWIN3 _ HG3].
      treassoc. eapply (tw_det W _ s3 _ P tt s3); [intros K' P' HK'; apply (ts_canary_check s3 cb); [exact HWIN3 | exact HG3 | exact HK'] |].
      apply tw_bind_ret.
      destruct (mmapfail_leaf sp0 argv envp cb D A s A1 s1 sc HII Hsc HII1 NF1 TV A2 s2 m FR2 GM2 AM2 Hxm2 SPARE A3 s3 FR3 Hvm3 AGF
                  (af_dead _ _ _ AGF) (af_fl _ _ _ AGF)) as (F1 & F2 & F3 & F4).
      apply (HF s3 A3 HII3 F1 F2 F3); [intros HWk; exact (F4 (NRm HWk) (DELTA2 HWk)) | |].
      * (* [comment removed for export] *)
        unfold aslot_growS. split.
        { apply (sgrow_weaken (1 + 0) (8192 + 0) (1 + 0)); [| clear - Hnr Hgc; lia | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia| clear - Hnr Hgc; lia].
          apply (sgrow_trans _ _ _ _ _ _ A A2 A3 _ _ _ G02). apply sgrow_same; [exact Hvm3 | exact (af_areas _ _ _ AGF) | exact (agfail_spare _ _ _ AGF)]. }
        (* [comment removed for export] *)
        apply (pgrow_weaken (META_COST + 0)); [| unfold META_COST; clear - HcF; lia].
        apply (pgrow_trans _ _ A A2 A3 _ _ _ P02). apply pgrow_pot; [exact Hvm3 | | exact (agfail_spare _ _ _ AGF)].
        rewrite (pot_keep_meta A2 A3 HW2 (fun c _ => f_equal (fun f => f c) (af_active _ _ _ AGF))); [apply Z.le_refl|].
        intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [exact (MallocInv_agrp_iface.af_grp_back _ _ _ AGF x mtx aibx slx Hx Hrx) | exact Hrx].
      * (* [comment removed for export] *)
        intros HWnf. unfold aslot_noroomS. exists (m :: D), A2, s2. split; [exact HII2|].
        split; [apply (sgrow_weaken 1 8192 1); [exact G02 | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia| clear - Hnr Hgc; lia]|].
        split; [rewrite X02; clear; lia | right].
        destruct (NRmS HWnf) as (len & L1 & L2 & L3). exists len. split; [exact L1|]. split; [exact L2|]. split; [| exact L3].
        pose proof (sg_backed _ _ _ _ _ _ _ G02) as SB. clear - SB Hnr L1. lia.
    + (* [comment removed for export] *)
      intros s3 A3 p L cnt aidx HII3 AGFR AH Hpal Hhr HL HLm Hin3 Hrf3 Hnodom3 Hzero3 Hcnt Hspan HfitL HreqL Haidx Hsingle Hs20 Hpsc HWf NONE2 EXACT HL21 HLcap HLlen.
      destruct (ah_m _ _ _ _ _ AH) as (md3 & Hmd3 & Hrd3 & HW32 & Hz3).
      assert (Hact3 : a_active A3 sc = []) by (rewrite (ah_active _ _ _ _ _ AH); exact Hact2).
      pose proof (ah_xmaps _ _ _ _ _ AH) as Hxm3.
      eapply (tw_lift W _ s3 (fun r s4 => r = Z_to_bv 64 0 /\ exists ab m', 0 <= ab < 256 /\ s4 = upd s3 m' (ms_vm s3) /\
                 II sp0 argv envp cb D (rootA A3 sc m p L cnt aidx (a_xmaps A2) ab) s4 /\ FR A3 s3 (rootA A3 sc m p L cnt aidx (a_xmaps A2) ab) s4 /\
                 (forall a : word, p + 16 <= u a < p + L -> m' a = ms_mem s3 a))).
      { intros K' P' HK'.
        apply (ts_root_tail sp0 argv envp cb D A3 s3 sc req m md3 p L cnt aidx (a_xmaps A2) HII3 Hmd3 Hrd3 HW32 Hz3 HmD Hxm3 Hsc Hact3 Hpal Hhr HL HLm Hin3 Hrf3 Hnodom3 Hzero3
                 Hcnt Hspan HfitL HreqL ltac:(lia) Haidx Hsingle Hs20 Hpsc K' P').
        intros ab m' Hab. cbv zeta. intros HII4 FR4 ZP. apply HK'. split; [reflexivity|]. exists ab, m'. auto 10. }
      intros r s4 (-> & ab & m' & Hab & Es4 & HII4 & FR4 & ZP).
      pose proof (ii_is HII4) as [_ _ _ HWIN4 _ HG4].
      treassoc. eapply (tw_det W _ s4 _ P tt s4); [intros K' P' HK'; apply (ts_canary_check s4 cb); [exact HWIN4 | exact HG4 | exact HK'] |].
      apply tw_bind_ret.
      assert (Hvm4 : ms_vm s4 = ms_vm s3) by (rewrite Es4; reflexivity).
      assert (ZP4 : forall a : word, p + 16 <= u a < p + L -> ms_mem s4 a = ms_mem s3 a) by (rewrite Es4; exact ZP).
      destruct (mmapok_leaf sp0 argv envp cb D A s A1 s1 sc Hsc HII1 NF1 TV Hact1 A2 s2 m HII2 FR2 GM2 AM2 Hxm2 SPARE md req c0 cnt1 A3 s3 md3 p L cnt aidx
                  Hmd2 Hrd ltac:(split; [exact Hreq | exact Hfit]) Hc0 eq_refl HII3 AGFR AH Hmd3 Hrd3 Hpal Hhr HL HLm Hnodom3 Hspan Hpsc Hzero3 Hcnt HreqL HfitL Haidx Hsingle Hs20 NONE2 EXACT
                  ab s4 Hab HII4 FR4 Hvm4 ZP4)
        as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
      apply (HS s4 _ m 0 _ _ _ HII4 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 N12 N13 N14); [intros HWF; exfalso; exact (HWf HWF) |].
      (* [comment removed for export] *)
      assert (HpL : 0 <= p /\ 0 <= L /\ p + L <= 2^64 - 1) by (clear - Hhr HL; unfold heap_range in Hhr; ceil; lia).
      assert (GM : sgrow 1 L 0 A2 A3 (ms_vm s2) (ms_vm s3)).
      { rewrite (agf_vm _ _ _ _ _ AGFR).
        exact (grow_mmap A2 A3 (ms_vm s2) p L (ii_vm HII2) (proj1 HpL) (proj1 (proj2 HpL)) (proj2 (proj2 HpL)) (ah_areas _ _ _ _ _ AH)
                 ltac:(rewrite (aghand_spare _ _ _ _ _ AH); apply Z.le_refl)). }
      unfold aslot_growS. split.
      { apply (sgrow_weaken (1 + 1 + 0) (8192 + grp_cap sc + 0) (1 + 0 + 0)); [| clear - Hnr Hgc; lia | clear - Hnr Hgc; lia | clear - Hnr Hgc; lia| clear - Hnr Hgc; lia].
        apply (sgrow_trans _ _ _ _ _ _ A A3 _ (ms_vm s) (ms_vm s3) (ms_vm s4)); [apply (sgrow_trans _ _ _ _ _ _ A A2 A3 _ _ _ G02) | apply sgrow_same; [exact Hvm4 | reflexivity | apply Z.le_refl]].
        apply (sgrow_weaken 1 L 0); [exact GM | clear; lia | clear - HLcap; lia | clear; lia| clear; lia]. }
      (* [comment removed for export] *)
      apply (pgrow_weaken (META_COST + (16 * size_class sc + 4111))); [| clear - HcG; lia].
      apply (pgrow_trans _ _ A A2 _ (ms_vm s) (ms_vm s2) (ms_vm s4) P02).
      unfold pgrow, pot2. rewrite Hvm4.
      assert (MP : mpot A2 <= mpot (rootA A3 sc m p L cnt aidx (a_xmaps A2) ab)).
      { apply (Z.le_trans _ (mpot A3)); [apply mpot_mono; rewrite (aghand_spare _ _ _ _ _ AH); apply Z.le_refl | apply mpot_mono; apply Z.le_refl]. }
      pose proof (sg_backed _ _ _ _ _ _ _ GM) as BK.
      (* [comment removed for export] *)
      assert (PK : pot A3 = pot A2).
      { apply (pot_keep_meta A2 A3 HW2 (fun c _ => f_equal (fun f => f c) (ah_active _ _ _ _ _ AH))).
        intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [| exact Hrx].
        rewrite (ah_other _ _ _ _ _ AH x); [exact Hx|]. intros ->. rewrite Hmd2 in Hx. injection Hx as <-. rewrite Hrd in Hrx. discriminate Hrx. }
      pose proof (is_wf _ _ _ _ _ _ (ii_is HII3)) as HW3.
      pose proof (pot_fresh A3 (rootA A3 sc m p L cnt aidx (a_xmaps A2) ab) sc m cnt HW3 Hsc Hact3
                    (fun c _ Hne => rootA_active_other A3 sc m p L cnt aidx (a_xmaps A2) ab c Hne)) as PF.
      assert (PF' : pot A3 + (cnt - 1) * (16 * size_class sc) <= pot (rootA A3 sc m p L cnt aidx (a_xmaps A2) ab)).
      { apply PF; [| exact (rootA_active_sc A3 sc m p L cnt aidx (a_xmaps A2) ab)
                   | exact (slots_of_grp _ m _ _ _ (rootA_m A3 sc m p L cnt aidx (a_xmaps A2) ab) eq_refl)
                   | clear - Hcnt; lia | exact Hspan].
        intros x mtx aibx slx Hx Hrx _.
        assert (Hxm : x <> m) by (intros ->; rewrite Hmd3 in Hx; injection Hx as <-; rewrite Hrd3 in Hrx; discriminate Hrx).
        unfold slots_of. rewrite (rootA_other A3 sc m p L cnt aidx (a_xmaps A2) Hact3 ab x Hxm), Hx, Hrx. reflexivity. }
      clear - BK PK PF' HLlen MP. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem alloc_slot_okW : alloc_slot_specW.
Proof.
  intros fuel W R sp0 argv envp cb D A s sp sc req K P HII Hsc Hreq Hfit Hfuel HF HS.
  pose proof (nest_rank_range sc) as Hnr.
  apply (alloc_slot_okI fuel W R sp0 argv envp cb D A s sp sc req K P HII Hsc Hreq Hfit Hfuel).
  - intros s' A' H1 H2 H3 H4 H5 G5 N5. apply (HF s' A' H1 H2 H3 H4); [| exact G5 | exact N5]. intros HWk. exact (inoroom_noroom sp0 argv envp cb A s (4 - nest_rank sc) ltac:(lia) (H5 HWk)).
  - intros s' A' g idx mt aib slots H1 H2 H3 _ H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 G5.
    exact (HS s' A' g idx mt aib slots H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 G5).
Qed.

Theorem alloc_slot_ok : alloc_slot_spec.
Proof. exact (alloc_slot_spec_of_W alloc_slot_okW). Qed.

End WithLayout.
