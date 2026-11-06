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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation u := bv_unsigned (only parsing).
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fact_dom : forall A x b, WF A -> facts A x b -> (LOCKA + 8 <= x < CTX_END) \/ dom A x.
Proof.
  intros A x b HW (f & Hf & [Hx ->]).
  destruct (has_where A HW f Hf) as [Hn [(Hc & H1 & H2) | [(_ & (pg & Hpg & Hlo & Hhi)) | (_ & (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi))]]].
  - left. llia.
  - right. left. exists pg. split; [exact Hpg | llia].
  - right. right. left. exists mr, mtr, aibr, slr. split; [exact Hmr|]. split; [exact Hrr|]. split; [exact Hml | llia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma IS_region : forall sp0 argv envp cb A s (m' : word -> option byte) h' lo n,
  IS sp0 argv envp cb A s ->
  (forall a : word, m' a = ms_mem s a \/ lo <= u a < lo + n) ->
  0x1000 <= lo -> lo + n <= alloc_ceiling -> (lo + n <= IMG_LO \/ IMG_HI <= lo) ->
  (forall x, dom A x -> ~ (lo <= x < lo + n)) ->
  (forall a : word, ms_mem s a <> None -> ~ (lo <= u a < lo + n) ->
     mcov (vm_maps (ms_vm s)) (u a) 1 -> mcov (vm_maps h') (u a) 1) ->
  (forall a : word, lo <= u a < lo + n -> m' a <> None -> mcov (vm_maps h') (u a) 1) ->
  IS sp0 argv envp cb A (upd s m' h').
Proof.
  intros sp0 argv envp cb A s m' h' lo n [W R C Wn E G] Hm Hlo Hhi Himg Hdom Hmono Hnew.
  pose proof alloc_ceiling_val as HCV.
  assert (OUT : forall a : word, ~ (lo <= u a < lo + n) -> m' a = ms_mem s a).
  { intros a Ha. destruct (Hm a) as [E0 | X]; [exact E0 | exfalso; exact (Ha X)]. }
  assert (ZN : forall a : word, m' a = ms_mem s a \/ mzone (u a)).
  { intros a. destruct (Hm a) as [E0 | X]; [left; exact E0 | right]. unfold mzone. llia. }
  constructor; cbn [ms_mem ms_vm upd].
  - exact W.
  - constructor.
    + intros x b Hf. rewrite <- (rep_facts A _ R x b Hf). apply mbyte_ext. apply OUT.
      pose proof (facts_addr64 A W x b Hf). rewrite uZ by llia.
      destruct (fact_dom A x b W Hf) as [Hc | Hd]; [unfold LOCKA, CTX_END in Hc; llia | exact (Hdom x Hd)].
    + intros x Hd. rewrite OUT; [exact (rep_dom A _ R x Hd)|]. pose proof (dom_addr64 A W x Hd). rewrite uZ by llia. exact (Hdom x Hd).
  - intros a Ha Hr Hi.
    assert (CASE : lo <= u a < lo + n \/ ~ (lo <= u a < lo + n)) by llia.
    destruct CASE as [IN | NI]; [exact (Hnew a IN Ha)|].
    pose proof (OUT a NI) as E0. apply (Hmono a); [rewrite <- E0; exact Ha | exact NI |].
    apply C; [rewrite <- E0; exact Ha | exact Hr | exact Hi].
  - apply WIN_upd. exact Wn.
  - apply (envok_frame sp0 argv envp s m' h' E Wn ZN).
  - apply (grd_frame cb (ms_mem s) m' G ZN).
Qed.

(* [comment removed for export] *)
Lemma IS_errno : forall sp0 argv envp cb A s e, IS sp0 argv envp cb A s ->
  IS sp0 argv envp cb A (upd s (errno_mem (ms_mem s) e) (ms_vm s)).
Proof.
  intros sp0 argv envp cb A s e HI. pose proof (is_wf _ _ _ _ _ _ HI) as HW. pose proof (is_rep _ _ _ _ _ _ HI) as HR.
  unfold errno_mem. rewrite A_ERRNO_eq.
  assert (Hlen : length (word_to_le_bytes 4 (Z_to_bv 64 e)) = 4%nat) by apply length_N_to_le_bytes.
  apply (IS_wbytes sp0 argv envp cb A A s ERRNO _ HI HW).
  - apply (rep_write A A (ms_mem s) ERRNO _ HR); rewrite ?Hlen; unfold ERRNO; try llia.
    + intros x b Hf. right. split; [| exact Hf].
      destruct (fact_dom A x b HW Hf) as [Hc | Hd]; [unfold LOCKA, CTX_END in Hc; cbn; llia|].
      pose proof (dom_heap A x HW Hd) as (lo & hi & Hh & Hx). unfold heap_range in Hh. cbn. llia.
    + intros x Hx. exact Hx.
    + exact (facts_addr64 A HW).
  - unfold ERRNO. llia.
  - rewrite Hlen. unfold ERRNO. cbn. llia.
  - intros x Hx. rewrite Hlen in Hx. unfold mzone, ERRNO in *. cbn in Hx. llia.
  - intros x Hx. rewrite Hlen in Hx. cbn in Hx. right. unfold ERRNO in Hx. llia.
Qed.

Lemma FR_errno : forall A s e, WF A -> FR A s A (upd s (errno_mem (ms_mem s) e) (ms_vm s)).
Proof.
  intros A s e HW. apply FR_mem. intros a. pose proof (u64_range a).
  unfold errno_mem. rewrite A_ERRNO_eq.
  assert (Hlen : length (word_to_le_bytes 4 (Z_to_bv 64 e)) = 4%nat) by apply length_N_to_le_bytes.
  assert (CASE : (ERRNO <= u a < ERRNO + 4) \/ ~ (ERRNO <= u a < ERRNO + 4)) by llia.
  destruct CASE as [IN | NI].
  - right. split; [right; exact IN|]. split.
    + intros p n Hp Hin. destruct (live_heap A p n HW Hp) as (Hn & H1 & H2 & H3 & _). pose proof (round16_ge n).
      unfold ERRNO in IN. ceil. llia.
    + intros Hm. apply wbytes_keeps; [rewrite Hlen, uZ by (unfold ERRNO; llia); unfold ERRNO; cbn; llia | exact Hm].
  - left. apply wbytes_other_Z; rewrite ?Hlen; unfold ERRNO in *; cbn; llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record VMcore (A : astate) (h : VmMaps) : Prop := {
  vc_grp : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     0 < mt_maplen mt ->
     In (Z_to_bv 64 (mt_mem mt), Z_to_bv 64 (grp_map_len mt)) (vm_maps h) /\
     region_free (vm_noaccess h) (Z_to_bv 64 (mt_mem mt)) (Z_to_bv 64 (grp_map_len mt)) = true;
  vc_res : vm_reserved h = segments_reserved ml_segs;
  vc_brk_valid : 0 < u (vm_brk h) /\ u (vm_start_brk h) <= u (vm_brk h) /\
                 page_aligned (u (vm_brk h)) /\ u (vm_brk h) <= alloc_ceiling;
  vc_pw : maps_pw (vm_maps h);
  vc_maps_wf : forall b sz, In (b, sz) (vm_maps h) -> 0 < u sz /\ u b + u sz <= alloc_ceiling /\
     0x1000 <= u b /\ (u b + u sz <= IMG_LO \/ IMG_HI <= u b);
  vc_na_in : forall b sz, In (b, sz) (vm_noaccess h) -> 0 < u sz /\ mcov (vm_maps h) (u b) (u sz);
  vc_areas_cov : forall pg, In pg (a_areas A) ->
     mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true;
  vc_pages_cov : forall pg, In pg (a_pages A) ->
     mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true;
  vc_top : alloc_top h = alloc_ceiling
}.

(* [comment removed for export] *)
Definition VMall (A : astate) (h : VmMaps) : Prop :=
  forall b sz, In (b, sz) (vm_maps h) ->
      (exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ 0 < mt_maplen mt /\
          bv_unsigned b = mt_mem mt /\ bv_unsigned sz = grp_map_len mt)
      \/ (bv_unsigned (vm_start_brk h) <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= bv_unsigned (vm_brk h))
      \/ (exists c l, In (c, l) (a_mblocks A ++ a_xmaps A) /\ c <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= c + l).

Lemma VMok_all : forall A h, VMok A h -> VMall A h.
Proof. intros A h HV. exact (vm_all A h HV). Qed.

Lemma VMok_core : forall A h, VMok A h -> VMcore A h.
Proof. intros A h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop]. constructor; assumption. Qed.

Lemma VMcore_ok : forall A h, VMcore A h -> VMall A h ->
  ((a_ctx A KBrk = 0 -> vm_brk h = vm_start_brk h) /\
     u (vm_brk h) - u (vm_start_brk h) <= 4096 * (Z.of_nat (length (a_areas A)) + 1)) ->
  (a_ctx A KBrk = 0 \/ a_ctx A KBrk = 2^64 - 1 \/
     (a_ctx A KBrk = u (vm_brk h) /\ 0 < u (vm_brk h) /\
      u (vm_start_brk h) <= u (vm_brk h) /\ page_aligned (u (vm_brk h)))) ->
  (a_ctx A KAac > 0 ->
     page_aligned (a_ctx A KAareas) /\ a_ctx A KAareas + 4096 * a_ctx A KAac <= alloc_ceiling /\
     map_contains (vm_maps h) (Z_to_bv 64 (a_ctx A KAareas)) (Z_to_bv 64 (4096 * a_ctx A KAac)) = true /\
     map_contains (vm_noaccess h) (Z_to_bv 64 (a_ctx A KAareas)) (Z_to_bv 64 (4096 * a_ctx A KAac)) = true) ->
  VMok A h.
Proof. intros A h [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop] Hall Hspan Hb Hr. constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma VMcore_restate : forall A A' h, VMcore A h ->
  (forall ma mt aib sl, a_meta A' ma = Some mt -> mt_role mt = RGroup aib sl -> 0 < mt_maplen mt ->
     exists mt0 aib0 sl0, a_meta A ma = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\
       mt_mem mt0 = mt_mem mt /\ mt_w32 mt0 = mt_w32 mt) ->
  (forall pg, In pg (a_areas A') -> In pg (a_areas A) \/
     (mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true)) ->
  (forall pg, In pg (a_pages A') -> In pg (a_pages A) \/
     (mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true)) ->
  VMcore A' h.
Proof.
  intros A A' h [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop] Hg Ha Hp. constructor; try assumption.
  - intros ma mt aib sl Hma Hr Hml. destruct (Hg ma mt aib sl Hma Hr Hml) as (mt0 & aib0 & sl0 & H0 & Hr0 & Em & Ew).
    assert (Eml : mt_maplen mt0 = mt_maplen mt) by (unfold mt_maplen; rewrite Ew; reflexivity).
    assert (Egl : grp_map_len mt0 = grp_map_len mt) by (unfold grp_map_len; rewrite Eml; reflexivity).
    rewrite <- Em, <- Egl. apply (Vg ma mt0 aib0 sl0 H0 Hr0). rewrite Eml. exact Hml.
  - intros pg Hpg. destruct (Ha pg Hpg) as [Ho | Hn]; [exact (Vac pg Ho) | exact Hn].
  - intros pg Hpg. destruct (Hp pg Hpg) as [Ho | Hn]; [exact (Vpc pg Ho) | exact Hn].
Qed.

(* [comment removed for export] *)
Lemma VMcore_same : forall A A' h, VMcore A h ->
  (forall ma mt aib sl, a_meta A' ma = Some mt -> mt_role mt = RGroup aib sl -> a_meta A ma = Some mt) ->
  a_areas A' = a_areas A -> a_pages A' = a_pages A -> VMcore A' h.
Proof.
  intros A A' h HV Hg Ea Ep. apply (VMcore_restate A A' h HV).
  - intros ma mt aib sl Hma Hr _. exists mt, aib, sl. split; [exact (Hg ma mt aib sl Hma Hr) | auto].
  - intros pg Hpg. left. rewrite <- Ea. exact Hpg.
  - intros pg Hpg. left. rewrite <- Ep. exact Hpg.
Qed.

(* [comment removed for export] *)
Lemma dom_mcov_core : forall A h x, WF A -> VMcore A h -> dom A x -> mcov (vm_maps h) x 1.
Proof.
  intros A h x HW HV [(pg & Hpg & Hx) | [(ma & mt & aib & slots & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx)]].
  - destruct (proj1 (vc_areas_cov A h HV pg Hpg)) as (b & sz & Hin & H1 & H2). exists b, sz. split; [exact Hin | llia].
  - destruct (vc_grp A h HV ma mt aib slots Hma Hr Hml) as [Hin _].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hce & Hpg).
    destruct (Hpg Hml) as [_ (R1 & R2 & R3 & R4)]. ceil.
    exists (Z_to_bv 64 (mt_mem mt)), (Z_to_bv 64 (grp_map_len mt)). split; [exact Hin|].
    unfold grp_map_len in *. rewrite !u_lit by llia. llia.
  - destruct (proj1 (vc_pages_cov A h HV pg Hpg)) as (b & sz & Hin & H1 & H2). exists b, sz. split; [exact Hin | llia].
Qed.

(* [comment removed for export] *)
Lemma dom_noaccess_free : forall A h x b sz, WF A -> VMcore A h -> dom A x -> In (b, sz) (vm_noaccess h) ->
  ~ (u b <= x < u b + u sz).
Proof.
  intros A h x b sz HW HV Hd Hin Hx. pose proof alloc_ceiling_val as HCV.
  destruct Hd as [(pg & Hpg & Hpx) | [(ma & mt & aib & slots & Hma & Hr & Hml & Hmx) | (pg & Hpg & Hpx)]].
  - destruct (vc_areas_cov A h HV pg Hpg) as [_ Hf]. destruct (wf_areas_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)].
    destruct (proj1 (region_free_spec _ _ _) Hf b sz Hin) as [H1 | H1]; rewrite !u_lit in H1 by llia; llia.
  - destruct (vc_grp A h HV ma mt aib slots Hma Hr Hml) as [_ Hf].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hce & Hpg).
    destruct (Hpg Hml) as [_ (R1 & R2 & R3 & R4)]. unfold grp_map_len in *.
    destruct (proj1 (region_free_spec _ _ _) Hf b sz Hin) as [H1 | H1]; rewrite !u_lit in H1 by llia; llia.
  - destruct (vc_pages_cov A h HV pg Hpg) as [_ Hf]. destruct (wf_pages_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)].
    destruct (proj1 (region_free_spec _ _ _) Hf b sz Hin) as [H1 | H1]; rewrite !u_lit in H1 by llia; llia.
Qed.

(* [comment removed for export] *)
Lemma na_nw : forall A h, VMcore A h -> maps_nw (vm_noaccess h).
Proof.
  intros A h HV b sz Hin. destruct (vc_na_in A h HV b sz Hin) as [Hsz (B & SZ & HinB & H1 & H2)].
  destruct (vc_maps_wf A h HV B SZ HinB) as (W1 & W2 & W3 & W4). ceil. llia.
Qed.

Lemma maps_nw_of : forall A h, VMcore A h -> maps_nw (vm_maps h).
Proof.
  intros A h HV b sz Hin. destruct (vc_maps_wf A h HV b sz Hin) as (W1 & W2 & W3 & W4). ceil. llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma VMcore_add_map : forall A h (a n b' : word),
  VMcore A h ->
  0 < u n -> u a + u n <= alloc_ceiling -> 0x1000 <= u a -> (u a + u n <= IMG_LO \/ IMG_HI <= u a) ->
  region_free (vm_maps h) a n = true ->
  0 < u b' -> u (vm_start_brk h) <= u b' -> page_aligned (u b') -> u b' <= alloc_ceiling ->
  VMcore A (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) b' (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros A h a n b' [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop] Hn Hce Hlo Himg Hfree Hb1 Hb2 Hb3 Hb4.
  constructor; cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_limit vm_init_sp alloc_top].
  - intros ma mt aib slots Hma Hr Hml. destruct (Vg ma mt aib slots Hma Hr Hml) as [H1 H2]. split; [right; exact H1 | exact H2].
  - exact Vres.
  - repeat split; assumption.
  - split; [exact Hfree | exact Vpw].
  - intros b sz [E | Hin]; [injection E as <- <-; repeat split; try assumption; llia | exact (Vmw b sz Hin)].
  - intros b sz Hin. destruct (Vna b sz Hin) as [H1 H2]. split; [exact H1 | apply mcov_cons; exact H2].
  - intros pg Hpg. destruct (Vac pg Hpg) as [H1 H2]. split; [apply mcov_cons; exact H1 | exact H2].
  - intros pg Hpg. destruct (Vpc pg Hpg) as [H1 H2]. split; [apply mcov_cons; exact H1 | exact H2].
  - exact Vtop.
Qed.

(* [comment removed for export] *)
Lemma VMcore_add_noacc : forall A h (a n : word),
  VMcore A h ->
  0 < u n -> u a + u n <= alloc_ceiling -> 0x1000 <= u a -> (u a + u n <= IMG_LO \/ IMG_HI <= u a) ->
  region_free (vm_maps h) a n = true ->
  VMcore A (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros A h a n HV Hn Hce Hlo Himg Hfree. pose proof HV as [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop].
  pose proof (proj1 (region_free_spec _ a n) Hfree) as FREE.
  assert (DISJ : forall x k, mcov (vm_maps h) x k -> 0 < k -> region_free [(a, n)] (Z_to_bv 64 x) (Z_to_bv 64 k) = true ->
            region_free ((a, n) :: vm_noaccess h) (Z_to_bv 64 x) (Z_to_bv 64 k) = region_free (vm_noaccess h) (Z_to_bv 64 x) (Z_to_bv 64 k)).
  { intros x k Hc Hk H1. change ((a, n) :: vm_noaccess h) with ([(a, n)] ++ vm_noaccess h). rewrite region_free_app, H1. reflexivity. }
  pose proof alloc_ceiling_val as HCV.
  assert (ONE : forall x k, mcov (vm_maps h) x k -> 0 < k -> 0 <= x -> x + k <= alloc_ceiling -> region_free [(a, n)] (Z_to_bv 64 x) (Z_to_bv 64 k) = true).
  { intros x k Hc Hk Hx Hxk. apply (proj2 (region_free_spec _ _ _)). intros b sz [E | []]. injection E as <- <-.
    rewrite !u_lit by llia. destruct (mcov_free_disj _ x k a n Hc Hfree); llia. }
  constructor; cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_limit vm_init_sp alloc_top].
  - intros ma mt aib slots Hma Hr Hml. destruct (Vg ma mt aib slots Hma Hr Hml) as [H1 H2]. split; [right; exact H1|].
    assert (Hin := H1). destruct (Vmw _ _ Hin) as (W1 & W2 & W3 & W4).
    pose proof (u64_range (Z_to_bv 64 (mt_mem mt))). pose proof (u64_range (Z_to_bv 64 (grp_map_len mt))).
    assert (Hc : mcov (vm_maps h) (u (Z_to_bv 64 (mt_mem mt))) (u (Z_to_bv 64 (grp_map_len mt)))) by (exists (Z_to_bv 64 (mt_mem mt)), (Z_to_bv 64 (grp_map_len mt)); split; [exact Hin | llia]).
    pose proof (ONE _ _ Hc W1 ltac:(llia) ltac:(llia)) as X. rewrite !Z_to_bv_bv_unsigned in X.
    change ((a, n) :: vm_noaccess h) with ([(a, n)] ++ vm_noaccess h). rewrite region_free_app, X, H2. reflexivity.
  - exact Vres.
  - exact Vbv.
  - split; [exact Hfree | exact Vpw].
  - intros b sz [E | Hin]; [injection E as <- <-; repeat split; try assumption; llia | exact (Vmw b sz Hin)].
  - intros b sz [E | Hin].
    + injection E as <- <-. split; [exact Hn|]. exists a, n. split; [left; reflexivity | llia].
    + destruct (Vna b sz Hin) as [H1 H2]. split; [exact H1 | apply mcov_cons; exact H2].
  - intros pg Hpg. destruct (Vac pg Hpg) as [H1 H2]. split; [apply mcov_cons; exact H1|].
    destruct H1 as (B & SZ & HinB & HB1 & HB2). destruct (Vmw B SZ HinB) as (W1 & W2 & W3 & W4).
    rewrite (DISJ pg 4096); [exact H2 | exists B, SZ; auto | llia |]. apply (ONE pg 4096); [exists B, SZ; auto | llia | llia | llia].
  - intros pg Hpg. destruct (Vpc pg Hpg) as [H1 H2]. split; [apply mcov_cons; exact H1|].
    destruct H1 as (B & SZ & HinB & HB1 & HB2). destruct (Vmw B SZ HinB) as (W1 & W2 & W3 & W4).
    rewrite (DISJ pg 4096); [exact H2 | exists B, SZ; auto | llia |]. apply (ONE pg 4096); [exists B, SZ; auto | llia | llia | llia].
  - exact Vtop.
Qed.

(* [comment removed for export] *)
Lemma VMcore_sub_noacc : forall A h (lo hi : Z),
  VMcore A h -> lo <= hi ->
  VMcore A (mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) lo hi) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros A h lo hi HV Hlh. pose proof (na_nw A h HV) as NW. pose proof HV as [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop].
  constructor; cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_limit vm_init_sp alloc_top]; try assumption.
  - intros ma mt aib slots Hma Hr Hml. destruct (Vg ma mt aib slots Hma Hr Hml) as [H1 H2]. split; [exact H1|].
    apply maps_subtract_free; [exact NW | exact H2].
  - intros b' sz' Hin. destruct (in_maps_subtract _ lo hi b' sz' Hin) as (b & sz & H0 & H1).
    destruct (iv_subtract_in b sz lo hi b' sz' (NW b sz H0) H1) as (A1 & A2 & A3 & A4).
    destruct (Vna b sz H0) as [Hsz Hc]. split; [exact (A4 Hsz)|]. apply (mcov_sub _ (u b) (u sz)); [exact Hc | llia | llia].
  - intros pg Hpg. destruct (Vac pg Hpg) as [H1 H2]. split; [exact H1 | apply maps_subtract_free; [exact NW | exact H2]].
  - intros pg Hpg. destruct (Vpc pg Hpg) as [H1 H2]. split; [exact H1 | apply maps_subtract_free; [exact NW | exact H2]].
Qed.

(* [comment removed for export] *)
Lemma VMcore_fixed_ok : forall A h (a n : word),
  WF A -> VMcore A h -> 0 < u n -> u a + u n <= alloc_ceiling ->
  mcov (vm_maps h) (u a) (u n) ->
  (forall x, dom A x -> ~ (u a <= x < u a + u n)) ->
  VMcore A (mkVmMapsFull (vm_reserved h) (vm_maps h) ((a, n) :: maps_subtract (vm_noaccess h) (u a) (u a + u n))
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros A h a n HW HV Hn Hnw Hc Hdom. pose proof (na_nw A h HV) as NW. pose proof HV as [Vg Vres Vbv Vpw Vmw Vna Vac Vpc Vtop].
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range a). pose proof (u64_range n).
  (* [comment removed for export] *)
  assert (APART : forall x k, 0 < k -> (forall y, x <= y < x + k -> dom A y) -> 0 <= x -> x + k <= alloc_ceiling ->
            region_free [(a, n)] (Z_to_bv 64 x) (Z_to_bv 64 k) = true).
  { intros x k Hk Hd Hx Hxk. apply (proj2 (region_free_spec _ _ _)). intros b sz [E | []]. injection E as <- <-.
    rewrite !u_lit by llia.
    destruct (Z.lt_ge_cases (x + k) (u a + 1)) as [L | L]; [left; llia|].
    destruct (Z.lt_ge_cases (u a + u n) (x + 1)) as [L2 | L2]; [right; llia|].
    exfalso. destruct (Z.lt_ge_cases x (u a)) as [L3 | L3].
    - apply (Hdom (u a)); [apply Hd; llia | llia].
    - apply (Hdom x); [apply Hd; llia | llia]. }
  constructor; cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_limit vm_init_sp alloc_top]; try assumption.
  - intros ma mt aib slots Hma Hr Hml. destruct (Vg ma mt aib slots Hma Hr Hml) as [H1 H2]. split; [exact H1|].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hce & Hpg).
    destruct (Hpg Hml) as [_ (R1 & R2 & R3 & R4)].
    change ((a, n) :: maps_subtract (vm_noaccess h) (u a) (u a + u n)) with ([(a, n)] ++ maps_subtract (vm_noaccess h) (u a) (u a + u n)).
    rewrite region_free_app. rewrite (APART (mt_mem mt) (grp_map_len mt)); [| unfold grp_map_len; llia | | llia | llia].
    + cbn [andb]. apply maps_subtract_free; [exact NW | exact H2].
    + intros y Hy. right; left. exists ma, mt, aib, slots. auto.
  - intros b' sz' [E | Hin].
    + injection E as <- <-. split; [exact Hn | exact Hc].
    + destruct (in_maps_subtract _ _ _ b' sz' Hin) as (b & sz & G0 & G1).
      destruct (iv_subtract_in b sz _ _ b' sz' (NW b sz G0) G1) as (A1 & A2 & A3 & A4).
      destruct (Vna b sz G0) as [Hsz Hcb]. split; [exact (A4 Hsz)|]. apply (mcov_sub _ (u b) (u sz)); [exact Hcb | llia | llia].
  - intros pg Hpg. destruct (Vac pg Hpg) as [H1 H2]. split; [exact H1|]. destruct (wf_areas_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)].
    change ((a, n) :: maps_subtract (vm_noaccess h) (u a) (u a + u n)) with ([(a, n)] ++ maps_subtract (vm_noaccess h) (u a) (u a + u n)).
    rewrite region_free_app. rewrite (APART pg 4096); [| llia | intros y Hy; left; exists pg; auto | llia | llia].
    cbn [andb]. apply maps_subtract_free; [exact NW | exact H2].
  - intros pg Hpg. destruct (Vpc pg Hpg) as [H1 H2]. split; [exact H1|]. destruct (wf_pages_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)].
    change ((a, n) :: maps_subtract (vm_noaccess h) (u a) (u a + u n)) with ([(a, n)] ++ maps_subtract (vm_noaccess h) (u a) (u a + u n)).
    rewrite region_free_app. rewrite (APART pg 4096); [| llia | intros y Hy; right; right; exists pg; auto | llia | llia].
    cbn [andb]. apply maps_subtract_free; [exact NW | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_apart : forall (b sz : word) (lo hi : Z), 0 < u sz -> u b + u sz <= 2^64 -> lo <= hi ->
  (u b + u sz <= lo \/ hi <= u b) -> iv_subtract b sz lo hi = [(b, sz)].
Proof.
  intros b sz lo hi Hsz Hnw Hlh Hd. unfold iv_subtract.
  pose proof (u64_range b). pose proof (u64_range sz).
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_lt (u b) lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (u b + u sz))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (u b) lo)) by lia.
    destruct (Z.ltb_spec hi (u b + u sz)).
    + rewrite Z.max_l by lia. replace (u b + u sz - u b) with (u sz) by lia. rewrite !Z_to_bv_bv_unsigned. reflexivity.
    + exfalso. lia.
Qed.

Lemma maps_subtract_apart : forall l (lo hi : Z), lo <= hi ->
  (forall b sz, In (b, sz) l -> 0 < u sz /\ u b + u sz <= 2^64 /\ (u b + u sz <= lo \/ hi <= u b)) ->
  maps_subtract l lo hi = l.
Proof.
  intros l lo hi Hlh. induction l as [|[b sz] l IH]; intros H; [reflexivity|].
  cbn [maps_subtract]. destruct (H b sz ltac:(left; reflexivity)) as (H1 & H2 & H3).
  rewrite (iv_subtract_apart b sz lo hi H1 H2 Hlh H3). cbn [app]. f_equal. apply IH. intros b0 sz0 Hin. apply H. right. exact Hin.
Qed.

Lemma iv_subtract_prefix : forall (b sz : word) (lo hi : Z), u b = lo -> lo < hi -> hi < u b + u sz -> u b + u sz <= 2^64 ->
  iv_subtract b sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (u b + u sz - hi))].
Proof.
  intros b sz lo hi E H1 H2 H3. unfold iv_subtract.
  pose proof (u64_range b). pose proof (u64_range sz).
  rewrite (proj2 (Z.ltb_ge (u b) lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (u b + u sz))) by lia.
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_up_Z_mod : forall z, page_round_up_Z z mod 4096 = 0.
Proof. intros z. unfold page_round_up_Z, page_size. apply Z.mod_mul. llia. Qed.

Lemma grant_ok_vm_spec : forall h a n, grant_ok_vm h a n = true <->
  (u a mod 4096 = 0 /\ 0 < u a /\ u a + n <= alloc_top h /\
   region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true /\ vm_backed_bytes h + n <= vm_limit h).
Proof.
  intros h a n. unfold grant_ok_vm, page_size. rewrite !andb_true_iff, Z.eqb_eq, Z.ltb_lt, !Z.leb_le. tauto.
Qed.

Lemma grant_ok_na_vm_spec : forall h a n, grant_ok_na_vm h a n = true <->
  (u a mod 4096 = 0 /\ 0 < u a /\ u a + n <= alloc_top h /\
   region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true).
Proof.
  intros h a n. unfold grant_ok_na_vm, page_size. rewrite !andb_true_iff, Z.eqb_eq, Z.ltb_lt, !Z.leb_le. tauto.
Qed.

Lemma map_contains_cons : forall e l a n, map_contains l a n = true -> map_contains (e :: l) a n = true.
Proof. intros e l a n H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma u_sub_small : forall a b : word, u b <= u a -> u (a - b)%bv = u a - u b.
Proof.
  intros a b H. rewrite bv_sub_unsigned, bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). pose proof (u64_range b). llia.
Qed.

Lemma aligned_ge_page : forall x, x mod 4096 = 0 -> 0 < x -> 4096 <= x.
Proof. intros x Hm Hx. pose proof (Z.div_mod x 4096 ltac:(llia)). lnia. Qed.

Lemma zfill_in : forall (a n : word) m (x : word),
  u a <= u x < u a + u n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by llia. rewrite (proj2 (Z.ltb_lt _ _)) by llia. reflexivity.
Qed.

Lemma unfill_in : forall (a n : word) m (x : word),
  u a <= u x < u a + u n -> unfill a n m x = None.
Proof.
  intros a n m x Hx. unfold unfill.
  rewrite (proj2 (Z.leb_le _ _)) by llia. rewrite (proj2 (Z.ltb_lt _ _)) by llia. reflexivity.
Qed.

(* [comment removed for export] *)

Definition xadd (A : astate) (c l : Z) : astate := set_xmaps A ((c, l) :: a_xmaps A).

Lemma WF_set_xmaps : forall A l, WF A -> WF (set_xmaps A l).
Proof.
  intros A l HW. destruct HW. constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps set_xmaps]; assumption.
Qed.

Lemma IS_set_xmaps : forall sp0 argv envp cb A s l, IS sp0 argv envp cb A s -> IS sp0 argv envp cb (set_xmaps A l) s.
Proof.
  intros sp0 argv envp cb A s l [W R C Wn E G]. constructor; try assumption.
  - apply WF_set_xmaps. exact W.
  - destruct R as [R1 R2]. constructor; assumption.
Qed.

Lemma VMcore_set_xmaps : forall A h l, VMcore A h -> VMcore (set_xmaps A l) h.
Proof. intros A h l HV. apply (VMcore_same A _ h HV); [intros ma mt aib sl Hm _; exact Hm | reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma VMall_xadd : forall A h (a n : word) res na sb lim mb isp,
  VMall A h -> vm_start_brk h = sb ->
  VMall (xadd A (u a) (u n)) (mkVmMapsFull res ((a, n) :: vm_maps h) na sb (vm_brk h) lim mb isp).
Proof.
  intros A h a n res na sb lim mb isp HA Esb b sz Hin. cbn [vm_maps vm_start_brk vm_brk] in *. subst sb.
  destruct Hin as [E | Hin].
  - injection E as <- <-. right; right. exists (u a), (u n). split; [| llia].
    cbn [xadd set_xmaps a_mblocks a_xmaps]. apply in_or_app. right. left. reflexivity.
  - destruct (HA b sz Hin) as [G | [B | (c & l & Hcl & H1 & H2)]]; [left; exact G | right; left; exact B | right; right].
    exists c, l. split; [| llia]. cbn [xadd set_xmaps a_mblocks a_xmaps].
    apply in_app_or in Hcl. apply in_or_app. destruct Hcl as [H | H]; [left; exact H | right; right; exact H].
Qed.

(* [comment removed for export] *)
Lemma mmap_grant_facts : forall sp0 argv envp cb A s (a len : word),
  IS sp0 argv envp cb A s -> VMcore A (ms_vm s) -> 0 < u len -> u len < 2^62 ->
  grant_ok_vm (ms_vm s) a (page_round_up_Z (u len)) = true ->
  u (page_round_up len) = page_round_up_Z (u len) /\
  u len <= page_round_up_Z (u len) /\
  u a mod 4096 = 0 /\ 0x1000 <= u a /\ u a + page_round_up_Z (u len) <= alloc_ceiling /\
  (u a + page_round_up_Z (u len) <= IMG_LO \/ IMG_HI <= u a) /\
  region_free (vm_maps (ms_vm s)) a (page_round_up len) = true /\
  region_free (vm_noaccess (ms_vm s)) a (page_round_up len) = true /\
  (forall x, u a <= x < u a + page_round_up_Z (u len) -> ~ dom A x /\ ms_mem s (Z_to_bv 64 x) = None) /\
  (forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> u a + page_round_up_Z (u len) <= u b \/ u b + u sz <= u a) /\
  vm_backed_bytes (ms_vm s) + page_round_up_Z (u len) <= vm_limit (ms_vm s).
Proof.
  intros sp0 argv envp cb A s a len HI HV Hlen Hlen2 Hg.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range a).
  pose proof (is_wf _ _ _ _ _ _ HI) as HW. pose proof (is_cov _ _ _ _ _ _ HI) as HC.
  pose proof (page_round_up_Z_bounds (u len) ltac:(llia)) as [B1 B2]. unfold page_size in B2.
  apply grant_ok_vm_spec in Hg. destruct Hg as (G1 & G2 & G3 & G4 & G5). rewrite (vc_top A _ HV) in G3.
  assert (EnZ : u (page_round_up len) = page_round_up_Z (u len)) by (unfold page_round_up; apply uZ; llia).
  assert (En : Z_to_bv 64 (page_round_up_Z (u len)) = page_round_up len) by reflexivity.
  rewrite En in G4. rewrite region_free_app in G4. apply andb_true_iff in G4. destruct G4 as [Gr Gm].
  pose proof (region_free_image a (page_round_up len) ltac:(rewrite <- (vc_res A _ HV); exact Gr) ltac:(rewrite EnZ; llia)) as Himg.
  rewrite EnZ in Himg.
  pose proof (proj1 (region_free_spec _ _ _) Gm) as FREE. rewrite EnZ in FREE.
  pose proof (aligned_ge_page (u a) G1 G2) as Hlo.
  assert (NODOM : forall x, u a <= x < u a + page_round_up_Z (u len) -> ~ dom A x).
  { intros x Hx Hd. pose proof (dom_mcov_core A (ms_vm s) x HW HV Hd) as Hc.
    destruct (mcov_free_disj _ x 1 a (page_round_up len) Hc Gm); rewrite ?EnZ in *; llia. }
  split; [exact EnZ|]. split; [exact B1|]. split; [exact G1|]. split; [exact Hlo|]. split; [exact G3|]. split; [exact Himg|].
  split; [exact Gm|]. split; [| split; [| split; [exact FREE | exact G5]]].
  - apply (proj2 (region_free_spec _ _ _)). intros b sz Hin. rewrite EnZ.
    destruct (vc_na_in A _ HV b sz Hin) as [Hsz (B & SZ & HinB & HB1 & HB2)].
    destruct (FREE B SZ HinB); llia.
  - intros x Hx. split; [exact (NODOM x Hx)|].
    destruct (ms_mem s (Z_to_bv 64 x)) eqn:E; [| reflexivity]. exfalso.
    pose proof (HC (Z_to_bv 64 x) ltac:(rewrite E; discriminate) ltac:(rewrite uZ by llia; llia) ltac:(rewrite uZ by llia; llia)) as Hc.
    rewrite uZ in Hc by llia. destruct (mcov_free_disj _ x 1 a (page_round_up len) Hc Gm); rewrite ?EnZ in *; llia.
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_ok : forall sp0 argv envp cb A s (a len : word),
  IS sp0 argv envp cb A s -> VMok A (ms_vm s) -> 0 < u len -> u len < 2^62 ->
  grant_ok_vm (ms_vm s) a (page_round_up_Z (u len)) = true ->
  let A' := xadd A (u a) (page_round_up_Z (u len)) in
  IS sp0 argv envp cb A' (upd s (zfill a (page_round_up len) (ms_mem s)) (vm_mmap a (page_round_up len) (ms_vm s))) /\
  VMok A' (vm_mmap a (page_round_up len) (ms_vm s)).
Proof.
  intros sp0 argv envp cb A s a len HI HVo Hlen Hlen2 Hg. pose proof (VMok_core A _ HVo) as HV. cbn beta zeta.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range a).
  destruct (mmap_grant_facts sp0 argv envp cb A s a len HI HV Hlen Hlen2 Hg) as (EnZ & B1 & G1 & Glo & Gce & Gimg & Gm & Gna & Gdom & Gdisj & Gbud).
  set (n := page_round_up len) in *. set (nZ := page_round_up_Z (u len)) in *.
  split.
  - apply IS_set_xmaps. apply (IS_region sp0 argv envp cb A s _ _ (u a) nZ HI).
    + intros x. pose proof (u64_range x).
      assert (CASE : u a <= u x < u a + nZ \/ ~ (u a <= u x < u a + nZ)) by llia. destruct CASE as [IN | NI]; [right; exact IN | left].
      apply zfill_out. rewrite EnZ. llia.
    + exact Glo.
    + exact Gce.
    + exact Gimg.
    + intros x Hd Hx. exact (proj1 (Gdom x Hx) Hd).
    + intros x _ _ Hc. cbn [vm_maps vm_mmap]. apply mcov_cons. exact Hc.
    + intros x Hx _. cbn [vm_maps vm_mmap]. exists a, n. split; [left; reflexivity | rewrite EnZ; llia].
  - pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    apply VMcore_ok; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_mmap a_ctx a_areas xadd set_xmaps].
    + apply VMcore_set_xmaps. unfold vm_mmap. destruct (vc_brk_valid A _ HV) as (K1 & K2 & K3 & K4).
      apply (VMcore_add_map A (ms_vm s) a n (vm_brk (ms_vm s)) HV); rewrite ?EnZ; try assumption; llia.
    + unfold vm_mmap. rewrite <- EnZ. apply VMall_xadd; [exact Vall | reflexivity].
    + exact Vspan.
    + exact Vb.
    + intros Haac. destruct (Va Haac) as (R1 & R2 & R3 & R4). repeat split; try assumption. apply map_contains_cons. exact R3.
Qed.

(* [comment removed for export] *)
Lemma mmap_none_ok : forall sp0 argv envp cb A s (a len : word),
  IS sp0 argv envp cb A s -> VMok A (ms_vm s) -> 0 < u len -> u len < 2^62 ->
  grant_ok_vm (ms_vm s) a (page_round_up_Z (u len)) = true ->
  let A' := xadd A (u a) (page_round_up_Z (u len)) in
  IS sp0 argv envp cb A' (upd s (unfill a (page_round_up len) (ms_mem s)) (vm_noacc a (page_round_up len) (ms_vm s))) /\
  VMok A' (vm_noacc a (page_round_up len) (ms_vm s)).
Proof.
  intros sp0 argv envp cb A s a len HI HVo Hlen Hlen2 Hg. pose proof (VMok_core A _ HVo) as HV. cbn beta zeta.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range a).
  destruct (mmap_grant_facts sp0 argv envp cb A s a len HI HV Hlen Hlen2 Hg) as (EnZ & B1 & G1 & Glo & Gce & Gimg & Gm & Gna & Gdom & Gdisj & Gbud).
  set (n := page_round_up len) in *. set (nZ := page_round_up_Z (u len)) in *.
  split.
  - apply IS_set_xmaps. apply (IS_region sp0 argv envp cb A s _ _ (u a) nZ HI).
    + intros x. pose proof (u64_range x).
      assert (CASE : u a <= u x < u a + nZ \/ ~ (u a <= u x < u a + nZ)) by llia. destruct CASE as [IN | NI]; [right; exact IN | left].
      apply unfill_out. rewrite EnZ. llia.
    + exact Glo.
    + exact Gce.
    + exact Gimg.
    + intros x Hd Hx. exact (proj1 (Gdom x Hx) Hd).
    + intros x _ _ Hc. cbn [vm_maps vm_noacc]. apply mcov_cons. exact Hc.
    + intros x Hx Hm. exfalso. apply Hm. apply unfill_in. rewrite EnZ. exact Hx.
  - pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    apply VMcore_ok; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_noacc a_ctx a_areas xadd set_xmaps].
    + apply VMcore_set_xmaps. unfold vm_noacc. apply (VMcore_add_noacc A (ms_vm s) a n HV); rewrite ?EnZ; try assumption; llia.
    + unfold vm_noacc. rewrite <- EnZ. apply VMall_xadd; [exact Vall | reflexivity].
    + exact Vspan.
    + exact Vb.
    + intros Haac. destruct (Va Haac) as (R1 & R2 & R3 & R4). repeat split; try assumption; apply map_contains_cons; assumption.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_facts : forall A h (req : word),
  VMcore A h -> brk_grow_ok_vm h req req = true -> u (vm_brk h) < u req -> page_aligned (u req) ->
  u req <= alloc_ceiling /\
  region_free (vm_reserved h ++ vm_maps h) (vm_brk h) (Z_to_bv 64 (u req - u (vm_brk h))) = true /\
  vm_backed_bytes h + (u req - u (vm_brk h)) <= vm_limit h.
Proof.
  intros A h req HV Hok Hlt Hal. destruct (vc_brk_valid A h HV) as (K1 & K2 & K3 & K4).
  pose proof (u64_range req). pose proof (u64_range (vm_brk h)).
  unfold brk_grow_ok_vm in Hok.
  rewrite (proj2 (Z.ltb_lt 0 _) K1), (proj2 (Z.ltb_lt _ _) Hlt) in Hok. cbn [andb] in Hok.
  unfold page_aligned in *.
  rewrite !page_round_up_Z_aligned in Hok by (unfold page_size; llia).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hok.
  apply andb_true_iff in Hok. destruct Hok as [H1 H3]. apply andb_true_iff in H1. destruct H1 as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H3. rewrite u_sub_small in H3 by llia.
  rewrite Z_to_bv_bv_unsigned in H2. rewrite (vc_top A h HV) in H1. unfold page_size in H2.
  split; [exact H1|]. split; [| exact H3].
  apply (region_free_sub _ (vm_brk h) (Z_to_bv 64 (u req + 4096 - u (vm_brk h)))); [exact H2 | lia |].
  ceil. rewrite !uZ by lia. lia.
Qed.

Lemma brk_grow_state : forall sp0 argv envp cb A s (req : word),
  IS sp0 argv envp cb A s -> VMcore A (ms_vm s) ->
  brk_grow_ok_vm (ms_vm s) req req = true -> u (vm_brk (ms_vm s)) < u req -> page_aligned (u req) ->
  let b := vm_brk (ms_vm s) in
  let m' := apply_zeros (ms_mem s) (brk_zeros req req b) in
  IS sp0 argv envp cb A (upd s m' (vm_brk_grow req (ms_vm s))) /\
  VMcore A (vm_brk_grow req (ms_vm s)) /\
  vm_maps (vm_brk_grow req (ms_vm s)) = (b, Z_to_bv 64 (u req - u b)) :: vm_maps (ms_vm s) /\
  (forall x, u b <= x < u req -> ~ dom A x /\ ms_mem s (Z_to_bv 64 x) = None) /\
  (forall b0 sz, In (b0, sz) (vm_maps (ms_vm s)) -> u req <= u b0 \/ u b0 + u sz <= u b) /\
  (forall x : word, u b <= u x < u req -> m' x = Some (Z_to_bv 8 0)) /\
  (forall x : word, ~ (u b <= u x < u req) -> m' x = ms_mem s x) /\
  u req <= alloc_ceiling /\ 0x1000 <= u b /\ (u req <= IMG_LO \/ IMG_HI <= u b) /\
  vm_live_bytes (vm_brk_grow req (ms_vm s)) = vm_live_bytes (ms_vm s) + (u req - u b) /\
  vm_backed_bytes (ms_vm s) + (u req - u b) <= vm_limit (ms_vm s).
Proof.
  intros sp0 argv envp cb A s req HI HV Hok Hlt Hal. cbn beta zeta.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range req). pose proof (u64_range (vm_brk (ms_vm s))).
  pose proof (is_wf _ _ _ _ _ _ HI) as HW. pose proof (is_cov _ _ _ _ _ _ HI) as HC.
  destruct (vc_brk_valid A _ HV) as (K1 & K2 & K3 & K4).
  destruct (brk_grow_facts A (ms_vm s) req HV Hok Hlt Hal) as (F1 & F2 & F3).
  set (b := vm_brk (ms_vm s)) in *. set (n := Z_to_bv 64 (u req - u b)) in *.
  assert (En : u n = u req - u b) by (unfold n; apply uZ; llia).
  rewrite region_free_app in F2. apply andb_true_iff in F2. destruct F2 as [Fr Fm].
  pose proof (region_free_image b n ltac:(rewrite <- (vc_res A _ HV); exact Fr) ltac:(rewrite En; llia)) as Himg. rewrite En in Himg.
  pose proof (proj1 (region_free_spec _ _ _) Fm) as FREE. rewrite En in FREE.
  unfold page_aligned in *. pose proof (aligned_ge_page (u b) K3 K1) as Hlo.
  assert (Esub : (req - b)%bv = n) by (apply bv_eq; rewrite u_sub_small by llia; rewrite En; reflexivity).
  assert (Emaps : vm_maps (vm_brk_grow req (ms_vm s)) = (b, n) :: vm_maps (ms_vm s)) by (unfold vm_brk_grow; cbn [vm_maps]; fold b; rewrite Esub; reflexivity).
  assert (Ezs : brk_zeros req req b = [(b, n)]).
  { unfold n. rewrite brk_zeros_aligned_grow; unfold page_size; try llia.
    - rewrite page_round_up_Z_aligned by (unfold page_size; llia). reflexivity.
    - intros E. rewrite E in Hlt. rewrite uZ in Hlt by llia. llia. }
  rewrite Ezs, apply_zeros_one.
  assert (ZIN : forall x : word, u b <= u x < u req -> zmem (ms_mem s) b n x = Some (Z_to_bv 8 0)).
  { intros x Hx. unfold zmem. rewrite (proj2 (Z.leb_le _ _)) by llia. rewrite (proj2 (Z.ltb_lt _ _)) by (rewrite En; llia). reflexivity. }
  assert (ZOUT : forall x : word, ~ (u b <= u x < u req) -> zmem (ms_mem s) b n x = ms_mem s x).
  { intros x Hx. apply zmem_out. rewrite En. llia. }
  assert (NODOM : forall x, u b <= x < u req -> ~ dom A x).
  { intros x Hx Hd. pose proof (dom_mcov_core A (ms_vm s) x HW HV Hd) as Hc.
    destruct (mcov_free_disj _ x 1 b n Hc Fm); rewrite ?En in *; llia. }
  assert (HVg : VMcore A (vm_brk_grow req (ms_vm s))).
  { unfold vm_brk_grow. fold b. rewrite Esub. apply (VMcore_add_map A (ms_vm s) b n req HV); rewrite ?En; try llia; [exact Fm | exact Hal]. }
  split; [| split; [exact HVg | split; [exact Emaps | split; [| split; [| split; [exact ZIN | split; [exact ZOUT|]]]]]]].
  - apply (IS_region sp0 argv envp cb A s _ _ (u b) (u req - u b) HI).
    + intros x. assert (CASE : u b <= u x < u req \/ ~ (u b <= u x < u req)) by llia.
      destruct CASE as [IN | NI]; [right; llia | left; exact (ZOUT x NI)].
    + exact Hlo.
    + llia.
    + llia.
    + intros x Hd Hx. apply (NODOM x); [llia | exact Hd].
    + intros x _ _ Hc. rewrite Emaps. apply mcov_cons. exact Hc.
    + intros x Hx _. rewrite Emaps. exists b, n. split; [left; reflexivity | rewrite En; llia].
  - intros x Hx. split; [apply NODOM; exact Hx|].
    destruct (ms_mem s (Z_to_bv 64 x)) eqn:E; [| reflexivity]. exfalso.
    pose proof (HC (Z_to_bv 64 x) ltac:(rewrite E; discriminate) ltac:(rewrite uZ by llia; llia) ltac:(rewrite uZ by llia; llia)) as Hc.
    rewrite uZ in Hc by llia. destruct (mcov_free_disj _ x 1 b n Hc Fm); rewrite ?En in *; llia.
  - intros b0 sz Hin. destruct (FREE b0 sz Hin); llia.
  - split; [exact F1|]. split; [exact Hlo|]. split; [llia|]. split; [| exact F3].
    unfold vm_live_bytes. rewrite Emaps. cbn [live_bytes]. rewrite En. unfold vm_live_bytes. llia.
Qed.

(* [comment removed for export] *)
Lemma mprotect_page_state : forall sp0 argv envp cb A s (p : word),
  IS sp0 argv envp cb A s -> VMcore A (ms_vm s) ->
  mcov (vm_noaccess (ms_vm s)) (u p) 4096 -> u p + 4096 <= alloc_ceiling ->
  let n := Z_to_bv 64 4096 in
  let m' := zfill p n (ms_mem s) in
  let h' := vm_unprotect p n (ms_vm s) in
  IS sp0 argv envp cb A (upd s m' h') /\ VMcore A h' /\
  vm_maps h' = vm_maps (ms_vm s) /\ vm_noaccess h' = maps_subtract (vm_noaccess (ms_vm s)) (u p) (u p + u n) /\
  mcov (vm_maps (ms_vm s)) (u p) 4096 /\ 0x1000 <= u p /\ (u p + 4096 <= IMG_LO \/ IMG_HI <= u p) /\
  (forall x, u p <= x < u p + 4096 -> ~ dom A x) /\
  (forall x : word, u p <= u x < u p + 4096 -> m' x = Some (Z_to_bv 8 0)) /\
  (forall x : word, ~ (u p <= u x < u p + 4096) -> m' x = ms_mem s x).
Proof.
  intros sp0 argv envp cb A s p HI HV Hna Hce. cbn beta zeta.
  pose proof alloc_ceiling_val as HCV. pose proof (u64_range p).
  pose proof (is_wf _ _ _ _ _ _ HI) as HW.
  set (n := Z_to_bv 64 4096). assert (En : u n = 4096) by (unfold n; apply uZ; llia).
  destruct Hna as (nb & nsz & Hnin & Hn1 & Hn2).
  destruct (vc_na_in A _ HV nb nsz Hnin) as [Hnsz (B & SZ & HinB & HB1 & HB2)].
  destruct (vc_maps_wf A _ HV B SZ HinB) as (W1 & W2 & W3 & W4).
  assert (Hcov : mcov (vm_maps (ms_vm s)) (u p) 4096) by (exists B, SZ; split; [exact HinB | llia]).
  assert (NODOM : forall x, u p <= x < u p + 4096 -> ~ dom A x).
  { intros x Hx Hd. apply (dom_noaccess_free A (ms_vm s) x nb nsz HW HV Hd Hnin). llia. }
  assert (ZIN : forall x : word, u p <= u x < u p + 4096 -> zfill p n (ms_mem s) x = Some (Z_to_bv 8 0)).
  { intros x Hx. apply zfill_in. rewrite En. exact Hx. }
  assert (ZOUT : forall x : word, ~ (u p <= u x < u p + 4096) -> zfill p n (ms_mem s) x = ms_mem s x).
  { intros x Hx. apply zfill_out. rewrite En. llia. }
  assert (HV' : VMcore A (vm_unprotect p n (ms_vm s))).
  { unfold vm_unprotect. apply (VMcore_sub_noacc A (ms_vm s) (u p) (u p + u n) HV). rewrite En. llia. }
  split; [| split; [exact HV' | split; [reflexivity | split; [reflexivity | split; [exact Hcov | split; [llia | split; [llia | split; [exact NODOM | split; [exact ZIN | exact ZOUT]]]]]]]]].
  apply (IS_region sp0 argv envp cb A s _ _ (u p) 4096 HI).
  - intros x. assert (CASE : u p <= u x < u p + 4096 \/ ~ (u p <= u x < u p + 4096)) by llia.
    destruct CASE as [IN | NI]; [right; exact IN | left; exact (ZOUT x NI)].
  - llia.
  - llia.
  - llia.
  - intros x Hd Hx. exact (NODOM x Hx Hd).
  - intros x _ _ Hc. cbn [vm_maps vm_unprotect]. exact Hc.
  - intros x Hx _. cbn [vm_maps vm_unprotect]. apply (mcov_sub _ (u p) 4096); [exact Hcov | llia | llia].
Qed.

End WithLayout.
