(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WFree2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WSlot2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2.MI_WNtf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WSlot2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2.MI_WSlot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.MI_WMalloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.MI_Sim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Contracts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Lemma simrel_init : forall resv, SIMREL (strip (minit 0 resv)) (led_init resv).
Proof. intros resv. exists (minit 0 resv), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; lia| reflexivity]. Qed.

Lemma creach_simrel : forall cs L, creach cs L -> SIMREL cs L.
Proof. exact creach_sim. Qed.

Theorem simrel_malloc_contract : forall cs L n,
  SIMREL cs L -> 0 <= n ->
  ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
  intros cs L n SR Hn. destruct SR as (st & BL & LS & <- & INV & LIVE).
  apply (ctree_ok_paths _ L (fun _ _ => True)).
  - apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
  - intros L' [cs' r] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
    destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE', LIVE. exact NI.
Qed.

Theorem simrel_free_contract : forall cs L c,
  SIMREL cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
  intros cs L c SR Hc. destruct SR as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.

Theorem simrel_malloc_step : forall cs L n L' cs' r,
  SIMREL cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
  SIMREL cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end).
Proof.
  intros cs L n L' cs' r SR Hn CP. destruct SR as (st & BL & LS & <- & INV & LIVE).
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
  destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
  rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
  destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
  - destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
    exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
  - destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
Qed.

Theorem simrel_free_step : forall cs L c L' cs',
  SIMREL cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
  SIMREL cs' (set_live (ap_remove c (ld_live L')) L').
Proof.
  intros cs L c L' cs' SR Hc CP. destruct SR as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
  rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
  exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_ranges_lranges : forall cs L x, SIMREL cs L -> In x (live_ranges cs) <-> In x (lranges L).
Proof.
  intros cs L x (st & BL & LS & <- & INV & _). pose proof (proj1 INV) as IR.
  assert (Ereg : s_regions (strip st) = s_regions st) by reflexivity.
  assert (Eres : s_reserved (strip st) = s_reserved st) by reflexivity.
  unfold live_ranges, lranges. rewrite Ereg, Eres, (ir_resv _ _ _ IR). rewrite !in_app_iff. split.
  - intros [H|H]; [left; exact H|]. apply in_map_iff in H as ([rid r] & <- & Hin). cbn [snd].
    apply list_elem_of_In, elem_of_map_to_list in Hin. unfold region_live_range.
    destruct (r_kind r) eqn:K.
    + right; right; right. destruct (ld_brkreg L) as [[b l]|] eqn:E.
      * destruct (proj1 (ir_brkreg _ _ _ IR b l) E) as (rid' & r' & Hr' & Kr' & <- & <-).
        rewrite <- (ir_brk1 _ _ _ IR rid rid' r r' Hin Hr' K Kr') in Hr'. rewrite Hin in Hr'. injection Hr' as <-. left. reflexivity.
      * exfalso. assert (HH : ld_brkreg L = Some (r_base r, r_len r)) by (apply (proj2 (ir_brkreg _ _ _ IR _ _)); exists rid, r; auto). rewrite E in HH. discriminate.
    + right; right; left. apply in_map_iff. exists (r_base r, r_len r, frontier st rid r / PGSZ - 1). split; [reflexivity|].
      apply (Permutation_in _ (Permutation_sym (ir_metas _ _ _ IR))). apply in_map_iff. exists (rid, r). split; [reflexivity|].
      apply List.filter_In. split; [apply list_elem_of_In, elem_of_map_to_list; exact Hin| rewrite K; reflexivity].
    + right; left. apply in_map_iff. exists (r_base r, r_len r). split; [reflexivity|].
      apply (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR))). apply in_map_iff. exists (rid, r). split; [reflexivity|].
      apply List.filter_In. split; [apply list_elem_of_In, elem_of_map_to_list; exact Hin| rewrite K; reflexivity].
  - intros [H|[H|[H|H]]]; [left; exact H| right| right| right].
    + apply in_map_iff in H as ([b l] & <- & Hg). apply (Permutation_in _ (ir_groups _ _ _ IR)) in Hg.
      apply in_map_iff in Hg as ([rid r] & E & Hf). cbn in E. injection E as <- <-. apply List.filter_In in Hf as [Hin Hk].
      apply in_map_iff. exists (rid, r). split; [| apply list_elem_of_In, elem_of_map_to_list; apply list_elem_of_In, elem_of_map_to_list in Hin; exact Hin].
      cbn [snd] in Hk |- *. unfold region_live_range. destruct (r_kind r); try discriminate Hk; reflexivity.
    + apply in_map_iff in H as ([[b l] k] & <- & Hm). apply (Permutation_in _ (ir_metas _ _ _ IR)) in Hm.
      apply in_map_iff in Hm as ([rid r] & E & Hf). cbn in E. injection E as <- <- _. apply List.filter_In in Hf as [Hin Hk].
      apply in_map_iff. exists (rid, r). split; [| apply list_elem_of_In, elem_of_map_to_list; apply list_elem_of_In, elem_of_map_to_list in Hin; exact Hin].
      cbn [snd fst] in Hk |- *. unfold region_live_range. destruct (r_kind r); try discriminate Hk; reflexivity.
    + destruct (ld_brkreg L) as [[b l]|] eqn:E; [|destruct H]. destruct H as [<-|[]].
      destruct (proj1 (ir_brkreg _ _ _ IR b l) E) as (rid & r & Hr & Kr & <- & <-).
      apply in_map_iff. exists (rid, r). split; [| apply list_elem_of_In, elem_of_map_to_list; exact Hr].
      cbn [snd]. unfold region_live_range. rewrite Kr. reflexivity.
Qed.

Lemma ranges_free_set_eq : forall l1 l2 a n, (forall x, In x l1 <-> In x l2) -> ranges_free l1 a n = ranges_free l2 a n.
Proof.
  intros l1 l2 a n H. unfold ranges_free.
  destruct (forallb _ l1) eqn:E1; destruct (forallb _ l2) eqn:E2; try reflexivity.
  - exfalso. assert (E2' : forallb (fun bm : Z * Z => iv_disjoint a n (fst bm) (snd bm)) l2 = true); [|congruence].
    apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) E1). apply H. exact Hx.
  - exfalso. assert (E1' : forallb (fun bm : Z * Z => iv_disjoint a n (fst bm) (snd bm)) l1 = true); [|congruence].
    apply forallb_forall. intros x Hx. apply (proj1 (forallb_forall _ _) E2). apply H. exact Hx.
Qed.

Corollary live_ranges_free_lranges : forall cs L a n, SIMREL cs L -> ranges_free (live_ranges cs) a n = ranges_free (lranges L) a n.
Proof. intros cs L a n SR. apply ranges_free_set_eq. intros x. apply live_ranges_lranges. exact SR. Qed.


End CeilWrap.
