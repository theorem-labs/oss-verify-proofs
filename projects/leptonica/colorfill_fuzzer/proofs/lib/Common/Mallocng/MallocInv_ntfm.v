(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_tryavail MallocInv_ameta_base MallocInv_ameta_iface
  MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_nt1.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeMeta.
  Variable B : astate.
  Hypothesis HW : WF B.
  Variables (g : Z) (mg : meta_rec) (fl : list Z) (h t : Z).
  Hypothesis Hg : a_meta B g = Some mg.
  Hypothesis Hrg : mt_role mg = RDead.
  Hypothesis Hfl : a_freelist B = fl.
  Hypothesis Hh : h = hd g fl.
  Hypothesis Ht : t = last fl g.

  Definition fmN : Z -> option Z := fun x => if x =? t then Some g else None.
  Definition fmP : Z -> option Z := fun x => if x =? h then Some g else None.
  Definition fm_mt : meta_rec := MT (fun f => match f with FPrev => t | FNext => h | _ => 0 end) RFree.
  Definition fmA : astate := MallocInv_wf3.A' B fmP fmN (a_active B) (fl ++ [g]) (Some (g, fm_mt)).

  Lemma fl_mem : forall x, In x fl -> exists mt, a_meta B x = Some mt /\ mt_role mt = RFree.
  Proof. intros x Hx. apply (proj1 (wf_fl_mem B HW x)). rewrite Hfl. exact Hx. Qed.
  Lemma g_notin : ~ In g fl.
  Proof. intros Hin. destruct (fl_mem g Hin) as (mt & Hm & Hr). rewrite Hg in Hm. injection Hm as <-. rewrite Hrg in Hr. discriminate. Qed.
  Lemma h_in : fl <> [] -> In h fl.
  Proof. intros Hne. rewrite Hh. destruct fl; [contradiction | left; reflexivity]. Qed.
  Lemma t_in : fl <> [] -> In t fl.
  Proof. intros Hne. rewrite Ht. apply last_In_ne. exact Hne. Qed.
  Lemma h_ne_g : fl <> [] -> h <> g.
  Proof. intros Hne E. apply g_notin. rewrite <- E. exact (h_in Hne). Qed.
  Lemma t_ne_g : fl <> [] -> t <> g.
  Proof. intros Hne E. apply g_notin. rewrite <- E. exact (t_in Hne). Qed.
  Lemma h_nil : fl = [] -> h = g. Proof. intros E. rewrite Hh, E. reflexivity. Qed.
  Lemma t_nil : fl = [] -> t = g. Proof. intros E. rewrite Ht, E. reflexivity. Qed.
  Lemma fl_nodup : List.NoDup fl.
  Proof. apply (proj1 (NoDup_ListNoDup _)). rewrite <- Hfl. exact (wf_fl_nodup B HW). Qed.
  Lemma h_nth : fl <> [] -> nth_error fl 0 = Some h.
  Proof. intros Hne. rewrite Hh. destruct fl; [contradiction | reflexivity]. Qed.
  Lemma t_nth : fl <> [] -> nth_error fl (length fl - 1) = Some t.
  Proof. intros Hne. rewrite Ht, (last_nth fl g Hne). apply nth_error_nth'. destruct fl; [contradiction | cbn; lia]. Qed.
  Lemma nth_is_h : forall k x, nth_error fl k = Some x -> (x = h <-> k = 0%nat).
  Proof.
    intros k x Hk. assert (Hne : fl <> []) by (intros E; rewrite E in Hk; destruct k; discriminate Hk). split.
    - intros ->. apply (proj1 (List.NoDup_nth_error fl) fl_nodup k 0%nat); [apply (proj1 (nth_error_Some fl k)); rewrite Hk; discriminate|].
      rewrite Hk, (h_nth Hne). reflexivity.
    - intros ->. rewrite (h_nth Hne) in Hk. injection Hk as ->. reflexivity.
  Qed.
  Lemma nth_is_t : forall k x, nth_error fl k = Some x -> (x = t <-> S k = length fl).
  Proof.
    intros k x Hk. assert (Hne : fl <> []) by (intros E; rewrite E in Hk; destruct k; discriminate Hk).
    assert (Hkl : (k < length fl)%nat) by (apply (proj1 (nth_error_Some fl k)); rewrite Hk; discriminate). split.
    - intros ->. enough (k = length fl - 1)%nat by lia. apply (proj1 (List.NoDup_nth_error fl) fl_nodup k (length fl - 1)%nat Hkl). rewrite Hk, (t_nth Hne). reflexivity.
    - intros E. replace k with (length fl - 1)%nat in Hk by lia. rewrite (t_nth Hne) in Hk. injection Hk as ->. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ht_meta : (exists mth, a_meta B h = Some mth /\ (mt_role mth = RFree \/ h = g)) /\
                  (exists mtt, a_meta B t = Some mtt /\ (mt_role mtt = RFree \/ t = g)).
  Proof.
    destruct (list_eq_dec Z.eq_dec fl []) as [E | NE].
    - rewrite (h_nil E), (t_nil E). split; exists mg; auto.
    - destruct (fl_mem h (h_in NE)) as (mth & H1 & H2). destruct (fl_mem t (t_in NE)) as (mtt & T1 & T2). split; [exists mth | exists mtt]; auto.
  Qed.

  Let RL := MallocInv_wf3.relink fmP fmN.

  Lemma victim_ok : exists mt0, a_meta B g = Some mt0 /\ (mt_role mt0 = RDead \/ mt_role mt0 = RFree) /\ (mt_role fm_mt = RDead \/ mt_role fm_mt = RFree).
  Proof. exists mg. split; [exact Hg|]. split; [left; exact Hrg | right; reflexivity]. Qed.

  Lemma fmA_meta_g : a_meta fmA g = Some fm_mt.
  Proof. unfold fmA, MallocInv_wf3.A', MallocInv_wf3.g'. cbn [a_meta]. destruct (Z.eq_dec g g); [reflexivity | contradiction]. Qed.
  Lemma fmA_meta_other : forall x, x <> g -> a_meta fmA x = option_map (RL x) (a_meta B x).
  Proof. intros x Hx. unfold fmA, MallocInv_wf3.A', MallocInv_wf3.g'. cbn [a_meta]. destruct (Z.eq_dec x g); [contradiction | reflexivity]. Qed.
  Lemma G'_eq : forall x, MallocInv_wf3.g' B fmP fmN (Some (g, fm_mt)) x = a_meta fmA x. Proof. reflexivity. Qed.
  Ltac g2a x := change (MallocInv_wf3.g' B fmP fmN (Some (g, fm_mt)) x) with (a_meta fmA x) in *.

  Lemma rl_next : forall x mt, mt_next (RL x mt) = if x =? t then g else mt_next mt.
  Proof. intros x mt. unfold RL, mt_next, MallocInv_wf3.relink. rewrite mt_f_MT. unfold fmN. destruct (x =? t); reflexivity. Qed.
  Lemma rl_prev : forall x mt, mt_prev (RL x mt) = if x =? h then g else mt_prev mt.
  Proof. intros x mt. unfold RL, mt_prev, MallocInv_wf3.relink. rewrite mt_f_MT. unfold fmP. destruct (x =? h); reflexivity. Qed.
  Lemma rl_f_other : forall x mt f, f <> FPrev -> f <> FNext -> mt_f (RL x mt) f = mt_f mt f.
  Proof. intros x mt f H1 H2. unfold RL, MallocInv_wf3.relink. rewrite mt_f_MT. destruct f; try reflexivity; contradiction. Qed.
  Lemma rl_other : forall x mt, x <> h -> x <> t -> RL x mt = mt.
  Proof.
    intros x mt H1 H2. unfold RL, MallocInv_wf3.relink, fmP, fmN. apply meta_ext; [reflexivity|]. intros f. rewrite mt_f_MT.
    rewrite (proj2 (Z.eqb_neq x h) H1), (proj2 (Z.eqb_neq x t) H2). destruct f; reflexivity.
  Qed.
  Lemma rl_nonfl : forall x mt, x <> g -> ~ In x fl -> RL x mt = mt.
  Proof.
    intros x mt Hxg Hxl. destruct (list_eq_dec Z.eq_dec fl []) as [E | NE].
    - apply rl_other; [rewrite (h_nil E) | rewrite (t_nil E)]; exact Hxg.
    - apply rl_other; intros ->; apply Hxl; [apply h_in | apply t_in]; exact NE.
  Qed.
  Lemma rl_nonfree : forall x mt, a_meta B x = Some mt -> mt_role mt <> RFree -> x <> g -> RL x mt = mt.
  Proof.
    intros x mt Hx Hr Hxg. apply (rl_nonfl x mt Hxg). intros Hin. destruct (fl_mem x Hin) as (mt' & Hx' & Hr'). rewrite Hx in Hx'. injection Hx' as <-. exact (Hr Hr').
  Qed.
  Lemma fm_mt_f : forall f, mt_f fm_mt f = match f with FPrev => t | FNext => h | _ => 0 end.
  Proof. intros f. unfold fm_mt. rewrite mt_f_MT. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fmA_meta_inv : forall x mt', a_meta fmA x = Some mt' ->
    (x = g /\ mt' = fm_mt) \/ (x <> g /\ exists mt, a_meta B x = Some mt /\ mt' = RL x mt).
  Proof.
    intros x mt' Hx. destruct (Z.eq_dec x g) as [-> | Hne].
    - left. rewrite fmA_meta_g in Hx. injection Hx as <-. auto.
    - right. rewrite (fmA_meta_other x Hne) in Hx. destruct (a_meta B x) as [mt|]; [| discriminate Hx]. cbn in Hx. injection Hx as <-. split; [exact Hne | exists mt; auto].
  Qed.
  (* [comment removed for export] *)
  Lemma fmA_group : forall x mt aib sl, a_meta B x = Some mt -> mt_role mt = RGroup aib sl -> a_meta fmA x = Some mt.
  Proof.
    intros x mt aib sl Hx Hr. assert (Hxg : x <> g) by (intros ->; rewrite Hg in Hx; injection Hx as <-; rewrite Hrg in Hr; discriminate).
    rewrite (fmA_meta_other x Hxg), Hx. cbn. rewrite (rl_nonfree x mt Hx) by (try exact Hxg; rewrite Hr; discriminate). reflexivity.
  Qed.
  Lemma fmA_group_inv : forall x mt' aib sl, a_meta fmA x = Some mt' -> mt_role mt' = RGroup aib sl -> a_meta B x = Some mt'.
  Proof.
    intros x mt' aib sl Hx Hr. destruct (fmA_meta_inv x mt' Hx) as [(-> & ->) | (Hne & mt & Hx0 & ->)]; [cbn in Hr; discriminate|].
    change (mt_role (RL x mt)) with (mt_role mt) in Hr. rewrite (rl_nonfree x mt Hx0) by (try exact Hne; rewrite Hr; discriminate). exact Hx0.
  Qed.

  Lemma fmA_ctx_valid : forall k, cvalid k -> a_ctx fmA k = if cslot_eq_dec k KFmh then h else a_ctx B k.
  Proof.
    intros k Hk. unfold fmA, MallocInv_wf3.A', MallocInv_wf3.c'. cbn [a_ctx]. destruct k; try reflexivity.
    - cbn. rewrite Hh. apply hd_app_g.
    - destruct (cslot_eq_dec (KActive i) KFmh) as [E | _]; [discriminate E|]. symmetry. apply (wf_act_head B HW). exact Hk.
  Qed.
  Lemma fmA_ctx_other : forall k, (k <> KFmh) -> (forall c, k <> KActive c) -> a_ctx fmA k = a_ctx B k.
  Proof.
    intros k H1 H2. unfold fmA, MallocInv_wf3.A', MallocInv_wf3.c'. cbn [a_ctx]. destruct k; try reflexivity; [contradiction | exfalso; exact (H2 i eq_refl)].
  Qed.
  Lemma fmA_active : a_active fmA = a_active B. Proof. reflexivity. Qed.
  Lemma fmA_freelist : a_freelist fmA = fl ++ [g]. Proof. reflexivity. Qed.
  Lemma fmA_live : a_live fmA = a_live B. Proof. reflexivity. Qed.
  Lemma fmA_areas : a_areas fmA = a_areas B. Proof. reflexivity. Qed.
  Lemma fmA_pages : a_pages fmA = a_pages B. Proof. reflexivity. Qed.
  Lemma fmA_mblocks : a_mblocks fmA = a_mblocks B. Proof. reflexivity. Qed.
  Lemma fmA_xmaps : a_xmaps fmA = a_xmaps B. Proof. reflexivity. Qed.

  Theorem WF_fmA : WF fmA.
  Proof.
    pose proof ht_meta as [(mth & Hmh & Rh) (mtt & Hmt & Rt)].
    assert (MEM : forall x, In x (fl ++ [g]) <-> In x fl \/ x = g).
    { intros x. rewrite in_app_iff. cbn. split; [intros [H|[H|[]]]; [left; exact H | right; symmetry; exact H] | intros [H|H]; [left; exact H | right; left; symmetry; exact H]]. }
    assert (GRP : forall x mt' aib sl, MallocInv_wf3.g' B fmP fmN (Some (g, fm_mt)) x = Some mt' -> mt_role mt' = RGroup aib sl -> a_meta B x = Some mt' /\ x <> g /\ ~ In x fl).
    { intros x mt' aib sl Hx Hr. g2a x. pose proof (fmA_group_inv x mt' aib sl Hx Hr) as Hx0. split; [exact Hx0|]. split.
      - intros ->. rewrite Hg in Hx0. injection Hx0 as <-. rewrite Hrg in Hr. discriminate.
      - intros Hin. destruct (fl_mem x Hin) as (mt0 & H0 & R0). rewrite Hx0 in H0. injection H0 as <-. rewrite Hr in R0. discriminate. }
    apply WF_relists; try exact HW.
    - exact victim_ok.
    - apply (proj2 (NoDup_ListNoDup _)). apply List.NoDup_app; [exact fl_nodup | constructor; [intros [] | constructor] |].
      intros x Hx [<- | []]. exact (g_notin Hx).
    - intros x. rewrite MEM. change (MallocInv_wf3.g' B fmP fmN (Some (g, fm_mt)) x) with (a_meta fmA x). split.
      + intros [Hin | ->]; [| exists fm_mt; rewrite fmA_meta_g; auto].
        destruct (fl_mem x Hin) as (mt & Hx & Hr). assert (Hxg : x <> g) by (intros ->; exact (g_notin Hin)).
        exists (RL x mt). rewrite (fmA_meta_other x Hxg), Hx. auto.
      + intros (mt' & Hx & Hr). destruct (fmA_meta_inv x mt' Hx) as [(-> & _) | (Hne & mt & Hx0 & ->)]; [right; reflexivity | left].
        rewrite <- Hfl. apply (proj2 (wf_fl_mem B HW x)). exists mt. auto.
    - destruct (list_eq_dec Z.eq_dec fl []) as [El | El].
      + rewrite El. cbn [app]. apply (dll_single' fmA g fm_mt); [apply fmA_meta_g | |].
        * unfold mt_next. rewrite fm_mt_f. exact (h_nil El).
        * unfold mt_prev. rewrite fm_mt_f. exact (t_nil El).
      + apply (dll_snoc B fmA fl g El).
        * rewrite <- Hfl. exact (wf_fl_dll B HW).
        * intros k x mt Hk Hx. pose proof (nth_error_In _ _ Hk) as Hin. assert (Hxg : x <> g) by (intros ->; exact (g_notin Hin)).
          exists (RL x mt). rewrite (fmA_meta_other x Hxg), Hx. split; [reflexivity|]. rewrite rl_next, rl_prev. split.
          -- destruct (Z.eqb_spec x t) as [E | NE]; [rewrite (proj2 (Nat.eqb_eq _ _) (proj1 (nth_is_t k x Hk) E)); reflexivity|].
             destruct (Nat.eqb_spec (S k) (length fl)) as [E2 | NE2]; [exfalso; exact (NE (proj2 (nth_is_t k x Hk) E2)) | reflexivity].
          -- destruct (Z.eqb_spec x h) as [E | NE]; [rewrite (proj2 (Nat.eqb_eq _ _) (proj1 (nth_is_h k x Hk) E)); reflexivity|].
             destruct (Nat.eqb_spec k 0) as [E2 | NE2]; [exfalso; exact (NE (proj2 (nth_is_h k x Hk) E2)) | reflexivity].
        * exists fm_mt. rewrite fmA_meta_g. unfold mt_next, mt_prev. rewrite !fm_mt_f.
          rewrite (hd_default_ne fl 0 g El), (last_default_ne fl 0 g El), Hh, Ht. auto.
    - exact (wf_act_nodup B HW).
    - intros c Hc. apply (dll_transfer B fmA (a_active B c) (wf_act_dll B HW c Hc)).
      intros y mty Hin Hy. destruct (wf_act_mem B HW c y Hin) as (mt0 & aib & sl & Hy0 & Hr0 & _). rewrite Hy in Hy0. injection Hy0 as <-.
      exists mty. rewrite (fmA_group y mty aib sl Hy Hr0). auto.
    - intros c x Hin. destruct (wf_act_mem B HW c x Hin) as (mt & aib & sl & Hx & Hr & Hs). exists mt, aib, sl.
      g2a x. rewrite (fmA_group x mt aib sl Hx Hr). auto.
    - intros x mt' aib sl Hx Hr. destruct (GRP x mt' aib sl Hx Hr) as (Hx0 & _). exact (wf_unlinked B HW x mt' aib sl Hx0 Hr).
    - intros c x mt' Hin Hne Hx. destruct (wf_act_mem B HW c x Hin) as (mt & aib & sl & Hx0 & Hr0 & _).
      g2a x. rewrite (fmA_group x mt aib sl Hx0 Hr0) in Hx. injection Hx as <-. exact (wf_act_nonhead B HW c x mt Hin Hne Hx0).
    - intros x mt' aib sl Hx Hr. destruct (GRP x mt' aib sl Hx Hr) as (Hx0 & _). exact (wf_act63 B HW x mt' aib sl Hx0 Hr).
    - intros c x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry.
      destruct (GRP x mtx aibx slx Hx Hrx) as (Hx0 & _). destruct (GRP y mty aiby sly Hy Hry) as (Hy0 & _).
      exact (wf_partial B HW c x mtx aibx slx y mty aiby sly Hinx Hiny Hx0 Hrx Hy0 Hry).
    - intros x mt' Hx Hr. g2a x. destruct (fmA_meta_inv x mt' Hx) as [(-> & ->) | (Hne & mt & Hx0 & ->)]; [cbn in Hr; discriminate|].
      change (mt_role (RL x mt)) with (mt_role mt) in Hr. rewrite (rl_nonfree x mt Hx0) by (try exact Hne; rewrite Hr; discriminate).
      exact (wf_avail_zero B HW x mt Hx0 Hr).
    - intros x mt' Hx Hr. g2a x. destruct (fmA_meta_inv x mt' Hx) as [(-> & ->) | (Hne & mt & Hx0 & ->)].
      + unfold mt_mem, mt_avail, mt_freed, mt_w32. rewrite !fm_mt_f. auto.
      + change (mt_role (RL x mt)) with (mt_role mt) in Hr. unfold mt_mem, mt_avail, mt_freed, mt_w32. rewrite !rl_f_other by discriminate.
        exact (wf_free_zero B HW x mt Hx0 Hr).
  Qed.

  Lemma dom_fmA : forall x, dom fmA x <-> dom B x.
  Proof. intros x. apply (MallocInv_wf3.dom_relists B fmP fmN (a_active B) (fl ++ [g]) (Some (g, fm_mt)) victim_ok). Qed.
  Lemma VMok_fmA : forall hh, VMok B hh -> VMok fmA hh.
  Proof. intros hh HV. apply (MallocInv_wf3.VMok_relists B fmP fmN (a_active B) (fl ++ [g]) (Some (g, fm_mt)) victim_ok). exact HV. Qed.

  Lemma meta_usage_fmA : forall c x, meta_usage fmA c x = meta_usage B c x.
  Proof.
    intros c x. unfold meta_usage. destruct (Z.eq_dec x g) as [-> | Hne].
    - rewrite fmA_meta_g, Hg, Hrg. reflexivity.
    - rewrite (fmA_meta_other x Hne). destruct (a_meta B x) as [mt|]; [cbn [option_map] | reflexivity].
      change (mt_role (RL x mt)) with (mt_role mt). unfold RL. rewrite MallocInv_wf3.rl_sc, MallocInv_wf3.rl_cnt. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma has_fmA : forall f, has fmA f ->
    has B f \/ f = FCT (caddr KFmh) 8 h \/
    (exists fld, f = FCT (g + moff fld) (mlen fld) (mt_f fm_mt fld)) \/
    (fl <> [] /\ (f = FCT h 8 g \/ f = FCT (t + 8) 8 g)).
  Proof.
    intros f Hf. pose proof ht_meta as [(mth & Hmh & Rh) (mtt & Hmt & Rt)].
    destruct (MallocInv_wf3.relists_has_inv B fmP fmN (a_active B) (fl ++ [g]) (Some (g, fm_mt)) victim_ok f Hf) as [(k & Hk & ->) | Hrest].
    - change (MallocInv_wf3.c' B (a_active B) (fl ++ [g]) k) with (a_ctx fmA k). rewrite (fmA_ctx_valid k Hk).
      destruct (cslot_eq_dec k KFmh) as [-> | Hne]; [right; left; reflexivity | left; left; exists k; auto].
    - destruct Hrest as [Har | [(x & mt' & fld & Hx & ->) | Hgr]].
      + left. right; left. exact Har.
      + g2a x. destruct (fmA_meta_inv x mt' Hx) as [(-> & ->) | (Hne & mt & Hx0 & ->)].
        * right; right; left. exists fld. reflexivity.
        * destruct (Z.eq_dec x h) as [-> | H1]; [| destruct (Z.eq_dec x t) as [-> | H2]].
          -- destruct fld.
             1:{ destruct (list_eq_dec Z.eq_dec fl []) as [El | El]; [exfalso; exact (Hne (h_nil El))|].
                 right; right; right. split; [exact El|]. left. cbn [moff mlen]. rewrite Z.add_0_r. f_equal.
                 change (mt_f (RL h mt) FPrev) with (mt_prev (RL h mt)). rewrite rl_prev, Z.eqb_refl. reflexivity. }
             1:{ change (mt_f (RL h mt) FNext) with (mt_next (RL h mt)). rewrite rl_next.
                 destruct (Z.eqb_spec h t) as [E | NE].
                 - destruct (list_eq_dec Z.eq_dec fl []) as [El | El]; [exfalso; exact (Hne (h_nil El))|].
                   right; right; right. split; [exact El|]. right. rewrite E. reflexivity.
                 - left. right; right; left. exists h, mt, FNext. auto. }
             all: left; right; right; left; exists h, mt; eexists; split; [exact Hx0 | rewrite rl_f_other by discriminate; reflexivity].
          -- destruct fld.
             2:{ destruct (list_eq_dec Z.eq_dec fl []) as [El | El]; [exfalso; exact (Hne (t_nil El))|].
                 right; right; right. split; [exact El|]. right. cbn [moff mlen]. f_equal.
                 change (mt_f (RL t mt) FNext) with (mt_next (RL t mt)). rewrite rl_next, Z.eqb_refl. reflexivity. }
             1:{ change (mt_f (RL t mt) FPrev) with (mt_prev (RL t mt)). rewrite rl_prev. rewrite (proj2 (Z.eqb_neq t h) ltac:(intros E; exact (H1 E))).
                 left. right; right; left. exists t, mt, FPrev. auto. }
             all: left; right; right; left; exists t, mt; eexists; split; [exact Hx0 | rewrite rl_f_other by discriminate; reflexivity].
          -- left. right; right; left. exists x, mt, fld. rewrite (rl_other x mt H1 H2). auto.
      + left. right; right; right. exact Hgr.
  Qed.
End FreeMeta.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeMetaCPS.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Variables (g : Z) (mg : meta_rec).
  Hypothesis HII : II sp0 argv envp cb (g :: D) B s1.
  Hypothesis HgD : ~ In g D.
  Hypothesis Hg : a_meta B g = Some mg.
  Hypothesis Hrg : mt_role mg = RDead.

  Let fl := a_freelist B.
  Let h := hd g fl.
  Let t := last fl g.
  Let hd0 := hd 0 fl.
  Let Bf := fmA B g fl h t.
  Let zws : list fct := [FCT (g + 32) 8 0; FCT (g + 24) 8 0; FCT (g + 16) 8 0; FCT g 8 0; FCT (g + 8) 8 0].
  Let fws : list fct :=
    (if list_eq_dec Z.eq_dec fl []
     then [FCT (caddr KFmh) 8 g; FCT (g + 8) 8 g; FCT g 8 g]
     else [FCT hd0 8 g; FCT (t + 8) 8 g; FCT g 8 t; FCT (g + 8) 8 hd0]) ++ zws.

  Lemma FW : WF B. Proof. exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma HWf : WF Bf. Proof. exact (WF_fmA B FW g mg fl h t Hg Hrg eq_refl eq_refl eq_refl). Qed.
  Lemma Bf_g : a_meta Bf g = Some (fm_mt h t). Proof. apply fmA_meta_g. Qed.

  Lemma fl_ne_facts : fl <> [] -> h = hd0 /\ In hd0 fl /\ In t fl /\ hd0 <> g /\ t <> g /\ hd0 <> 0 /\
    exists mth mtt, a_meta B hd0 = Some mth /\ a_meta B t = Some mtt /\ mt_prev mth = t.
  Proof.
    intros Hne. pose proof FW as HW. assert (Eh : h = hd0) by (unfold h, hd0; apply hd_default_ne; exact Hne).
    pose proof (h_in B g fl h t eq_refl eq_refl eq_refl Hne) as Hin_h. rewrite Eh in Hin_h. pose proof (t_in g fl t eq_refl Hne) as Hin_t.
    destruct (fl_mem B HW fl eq_refl hd0 Hin_h) as (mth & Hmh & Rh). destruct (fl_mem B HW fl eq_refl t Hin_t) as (mtt & Hmt & Rt).
    pose proof (g_notin B HW g mg fl Hg Hrg eq_refl) as Hgn.
    pose proof (meta_facts B hd0 mth HW Hmh) as (L1 & _).
    split; [exact Eh|]. split; [exact Hin_h|]. split; [exact Hin_t|]. split; [intros E; apply Hgn; rewrite <- E; exact Hin_h|].
    split; [intros E; apply Hgn; rewrite <- E; exact Hin_t|]. split; [llia|].
    exists mth, mtt. split; [exact Hmh|]. split; [exact Hmt|].
    pose proof (wf_fl_dll B HW) as Hd. fold fl in Hd.
    assert (H0 : nth_error fl 0 = Some hd0) by (unfold hd0; destruct fl; [contradiction | reflexivity]).
    destruct (Hd 0%nat hd0 H0) as (mt' & Hm' & _ & Hp). rewrite Hmh in Hm'. injection Hm' as <-.
    rewrite Hp. replace ((0 + length fl - 1) mod length fl)%nat with (length fl - 1)%nat.
    2:{ rewrite Nat.add_0_l. symmetry. apply Nat.mod_small. destruct fl; [contradiction | cbn; lia]. }
    rewrite <- (last_nth fl 0 Hne). unfold t. apply last_default_ne. exact Hne.
  Qed.

  Lemma h_nil' : fl = [] -> h = g /\ t = g.
  Proof. intros E. unfold h, t. rewrite E. auto. Qed.

  Lemma AUD_Bf : AvOK Bf /\ UsOK Bf /\ deads Bf D.
  Proof.
    pose proof FW as HW.
    assert (BK : forall x mt', a_meta Bf x = Some mt' -> x <> g -> exists mtx, a_meta B x = Some mtx /\ mt_role mt' = mt_role mtx).
    { intros x mt' Hx Hne. destruct (fmA_meta_inv B g fl h t x mt' Hx) as [(E & _) | (_ & mtx & Hx0 & ->)]; [contradiction|]. exists mtx. auto. }
    split; [| split].
    - apply (AvOK_transfer B Bf (ii_av HII)); [reflexivity | apply (fmA_ctx_other B g fl h t KAmc); [discriminate | intros c; discriminate] |].
      intros x mt' Hx Hrl. destruct (Z.eq_dec x g) as [-> | Hne].
      + unfold Bf in Hx. rewrite (fmA_meta_g B g fl h t) in Hx. injection Hx as <-. cbn in Hrl. discriminate.
      + destruct (BK x mt' Hx Hne) as (mtx & H1 & R1). exists mtx. rewrite <- R1. auto.
    - apply (UsOK_transfer B Bf (ii_us HII)); [reflexivity | | intros c x; apply (meta_usage_fmA B g mg fl h t Hg Hrg)].
      intros c Hc. apply (fmA_ctx_other B g fl h t (KUsage c)); [discriminate | intros c'; discriminate].
    - intros x. split.
      + intros (mt' & Hx & Hrl). destruct (Z.eq_dec x g) as [-> | Hne].
        * unfold Bf in Hx. rewrite (fmA_meta_g B g fl h t) in Hx. injection Hx as <-. cbn in Hrl. discriminate.
        * destruct (BK x mt' Hx Hne) as (mtx & H1 & R1).
          destruct (proj1 (ii_dd HII x) ltac:(exists mtx; rewrite <- R1; auto)) as [E | Hin]; [exfalso; exact (Hne (eq_sym E)) | exact Hin].
      + intros Hin. assert (Hne : x <> g) by (intros ->; exact (HgD Hin)).
        destruct (proj2 (ii_dd HII x) (or_intror Hin)) as (mtx & Hx & Hrl).
        exists (MallocInv_wf3.relink (fmP g h) (fmN g t) x mtx). unfold Bf. rewrite (fmA_meta_other B g fl h t x Hne), Hx. auto.
  Qed.

  Lemma fws_zws : forall w, In w fws ->
    In w zws \/ (w = FCT (caddr KFmh) 8 g /\ fl = []) \/ (exists d v, (d = 0 \/ d = 8) /\ w = FCT (g + d) 8 v) \/
    (fl <> [] /\ (w = FCT hd0 8 g \/ w = FCT (t + 8) 8 g)).
  Proof.
    intros w Hw. unfold fws in Hw. apply in_app_iff in Hw. destruct Hw as [Hw | Hw]; [| left; exact Hw].
    destruct (list_eq_dec Z.eq_dec fl []) as [El | El].
    - destruct Hw as [<- | [<- | [<- | []]]]; [right; left; auto | right; right; left | right; right; left].
      + exists 8, g. auto.
      + exists 0, g. rewrite Z.add_0_r. auto.
    - destruct Hw as [<- | [<- | [<- | [<- | []]]]]; [right; right; right; auto | right; right; right; auto | right; right; left | right; right; left].
      + exists 0, t. rewrite Z.add_0_r. auto.
      + exists 8, hd0. auto.
  Qed.

  Lemma WOf : writes_ok B fws.
  Proof.
    pose proof FW as HW. intros w x Hw Hx.
    destruct (fws_zws w Hw) as [Hz | [(-> & _) | [(d & v & Hd & ->) | (El & Hht)]]].
    - assert (Hg40 : g <= x < g + 40) by (destruct Hz as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [f_a f_n] in Hx; lia).
      destruct (meta_dom_nolive B g mg x HW Hg Hg40) as [H1 H2]. split; [left; exact H1 | exact H2].
    - apply (writes_ok_ctx B [] KFmh g HW (writes_ok_nil B) I _ x (or_introl eq_refl) Hx).
    - cbn [f_a f_n] in Hx. destruct (meta_dom_nolive B g mg x HW Hg ltac:(lia)) as [H1 H2]. split; [left; exact H1 | exact H2].
    - destruct (fl_ne_facts El) as (_ & _ & _ & _ & _ & _ & mth & mtt & Hmh & Hmt & _).
      destruct Hht as [-> | ->]; cbn [f_a f_n] in Hx.
      + destruct (meta_dom_nolive B hd0 mth x HW Hmh ltac:(lia)) as [H1 H2]. split; [left; exact H1 | exact H2].
      + destruct (meta_dom_nolive B t mtt x HW Hmt ltac:(lia)) as [H1 H2]. split; [left; exact H1 | exact H2].
  Qed.

  Lemma has_Bf_written : forall f, has Bf f -> has B f \/ (forall x, f_a f <= x < f_a f + f_n f -> wlook fws x <> None).
  Proof.
    intros f Hf. pose proof FW as HW.
    assert (CV : forall a n v x, In (FCT a n v) fws -> a <= x < a + n -> wlook fws x <> None).
    { intros a n v x Hin Hx. apply (wlook_cov_some fws (FCT a n v) x Hin). cbn [f_a f_n]. exact Hx. }
    assert (INZ : forall w, In w zws -> In w fws) by (intros w Hw; unfold fws; apply in_app_iff; right; exact Hw).
    destruct (has_fmA B FW g mg fl h t Hg Hrg eq_refl eq_refl eq_refl f Hf) as [H | [-> | [(fld & ->) | (El & Hc)]]]; [left; exact H | | right | right].
    - destruct (list_eq_dec Z.eq_dec fl []) as [El | El].
      + right. cbn [f_a f_n]. intros x Hx. apply (CV (caddr KFmh) 8 g); [| exact Hx]. unfold fws. cbn. auto.
      + left. destruct (fl_ne_facts El) as (Eh & _). rewrite Eh. unfold hd0, fl. rewrite <- (wf_fl_head B HW). left. exists KFmh. split; [exact I | reflexivity].
    - intros x Hx. destruct fld; cbn [moff mlen f_a f_n] in Hx.
      + apply (CV g 8 0); [apply INZ; cbn; auto 10 | lia].
      + apply (CV (g + 8) 8 0); [apply INZ; cbn; auto 10 | lia].
      + apply (CV (g + 16) 8 0); [apply INZ; cbn; auto 10 | lia].
      + apply (CV (g + 24) 8 0); [apply INZ; cbn; auto 10 | lia].
      + apply (CV (g + 24) 8 0); [apply INZ; cbn; auto 10 | lia].
      + apply (CV (g + 32) 8 0); [apply INZ; cbn; auto 10 | lia].
    - assert (Q : exists pre, fws = pre ++ zws /\ pre = [FCT hd0 8 g; FCT (t + 8) 8 g; FCT g 8 t; FCT (g + 8) 8 hd0]).
      { unfold fws. destruct (list_eq_dec Z.eq_dec fl []); [contradiction|]. eexists. split; reflexivity. }
      destruct Q as (pre & Efws & Epre). destruct (fl_ne_facts El) as (Eh & _).
      destruct Hc as [-> | ->]; cbn [f_a f_n]; intros x Hx.
      + apply (CV hd0 8 g); [| rewrite <- Eh; exact Hx]. rewrite Efws, Epre. cbn. auto.
      + apply (CV (t + 8) 8 g); [| exact Hx]. rewrite Efws, Epre. cbn. auto 10.
  Qed.

  Lemma fws_lookup : forall x b, wlook fws x = Some b ->
    (exists y mty fld, a_meta Bf y = Some mty /\ y + moff fld <= x < y + moff fld + mlen fld /\ b = byte_of (mt_f mty fld) (x - (y + moff fld))) \/
    (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx Bf k) (x - caddr k)) \/
    (forall f, has Bf f -> ~ (f_a f <= x < f_a f + f_n f)).
  Proof.
    intros x b Hw. pose proof FW as HW. pose proof (meta_facts B g mg HW Hg) as (M1 & M2 & M3 & M4 & _).
    pose proof (ctx_slot_range KFmh I) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    pose proof Bf_g as Hg2.
    assert (FM : forall fld, mt_f (fm_mt h t) fld = match fld with FPrev => t | FNext => h | _ => 0 end) by (intros fld; apply fm_mt_f).
    assert (CTX : a_ctx Bf KFmh = h).
    { unfold Bf. rewrite (fmA_ctx_valid B HW g fl h t eq_refl KFmh I). destruct (cslot_eq_dec KFmh KFmh); [reflexivity | contradiction]. }
    unfold fws, zws in Hw.
    destruct (list_eq_dec Z.eq_dec fl []) as [El | El]; cbn [app] in Hw.
    - destruct (h_nil' El) as [Eh Et].
      destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw).
      destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]; cbn [f_a f_n] in Hxw;
        repeat (rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; llia)); rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; llia);
        injection Hw as <-; cbn [f_v f_a].
      + right; left. exists KFmh. cbn [clen]. split; [exact I|]. split; [lia|]. rewrite CTX, Eh. reflexivity.
      + left. exists g, (fm_mt h t), FNext. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Eh. reflexivity.
      + left. exists g, (fm_mt h t), FPrev. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Et, Z.add_0_r. reflexivity.
      + left. exists g, (fm_mt h t), FW32. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM. reflexivity.
      + left. destruct (Z.lt_ge_cases x (g + 28)) as [H28 | H28].
        * exists g, (fm_mt h t), FAvail. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, !byte_of_zero. reflexivity.
        * exists g, (fm_mt h t), FFreed. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, !byte_of_zero. reflexivity.
      + left. exists g, (fm_mt h t), FMem. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM. reflexivity.
      + left. exists g, (fm_mt h t), FPrev. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Et, Z.add_0_r. reflexivity.
      + left. exists g, (fm_mt h t), FNext. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Eh. reflexivity.
    - destruct (fl_ne_facts El) as (Eh & Hin_h & Hin_t & Hhg & Htg & Hh0 & mth & mtt & Hmh & Hmt & Hph).
      pose proof (meta_facts B hd0 mth HW Hmh) as (P1 & P2 & P3 & P4 & _). pose proof (meta_facts B t mtt HW Hmt) as (T1 & T2 & T3 & T4 & _).
      pose proof (metas_apart B hd0 mth g mg HW Hmh Hg Hhg) as Dhg. pose proof (metas_apart B t mtt g mg HW Hmt Hg Htg) as Dtg.
      assert (Dht : hd0 = t \/ hd0 + 40 <= t \/ t + 40 <= hd0).
      { destruct (Z.eq_dec hd0 t) as [E | NE]; [left; exact E | right; exact (metas_apart B hd0 mth t mtt HW Hmh Hmt NE)]. }
      assert (Hh2 : a_meta Bf hd0 = Some (MallocInv_wf3.relink (fmP g h) (fmN g t) hd0 mth)).
      { unfold Bf. rewrite (fmA_meta_other B g fl h t hd0 Hhg), Hmh. reflexivity. }
      assert (Ht2 : a_meta Bf t = Some (MallocInv_wf3.relink (fmP g h) (fmN g t) t mtt)).
      { unfold Bf. rewrite (fmA_meta_other B g fl h t t Htg), Hmt. reflexivity. }
      destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw).
      destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]; cbn [f_a f_n] in Hxw;
        repeat (rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; llia)); rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; llia);
        injection Hw as <-; cbn [f_v f_a]; left.
      + exists hd0, (MallocInv_wf3.relink (fmP g h) (fmN g t) hd0 mth), FPrev. split; [exact Hh2|]. cbn [moff mlen]. split; [lia|].
        change (mt_f (MallocInv_wf3.relink (fmP g h) (fmN g t) hd0 mth) FPrev) with (mt_prev (MallocInv_wf3.relink (fmP g h) (fmN g t) hd0 mth)).
        rewrite rl_prev, Eh, Z.eqb_refl, Z.add_0_r. reflexivity.
      + exists t, (MallocInv_wf3.relink (fmP g h) (fmN g t) t mtt), FNext. split; [exact Ht2|]. cbn [moff mlen]. split; [lia|].
        change (mt_f (MallocInv_wf3.relink (fmP g h) (fmN g t) t mtt) FNext) with (mt_next (MallocInv_wf3.relink (fmP g h) (fmN g t) t mtt)).
        rewrite rl_next, Z.eqb_refl. reflexivity.
      + exists g, (fm_mt h t), FPrev. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Z.add_0_r. reflexivity.
      + exists g, (fm_mt h t), FNext. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Eh. reflexivity.
      + exists g, (fm_mt h t), FW32. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM. reflexivity.
      + destruct (Z.lt_ge_cases x (g + 28)) as [H28 | H28].
        * exists g, (fm_mt h t), FAvail. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, !byte_of_zero. reflexivity.
        * exists g, (fm_mt h t), FFreed. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, !byte_of_zero. reflexivity.
      + exists g, (fm_mt h t), FMem. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM. reflexivity.
      + exists g, (fm_mt h t), FPrev. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Z.add_0_r. reflexivity.
      + exists g, (fm_mt h t), FNext. split; [exact Hg2|]. cbn [moff mlen]. split; [lia|]. rewrite FM, Eh. reflexivity.
  Qed.

  Lemma commit_f : forall m', RepW B (ms_mem s1) fws m' ->
    II sp0 argv envp cb D Bf (upd s1 m' (ms_vm s1)) /\ ntframe B s1 (upd s1 m' (ms_vm s1)).
  Proof.
    intros m' RW. pose proof FW as HW. pose proof WOf as WO. pose proof HWf as HW'.
    split; [| exact (ntframe_commit B s1 fws m' HW RW WO)].
    pose proof AUD_Bf as (Hav & Hus & Hdd).
    apply II_intro; [| cbn [ms_vm upd]; unfold Bf; apply (VMok_fmA B g mg fl h t Hg Hrg); exact (ii_vm HII) | exact Hav | exact Hus | exact Hdd].
    apply (IS_commit sp0 argv envp cb B Bf s1 fws m' (ii_is HII) RW WO HW').
    apply (repw_commit2 B Bf (ms_mem s1) fws m' HW' RW has_Bf_written fws_lookup).
    intros x Hx. apply (proj1 (dom_fmA B g mg fl h t Hg Hrg x)). exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma fmrel :
    a_live Bf = a_live B /\ a_areas Bf = a_areas B /\ a_pages Bf = a_pages B /\ a_mblocks Bf = a_mblocks B /\ a_xmaps Bf = a_xmaps B /\
    a_active Bf = a_active B /\ (forall k, k <> KFmh -> (forall c, k <> KActive c) -> a_ctx Bf k = a_ctx B k) /\
    (forall x mt aib sl, a_meta B x = Some mt -> mt_role mt = RGroup aib sl -> a_meta Bf x = Some mt) /\
    (forall x mt' aib sl, a_meta Bf x = Some mt' -> mt_role mt' = RGroup aib sl -> a_meta B x = Some mt') /\
    (forall x, dom Bf x <-> dom B x).
  Proof.
    pose proof FW as HW. repeat split; try reflexivity.
    - intros k H1 H2. apply (fmA_ctx_other B g fl h t k H1 H2).
    - exact (fmA_group B HW g mg fl h t Hg Hrg eq_refl eq_refl eq_refl).
    - exact (fmA_group_inv B HW g fl h t eq_refl eq_refl eq_refl).
    - apply (proj1 (dom_fmA B g mg fl h t Hg Hrg x)).
    - apply (proj2 (dom_fmA B g mg fl h t Hg Hrg x)).
  Qed.

  (* [comment removed for export] *)
  Lemma free_meta_rest : forall (hda : word) (K : unit -> M R) P m5,
    hda = Z_to_bv 64 (caddr KFmh) ->
    RepW B (ms_mem s1) zws m5 ->
    (forall s', II sp0 argv envp cb D Bf s' -> ntframe B s1 s' -> tsafe (K tt s') P) ->
    tsafe ((x <- (nx <- m_ld (Z_to_bv 64 (g + 8)) ;; massert (is0 nx) ;;
                  pv <- m_ld (Z_to_bv 64 g) ;; massert (is0 pv) ;;
                  hd <- m_ld hda ;;
                  nt_queue hda (Z_to_bv 64 g) hd) ;; K x) (upd s1 m5 (ms_vm s1))) P.
  Proof.
    intros hda K P m5 -> RW5 HK. pose proof FW as HW. pose proof (is_rep _ _ _ _ _ _ (ii_is HII)) as HR. pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof (meta_facts B g mg HW Hg) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof (ctx_slot_range KFmh I) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    reassoc.
    (* [comment removed for export] *)
    eapply (ts_ld_wrw B _ (ms_mem s1) _ (g + 8) 0); [exact RW5 | exact HWIN | lia | llia | lia | |].
    { intros j Hj. unfold zws. repeat (rewrite wlook_skip by (cbn [f_a f_n f_v]; lia)). rewrite wlook_hit by (cbn [f_a f_n f_v]; lia). cbn [f_v f_a]. rewrite !byte_of_zero. reflexivity. }
    reassoc. apply ts_assert; [reflexivity|]. reassoc.
    replace (Z_to_bv 64 g) with (Z_to_bv 64 (g + 0)) at 1 by (f_equal; lia).
    eapply (ts_ld_wrw B _ (ms_mem s1) _ (g + 0) 0); [exact RW5 | exact HWIN | lia | llia | lia | |].
    { intros j Hj. unfold zws. repeat (rewrite wlook_skip by (cbn [f_a f_n f_v]; lia)). rewrite wlook_hit by (cbn [f_a f_n f_v]; lia). cbn [f_v f_a]. rewrite !byte_of_zero. reflexivity. }
    reassoc. apply ts_assert; [reflexivity|]. reassoc.
    (* [comment removed for export] *)
    eapply (ts_ld_ctxfW B HW _ (ms_mem s1) _ KFmh); [exact RW5 | exact HWIN | exact I | reflexivity | |].
    { unfold zws. repeat apply wfree_range_cons; try apply wfree_range_nil; cbn [f_a f_n]; llia. }
    rewrite (wf_fl_head B HW). change (hd 0 (a_freelist B)) with hd0.
    assert (Hhd64 : 0 <= hd0 < 2^64 /\ (hd0 <> 0 -> fl <> [])).
    { destruct (list_eq_dec Z.eq_dec fl []) as [El | El].
      - unfold hd0. rewrite El. cbn. split; [lia | intros H; exfalso; exact (H eq_refl)].
      - destruct (fl_ne_facts El) as (_ & _ & _ & _ & _ & _ & mth & mtt & Hmh & _). pose proof (meta_u64 B hd0 mth HW Hmh). split; [lia | auto]. }
    destruct Hhd64 as [Hhd64 Hflne].
    eapply (ts_nt_queue B HW _ (ms_mem s1) zws KFmh g hd0 t mg K P); [exact RW5 | exact HWIN | exact I | reflexivity | exact Hg | lia | | |].
    - intros Hne. destruct (fl_ne_facts (Hflne Hne)) as (Eh & Hin_h & Hin_t & Hhg & Htg & Hh0 & mth & mtt & Hmh & Hmt & Hph).
      exists mth, mtt. split; [exact Hmh|]. split; [exact Hph|]. split; [exact Hmt|]. split; [| auto].
      pose proof (metas_apart B hd0 mth g mg HW Hmh Hg Hhg) as Dhg.
      unfold zws. repeat apply wfree_range_cons; try apply wfree_range_nil; cbn [f_a f_n]; lia.
    - intros Hh0 m' RW'. destruct (commit_f m') as [HII' HF'].
      { unfold fws. destruct (list_eq_dec Z.eq_dec fl []) as [El | El]; [exact RW' |].
        exfalso. destruct (fl_ne_facts El) as (_ & _ & _ & _ & _ & Hne0 & _). exact (Hne0 Hh0). }
      apply HK; [exact HII' | exact HF'].
    - intros Hh0 m' RW'. destruct (commit_f m') as [HII' HF'].
      { unfold fws. destruct (list_eq_dec Z.eq_dec fl []) as [El | El]; [exfalso; exact (Hh0 ltac:(unfold hd0; rewrite El; reflexivity)) | exact RW']. }
      apply HK; [exact HII' | exact HF'].
  Qed.

  (* [comment removed for export] *)
  Let zws_ag : list fct := [FCT g 8 0; FCT (g + 16) 8 0; FCT (g + 24) 8 0; FCT (g + 32) 8 0; FCT (g + 8) 8 0].

  Lemma zws_ag_lookup : forall x, wlook zws_ag x = wlook zws x.
  Proof.
    intros x. unfold zws_ag, zws. cbn [wlook]. unfold wcov. cbn [f_a f_n f_v]. rewrite !byte_of_zero.
    repeat match goal with |- context [if ?c then _ else _] => let b := fresh "b" in destruct c eqn:? end; try reflexivity;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H; destruct H end;
      repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end; try lia.
    all: exfalso;
      repeat match goal with H : (_ && _) = false |- _ => apply Bool.andb_false_iff in H; destruct H as [H|H]; [apply Z.leb_gt in H | apply Z.ltb_ge in H] end; lia.
  Qed.

  Lemma RepW_zws_ag : forall m, RepW B (ms_mem s1) zws_ag m -> RepW B (ms_mem s1) zws m.
  Proof.
    intros m [F1 F2 F3 F4 F5 F6 F7 F8]. constructor.
    - intros x b Hx. apply F1. rewrite zws_ag_lookup. exact Hx.
    - intros x b Hx. apply F2. rewrite zws_ag_lookup. exact Hx.
    - exact F3.
    - intros w Hw. apply F4. unfold zws, zws_ag in *. cbn [In] in Hw |- *. tauto.
    - exact F5.
    - intros a Ha. apply F6. unfold wfree in *. apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) Ha).
      unfold zws, zws_ag in *. cbn [In] in Hw |- *. tauto.
    - exact F7.
    - intros w Hw. apply F8. unfold zws, zws_ag in *. cbn [In] in Hw |- *. tauto.
  Qed.

  Theorem ts_free_meta : forall (K : unit -> M R) P,
    (forall s', II sp0 argv envp cb D Bf s' -> ntframe B s1 s' -> tsafe (K tt s') P) ->
    tsafe ((x <- m_free_meta (at_ A_CTX 16) (Z_to_bv 64 g) ;; K x) s1) P.
  Proof.
    intros K P HK. pose proof FW as HW. pose proof (is_rep _ _ _ _ _ _ (ii_is HII)) as HR. pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof (meta_facts B g mg HW Hg) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0.
    rewrite m_free_meta_unfold, addr_fmh. reassoc.
    (* [comment removed for export] *)
    rewrite !at_Z.
    eapply (ts_sd_metaW B HW); [exact RW0 | exact HWIN | exact Hg | lia | lia |]. intros m1 RW1. change (bv_unsigned w0) with 0 in RW1. reassoc.
    replace (Z_to_bv 64 g) with (Z_to_bv 64 (g + 0)) at 1 by (f_equal; lia).
    eapply (ts_sd_metaW B HW); [exact RW1 | exact HWIN | exact Hg | lia | lia |]. intros m2 RW2. change (bv_unsigned w0) with 0 in RW2. rewrite (Z.add_0_r g) in RW2. reassoc.
    eapply (ts_sd_metaW B HW); [exact RW2 | exact HWIN | exact Hg | lia | lia |]. intros m3 RW3. change (bv_unsigned w0) with 0 in RW3. reassoc.
    eapply (ts_sd_metaW B HW); [exact RW3 | exact HWIN | exact Hg | lia | lia |]. intros m4 RW4. change (bv_unsigned w0) with 0 in RW4. reassoc.
    eapply (ts_sd_metaW B HW); [exact RW4 | exact HWIN | exact Hg | lia | lia |]. intros m5 RW5. change (bv_unsigned w0) with 0 in RW5.
    fold zws in RW5. exact (free_meta_rest _ K P m5 eq_refl RW5 HK).
  Qed.

  Lemma addr_fmh_ag : at_ A_LOCK 24 = Z_to_bv 64 (caddr KFmh).
  Proof. rewrite A_LOCK_eq, at_Z. f_equal; cbn; unfold C_FMH; llia. Qed.

  (* [comment removed for export] *)
  Theorem ts_free_meta_ag : forall (K : unit -> M R) P,
    (forall s', II sp0 argv envp cb D Bf s' -> ntframe B s1 s' -> tsafe (K tt s') P) ->
    tsafe ((x <- m_free_meta_ag (at_ A_LOCK 24) (Z_to_bv 64 g) ;; K x) s1) P.
  Proof.
    intros K P HK. pose proof FW as HW. pose proof (is_rep _ _ _ _ _ _ (ii_is HII)) as HR. pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof (meta_facts B g mg HW Hg) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0.
    rewrite m_free_meta_ag_unfold, addr_fmh_ag. reassoc.
    rewrite !at_Z.
    eapply (ts_sd_metaW B HW); [exact RW0 | exact HWIN | exact Hg | lia | lia |]. intros m1 RW1. change (bv_unsigned w0) with 0 in RW1. reassoc.
    eapply (ts_sd_metaW B HW); [exact RW1 | exact HWIN | exact Hg | lia | lia |]. intros m2 RW2. change (bv_unsigned w0) with 0 in RW2. reassoc.
    eapply (ts_sd_metaW B HW); [exact RW2 | exact HWIN | exact Hg | lia | lia |]. intros m3 RW3. change (bv_unsigned w0) with 0 in RW3. reassoc.
    eapply (ts_sd_metaW B HW); [exact RW3 | exact HWIN | exact Hg | lia | lia |]. intros m4 RW4. change (bv_unsigned w0) with 0 in RW4. reassoc.
    replace (Z_to_bv 64 g) with (Z_to_bv 64 (g + 0)) at 1 by (f_equal; lia).
    eapply (ts_sd_metaW B HW); [exact RW4 | exact HWIN | exact Hg | lia | lia |]. intros m5 RW5. change (bv_unsigned w0) with 0 in RW5. rewrite (Z.add_0_r g) in RW5.
    fold zws_ag in RW5. exact (free_meta_rest _ K P m5 eq_refl (RepW_zws_ag m5 RW5) HK).
  Qed.
End FreeMetaCPS.

End WithLayout.
