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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_wf2
  MallocInv_wf3 MallocInv_dll MallocInv_vm MallocInv_tryavail MallocInv_free.
Import ListNotations.
Local Open Scope Z_scope.

Lemma last_In_ne : forall (l : list Z) d, l <> [] -> In (last l d) l.
Proof. intros l d Hne. rewrite last_nth by exact Hne. apply nth_In. destruct l; [contradiction | cbn; lia]. Qed.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeBit.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  (* [comment removed for export] *)
  Hypothesis Hreuse : mt_sc mt < 48 -> Z.lor (mt_avail mt) (mt_freed mt) <> 0 \/ 16 * size_class (mt_sc mt) <= mt_stride mt.

  Definition fb_fr : Z := mt_freed mt + 2 ^ i.
  Definition fb_slots : list slot_st := list_set slots (Z.to_nat i) SIdle.
  Definition fb_mt : meta_rec := MT (gu_f mt (mt_avail mt) fb_fr) (RGroup aib fb_slots).
  Definition fbA : astate := set_live (ameta_upd A ma fb_mt) (a_live A).

  Lemma fb_ilt : (Z.to_nat i < length slots)%nat.
  Proof. apply (proj1 (nth_error_Some slots (Z.to_nat i))). rewrite Hi. discriminate. Qed.

  Lemma fb_grp : 0 <= mt_w32 mt < 2^64 /\ Z.of_nat (length slots) = mt_cnt mt /\
    0 <= mt_avail mt < 2 ^ (mt_cnt mt) /\ 0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\
    Z.land (mt_avail mt) (mt_freed mt) = 0 /\ 0 <= aib < 256 /\ mt_avail mt < 2 ^ (aib mod 32 + 1) /\ aib mod 32 <= mt_last mt /\
    (forall j st, nth_error slots (Z.to_nat j) = Some st -> 0 <= j -> (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) j = true <-> st = SIdle)).
  Proof.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (H1 & _ & _ & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _).
    split; [exact H1|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
    split; [exact H8|]. split; [exact H9|]. split; [exact H10 | exact H11].
  Qed.

  Lemma fb_i_cnt : i < mt_cnt mt.
  Proof. pose proof fb_grp as (_ & Hlen & _). pose proof fb_ilt. lia. Qed.

  (* [comment removed for export] *)
  Lemma fb_bit_clear : Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = false.
  Proof.
    pose proof fb_grp as (_ & _ & _ & _ & _ & _ & _ & _ & Hidle).
    destruct (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i) eqn:E; [| reflexivity].
    exfalso. pose proof (proj1 (Hidle i STaken Hi Hi0) E). discriminate.
  Qed.

  Lemma fb_bit_av : Z.testbit (mt_avail mt) i = false.
  Proof. pose proof fb_bit_clear as E. rewrite Z.lor_spec in E. apply orb_false_iff in E. tauto. Qed.
  Lemma fb_bit_fr : Z.testbit (mt_freed mt) i = false.
  Proof. pose proof fb_bit_clear as E. rewrite Z.lor_spec in E. apply orb_false_iff in E. tauto. Qed.

  Lemma fb_fr_facts : fb_fr = Z.lor (mt_freed mt) (2 ^ i) /\ fb_fr < 2 ^ (mt_cnt mt).
  Proof.
    pose proof fb_grp as (_ & _ & _ & Hfr & _). pose proof fb_i_cnt. unfold fb_fr.
    apply (add_clear_bit (mt_freed mt) i (mt_cnt mt)); [exact Hfr | lia | exact fb_bit_fr].
  Qed.

  Lemma fb_fr_lor : fb_fr = Z.lor (mt_freed mt) (2 ^ i).
  Proof. exact (proj1 fb_fr_facts). Qed.

  Lemma fb_fr_testbit : forall j, 0 <= j -> Z.testbit fb_fr j = (Z.testbit (mt_freed mt) j || (j =? i))%bool.
  Proof.
    intros j Hj. rewrite fb_fr_lor, Z.lor_spec. f_equal. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_sym.
  Qed.

  Lemma fb_fr_range : 0 <= fb_fr < 2 ^ (mt_cnt mt).
  Proof.
    pose proof fb_grp as (_ & _ & _ & Hfr & _). split; [unfold fb_fr; pose proof (Z.pow_nonneg 2 i); lia | exact (proj2 fb_fr_facts)].
  Qed.

  Lemma fb_fr_nz : fb_fr <> 0.
  Proof. pose proof fb_grp as (_ & _ & _ & Hfr & _). unfold fb_fr. pose proof (Z.pow_pos_nonneg 2 i). lia. Qed.

  Theorem WF_fbA : WF fbA.
  Proof.
    pose proof fb_grp as (Hw & Hlen & Hav & Hfr & Hdis & Haib & Havact & Haibl & Hidle).
    apply (WF_grp_upd A HW ma mt aib slots Hma Hr (mt_avail mt) fb_fr aib fb_slots (a_live A)).
    - unfold fb_slots. apply list_set_length.
    - intros j st st' Hj Hj'. unfold fb_slots in Hj'. destruct (list_set_nth_inv _ _ _ _ _ Hj') as [(-> & -> & _) | (Hne & H)].
      + rewrite Hi in Hj. injection Hj as <-. right. split; [right; left; reflexivity | left; reflexivity].
      + rewrite H in Hj. injection Hj as <-. left. reflexivity.
    - exact Hav.
    - exact fb_fr_range.
    - apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, fb_fr_testbit by lia.
      destruct (Z.eqb_spec j i) as [-> | Hne]; [rewrite fb_bit_av; reflexivity|].
      rewrite orb_false_r. rewrite <- Z.land_spec, Hdis. apply Z.bits_0.
    - exact Haib.
    - exact Havact.
    - exact Haibl.
    - intros j st Hj Hj0. rewrite Z.lor_spec, fb_fr_testbit by lia. unfold fb_slots in Hj.
      destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(E & -> & _) | (Hne & H)].
      + assert (j = i) by lia. subst j. rewrite Z.eqb_refl, !orb_true_r. tauto.
      + replace (j =? i) with false by (symmetry; apply Z.eqb_neq; lia). rewrite orb_false_r, <- Z.lor_spec. apply Hidle; [exact H | exact Hj0].
    - intros j off n Hj Hj0. unfold fb_slots in Hj. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(_ & E & _) | (Hne & H)]; [discriminate E|].
      exact (wf_live A HW ma mt aib slots j off n Hma Hr H Hj0).
    - intros j Hj. rewrite fb_fr_testbit by lia. rewrite (wf_inactive A HW ma mt aib slots j Hma Hr Hj). reflexivity.
    - intros Hin Hne. split; [exact (proj1 (wf_act_nonhead A HW _ _ _ Hin Hne Hma)) | exact fb_fr_nz].
    - intros H. exact H.
    - intros Hsc _. exact (Hreuse Hsc).
    - (* [comment removed for export] *)
      intros q k. rewrite (wf_live_map A HW q k). unfold is_live. split.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & E).
        destruct (Z.eq_dec x ma) as [-> | Hne].
        * left. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          exists j, off. split; [exact Hj0|]. split; [| exact E].
          unfold fb_slots. rewrite list_set_nth_other; [exact Hj|]. intros E2. rewrite <- E2, Hi in Hj. discriminate Hj.
        * right. exists x, mtx, aibx, slx, j, off. auto 10.
      + intros [(j & off & Hj0 & Hj & E) | (x & mtx & aibx & slx & j & off & Hne & Hx & Hrx & Hj0 & Hj & E)].
        * exists ma, mt, aib, slots, j, off. split; [exact Hma|]. split; [exact Hr|]. split; [exact Hj0|]. split; [| exact E].
          unfold fb_slots in Hj. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(_ & Ebad & _) | (_ & H)]; [discriminate Ebad | exact H].
        * exists x, mtx, aibx, slx, j, off. auto 10.
  Qed.

  Lemma fbA_meta_same : a_meta fbA ma = Some fb_mt.
  Proof. unfold fbA, set_live, ameta_upd, set_meta. cbn. apply aupd_same. Qed.

  Lemma fbA_meta_other : forall x, x <> ma -> a_meta fbA x = a_meta A x.
  Proof. intros x Hne. unfold fbA, set_live, ameta_upd, set_meta. cbn. apply aupd_other. exact Hne. Qed.

  Lemma fbA_ctx : a_ctx fbA = a_ctx A. Proof. reflexivity. Qed.
  Lemma fbA_active : a_active fbA = a_active A. Proof. reflexivity. Qed.
  Lemma fbA_areas : a_areas fbA = a_areas A. Proof. reflexivity. Qed.
  Lemma fbA_freelist : a_freelist fbA = a_freelist A. Proof. reflexivity. Qed.
  Lemma fbA_live : a_live fbA = a_live A. Proof. reflexivity. Qed.
  Lemma fbA_xmaps : a_xmaps fbA = a_xmaps A. Proof. reflexivity. Qed.

  Lemma fb_mt_f : forall fl, mt_f fb_mt fl = if mfield_eq_dec fl FFreed then fb_fr else mt_f mt fl.
  Proof.
    intros fl. unfold fb_mt. rewrite mt_f_MT. unfold gu_f.
    destruct fl; cbn; try reflexivity.
  Qed.

  Lemma dom_fbA : forall x, dom fbA x <-> dom A x.
  Proof. exact (dom_grp_upd A ma mt aib slots Hma Hr (mt_avail mt) fb_fr aib fb_slots (a_live A)). Qed.

  Lemma VMok_fbA : forall h, VMok A h -> VMok fbA h.
  Proof. exact (VMok_grp_upd A ma mt aib slots Hma Hr (mt_avail mt) fb_fr aib fb_slots (a_live A)). Qed.
End FreeBit.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma hd_app_g : forall (l : list Z) g d, hd d (l ++ [g]) = hd g l.
Proof. intros l g d. destruct l; reflexivity. Qed.

Lemma last_default_ne : forall (l : list Z) d d', l <> [] -> last l d = last l d'.
Proof. intros l d d' Hne. rewrite !last_nth by exact Hne. apply nth_indep. destruct l; [contradiction | cbn; lia]. Qed.

Lemma hd_default_ne : forall (l : list Z) d d', l <> [] -> hd d l = hd d' l.
Proof. intros l d d' Hne. destruct l; [contradiction | reflexivity]. Qed.

Section Queue.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (sc g : Z) (mg : meta_rec) (aibg : Z) (slg : list slot_st) (l : list Z) (h t : Z).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hg : a_meta A g = Some mg.
  Hypothesis Hrg : mt_role mg = RGroup aibg slg.
  Hypothesis Hscg : mt_sc mg = sc.
  Hypothesis Hl : a_active A sc = l.
  Hypothesis Hh : h = hd g l.
  Hypothesis Ht : t = last l g.
  Hypothesis Hnin : ~ In g l.
  (* [comment removed for export] *)
  Hypothesis Hav0 : l <> [] -> mt_avail mg = 0.
  Hypothesis Hfr1 : l <> [] -> mt_freed mg <> 0.
  Hypothesis Hfull : l <> [] -> ~ (aibg mod 32 < mt_last mg).

  Definition qN : Z -> option Z := fun x => if x =? t then Some g else if x =? g then Some h else None.
  Definition qP : Z -> option Z := fun x => if x =? h then Some g else if x =? g then Some t else None.
  Definition que_act : Z -> list Z := fun c => if Z.eq_dec c sc then l ++ [g] else a_active A c.
  Definition queA : astate := MallocInv_wf3.A' A qP qN que_act (a_freelist A) None.

  Lemma l_mem : forall x, In x l -> exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt = sc.
  Proof. intros x Hx. apply (wf_act_mem A HW sc x). rewrite Hl. exact Hx. Qed.

  Lemma h_in : l <> [] -> In h l.
  Proof. intros Hne. rewrite Hh. destruct l; [contradiction | left; reflexivity]. Qed.
  Lemma t_in : l <> [] -> In t l.
  Proof. intros Hne. rewrite Ht. apply last_In_ne. exact Hne. Qed.
  Lemma h_ne_g : l <> [] -> h <> g.
  Proof. intros Hne E. apply Hnin. rewrite <- E. exact (h_in Hne). Qed.
  Lemma t_ne_g : l <> [] -> t <> g.
  Proof. intros Hne E. apply Hnin. rewrite <- E. exact (t_in Hne). Qed.
  Lemma h_nil : l = [] -> h = g.
  Proof. intros E. rewrite Hh, E. reflexivity. Qed.
  Lemma t_nil : l = [] -> t = g.
  Proof. intros E. rewrite Ht, E. reflexivity. Qed.

  Lemma l_nodup : List.NoDup l.
  Proof. apply (proj1 (NoDup_ListNoDup _)). rewrite <- Hl. exact (wf_act_nodup A HW sc). Qed.

  Lemma h_nth : l <> [] -> nth_error l 0 = Some h.
  Proof. intros Hne. rewrite Hh. destruct l; [contradiction | reflexivity]. Qed.
  Lemma t_nth : l <> [] -> nth_error l (length l - 1) = Some t.
  Proof.
    intros Hne. rewrite Ht, (last_nth l g Hne). apply nth_error_nth'. destruct l; [contradiction | cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma nth_is_h : forall k x, nth_error l k = Some x -> (x = h <-> k = 0%nat).
  Proof.
    intros k x Hk. assert (Hne : l <> []) by (intros E; rewrite E in Hk; destruct k; discriminate Hk).
    split.
    - intros ->. apply (proj1 (List.NoDup_nth_error l) l_nodup k 0%nat).
      + apply (proj1 (nth_error_Some l k)). rewrite Hk. discriminate.
      + rewrite Hk, (h_nth Hne). reflexivity.
    - intros ->. rewrite (h_nth Hne) in Hk. injection Hk as ->. reflexivity.
  Qed.
  Lemma nth_is_t : forall k x, nth_error l k = Some x -> (x = t <-> S k = length l).
  Proof.
    intros k x Hk. assert (Hne : l <> []) by (intros E; rewrite E in Hk; destruct k; discriminate Hk).
    assert (Hkl : (k < length l)%nat) by (apply (proj1 (nth_error_Some l k)); rewrite Hk; discriminate).
    split.
    - intros ->. enough (k = length l - 1)%nat by lia. apply (proj1 (List.NoDup_nth_error l) l_nodup k (length l - 1)%nat Hkl).
      rewrite Hk, (t_nth Hne). reflexivity.
    - intros E. replace k with (length l - 1)%nat in Hk by lia. rewrite (t_nth Hne) in Hk. injection Hk as ->. reflexivity.
  Qed.

  Lemma queA_meta : forall x, a_meta queA x = option_map (MallocInv_wf3.relink qP qN x) (a_meta A x).
  Proof. intros x. reflexivity. Qed.

  Lemma queA_meta_inv : forall x mt', a_meta queA x = Some mt' -> exists mt, a_meta A x = Some mt /\ mt' = MallocInv_wf3.relink qP qN x mt.
  Proof.
    intros x mt' Hx. rewrite queA_meta in Hx. destruct (a_meta A x) as [mt|]; [| discriminate Hx]. cbn in Hx. injection Hx as <-. exists mt. auto.
  Qed.

  Lemma relink_next : forall x mt, mt_next (MallocInv_wf3.relink qP qN x mt) = if x =? t then g else if x =? g then h else mt_next mt.
  Proof.
    intros x mt. unfold mt_next, MallocInv_wf3.relink. rewrite mt_f_MT. unfold qN.
    destruct (x =? t); [reflexivity|]. destruct (x =? g); reflexivity.
  Qed.
  Lemma relink_prev : forall x mt, mt_prev (MallocInv_wf3.relink qP qN x mt) = if x =? h then g else if x =? g then t else mt_prev mt.
  Proof.
    intros x mt. unfold mt_prev, MallocInv_wf3.relink. rewrite mt_f_MT. unfold qP.
    destruct (x =? h); [reflexivity|]. destruct (x =? g); reflexivity.
  Qed.

  Lemma relink_other : forall x mt, x <> g -> x <> h -> x <> t -> MallocInv_wf3.relink qP qN x mt = mt.
  Proof.
    intros x mt H1 H2 H3. unfold MallocInv_wf3.relink, qP, qN.
    apply meta_ext; [reflexivity|]. intros fl. rewrite mt_f_MT.
    rewrite ?(proj2 (Z.eqb_neq x g) H1), ?(proj2 (Z.eqb_neq x h) H2), ?(proj2 (Z.eqb_neq x t) H3); destruct fl; reflexivity.
  Qed.

  Lemma relink_nonmember : forall x mt, x <> g -> ~ In x l -> MallocInv_wf3.relink qP qN x mt = mt.
  Proof.
    intros x mt Hxg Hxl. destruct (list_eq_dec Z.eq_dec l []) as [El | El].
    - apply relink_other; [exact Hxg | rewrite (h_nil El); exact Hxg | rewrite (t_nil El); exact Hxg].
    - apply relink_other; [exact Hxg | |]; intros ->; apply Hxl; [apply h_in | apply t_in]; exact El.
  Qed.

  Lemma relink_nongroup : forall x mt, a_meta A x = Some mt -> ~ is_group mt -> MallocInv_wf3.relink qP qN x mt = mt.
  Proof.
    intros x mt Hx Hng. apply (relink_nonmember x mt).
    - intros ->. rewrite Hg in Hx. injection Hx as <-. apply Hng. exists aibg, slg. exact Hrg.
    - intros Hin. destruct (l_mem x Hin) as (mt' & aib & sl & Hx' & Hr' & _). rewrite Hx in Hx'. injection Hx' as <-. apply Hng. exists aib, sl. exact Hr'.
  Qed.

  Lemma relink_otherclass : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> mt_sc mt <> sc ->
    MallocInv_wf3.relink qP qN x mt = mt.
  Proof.
    intros x mt aib sl Hx Hr Hs. apply (relink_nonmember x mt).
    - intros ->. rewrite Hg in Hx. injection Hx as <-. exact (Hs Hscg).
    - intros Hin. destruct (l_mem x Hin) as (mt' & aib' & sl' & Hx' & _ & Hs'). rewrite Hx in Hx'. injection Hx' as <-. exact (Hs Hs').
  Qed.

  Lemma queA_meta_other : forall x, x <> g -> ~ In x l -> a_meta queA x = a_meta A x.
  Proof.
    intros x Hxg Hxl. rewrite queA_meta. destruct (a_meta A x) as [mt|]; [cbn | reflexivity]. rewrite (relink_nonmember x mt Hxg Hxl). reflexivity.
  Qed.

  Lemma queA_active_sc : a_active queA sc = l ++ [g].
  Proof. unfold queA, MallocInv_wf3.A', que_act. cbn. destruct (Z.eq_dec sc sc); [reflexivity | contradiction]. Qed.
  Lemma queA_active_other : forall c, c <> sc -> a_active queA c = a_active A c.
  Proof. intros c Hc. unfold queA, MallocInv_wf3.A', que_act. cbn. destruct (Z.eq_dec c sc); [contradiction | reflexivity]. Qed.
  Lemma queA_ctx : a_ctx queA = MallocInv_wf3.c' A que_act (a_freelist A). Proof. reflexivity. Qed.
  Lemma queA_areas : a_areas queA = a_areas A. Proof. reflexivity. Qed.
  Lemma queA_freelist : a_freelist queA = a_freelist A. Proof. reflexivity. Qed.
  Lemma queA_live : a_live queA = a_live A. Proof. reflexivity. Qed.
  Lemma queA_xmaps : a_xmaps queA = a_xmaps A. Proof. reflexivity. Qed.
  Lemma queA_pages : a_pages queA = a_pages A. Proof. reflexivity. Qed.

  Lemma hd_lg : hd 0 (l ++ [g]) = h.
  Proof. rewrite Hh. apply hd_app_g. Qed.

  Lemma queA_ctx_valid : forall k, cvalid k -> a_ctx queA k = if cslot_eq_dec k (KActive sc) then h else a_ctx A k.
  Proof.
    clear Hfull Hfr1 Hav0 Hscg Hrg Hg mg aibg slg. 
    intros k Hk. unfold queA, MallocInv_wf3.A', MallocInv_wf3.c'. cbn. destruct k; try reflexivity.
    - destruct (cslot_eq_dec KFmh (KActive sc)) as [E|_]; [discriminate E|]. symmetry. apply (wf_fl_head A HW).
    - unfold que_act. destruct (Z.eq_dec i sc) as [-> | Hne].
      + destruct (cslot_eq_dec (KActive sc) (KActive sc)); [exact hd_lg | contradiction].
      + destruct (cslot_eq_dec (KActive i) (KActive sc)) as [E | _]; [injection E; lia|]. symmetry. apply (wf_act_head A HW). exact Hk.
  Qed.

  Theorem WF_queA : WF queA.
  Proof.
    assert (GONLY : forall x mt, a_meta A x = Some mt -> MallocInv_wf3.g' A qP qN None x = Some (MallocInv_wf3.relink qP qN x mt)).
    { intros x mt Hx. change (MallocInv_wf3.g' A qP qN None x) with (a_meta queA x). rewrite queA_meta, Hx. reflexivity. }
    assert (GINV : forall x mt', MallocInv_wf3.g' A qP qN None x = Some mt' -> exists mt, a_meta A x = Some mt /\ mt' = MallocInv_wf3.relink qP qN x mt).
    { intros x mt' Hx. exact (queA_meta_inv x mt' Hx). }
    assert (MEM : forall x, In x (l ++ [g]) <-> In x l \/ x = g).
    { intros x. rewrite in_app_iff. cbn. split; [intros [H|[H|[]]]; [left; exact H | right; symmetry; exact H] | intros [H|H]; [left; exact H | right; left; symmetry; exact H]]. }
    apply WF_relists; try exact HW.
    - exact I.
    - exact (wf_fl_nodup A HW).
    - intros x. rewrite (wf_fl_mem A HW x). change (MallocInv_wf3.g' A qP qN None x) with (a_meta queA x). rewrite queA_meta.
      destruct (a_meta A x) as [mt|]; cbn; [| split; intros (mt & Hmt & _); discriminate Hmt].
      split; intros (mt' & E & Hr); injection E as <-; [eexists; split; [reflexivity | exact Hr] | exists mt; cbn in Hr; auto].
    - apply (dll_transfer A queA _ (wf_fl_dll A HW)). intros y mt Hin Hy.
      destruct (proj1 (wf_fl_mem A HW y) Hin) as (mt' & Hy' & Hr'). rewrite Hy in Hy'. injection Hy' as <-.
      exists mt. rewrite queA_meta, Hy. cbn. rewrite (relink_nongroup y mt Hy) by (intros (aib & sl & R); rewrite Hr' in R; discriminate R). auto.
    - intros c. unfold que_act. destruct (Z.eq_dec c sc) as [-> | Hne]; [| exact (wf_act_nodup A HW c)].
      apply (proj2 (NoDup_ListNoDup _)). apply List.NoDup_app; [exact l_nodup | constructor; [intros [] | constructor] |].
      intros x Hx [<- | []]. exact (Hnin Hx).
    - intros c Hc. unfold que_act. destruct (Z.eq_dec c sc) as [-> | Hne].
      + destruct (list_eq_dec Z.eq_dec l []) as [El | El].
        * rewrite El. cbn [app]. apply (dll_single' queA g (MallocInv_wf3.relink qP qN g mg)).
          -- rewrite queA_meta, Hg. reflexivity.
          -- rewrite relink_next, (t_nil El), Z.eqb_refl. reflexivity.
          -- rewrite relink_prev, (h_nil El), Z.eqb_refl. reflexivity.
        * apply (dll_snoc A queA l g El).
          -- rewrite <- Hl. exact (wf_act_dll A HW sc Hsc).
          -- intros k x mt Hk Hx. pose proof (nth_error_In _ _ Hk) as Hin.
             assert (Hxg : x <> g) by (intros ->; exact (Hnin Hin)).
             exists (MallocInv_wf3.relink qP qN x mt). rewrite queA_meta, Hx. split; [reflexivity|].
             rewrite relink_next, relink_prev, (proj2 (Z.eqb_neq x g) Hxg). split.
             ++ destruct (Z.eqb_spec x t) as [E | NE].
                ** rewrite (proj2 (Nat.eqb_eq _ _) (proj1 (nth_is_t k x Hk) E)). reflexivity.
                ** destruct (Nat.eqb_spec (S k) (length l)) as [E2 | NE2]; [exfalso; exact (NE (proj2 (nth_is_t k x Hk) E2)) | reflexivity].
             ++ destruct (Z.eqb_spec x h) as [E | NE].
                ** rewrite (proj2 (Nat.eqb_eq _ _) (proj1 (nth_is_h k x Hk) E)). reflexivity.
                ** destruct (Nat.eqb_spec k 0) as [E2 | NE2]; [exfalso; exact (NE (proj2 (nth_is_h k x Hk) E2)) | reflexivity].
          -- exists (MallocInv_wf3.relink qP qN g mg). rewrite queA_meta, Hg. split; [reflexivity|].
             rewrite relink_next, relink_prev, Z.eqb_refl.
             rewrite (proj2 (Z.eqb_neq g t) ltac:(intros E; apply (t_ne_g El); symmetry; exact E)).
             rewrite (proj2 (Z.eqb_neq g h) ltac:(intros E; apply (h_ne_g El); symmetry; exact E)).
             rewrite (hd_default_ne l 0 g El), (last_default_ne l 0 g El), Hh, Ht. split; reflexivity.
      + apply (dll_transfer A queA (a_active A c) (wf_act_dll A HW c Hc)).
        intros y mty Hin Hy. destruct (wf_act_mem A HW c y Hin) as (mt0 & aib & sl & Hy0 & Hr0 & Hs0). rewrite Hy in Hy0. injection Hy0 as <-.
        exists mty. rewrite queA_meta, Hy. cbn. rewrite (relink_otherclass y mty aib sl Hy Hr0) by lia. auto.
    - intros c x Hin. unfold que_act in Hin.
      destruct (Z.eq_dec c sc) as [-> | Hne].
      + apply MEM in Hin. destruct Hin as [Hin | ->].
        * destruct (l_mem x Hin) as (mt & aib & sl & Hx & Hr & Hs). exists (MallocInv_wf3.relink qP qN x mt), aib, sl.
          rewrite (GONLY x mt Hx). cbn. auto.
        * exists (MallocInv_wf3.relink qP qN g mg), aibg, slg. rewrite (GONLY g mg Hg). cbn. auto.
      + destruct (wf_act_mem A HW c x Hin) as (mt & aib & sl & Hx & Hr & Hs). exists (MallocInv_wf3.relink qP qN x mt), aib, sl.
        rewrite (GONLY x mt Hx). cbn. auto.
    - intros x mt' aib sl Hx Hr' Hnin'. destruct (GINV x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      rewrite MallocInv_wf3.rl_sc in Hnin'.
      assert (Hxg : x <> g).
      { intros ->. apply Hnin'. unfold que_act. rewrite Hg in Hx0. injection Hx0 as <-. rewrite Hscg.
        destruct (Z.eq_dec sc sc); [| contradiction]. apply in_app_iff. right. left. reflexivity. }
      assert (Hxl : ~ In x l).
      { intros Hinl. destruct (l_mem x Hinl) as (mt0 & aib0 & sl0 & Hx1 & _ & Hs1). rewrite Hx0 in Hx1. injection Hx1 as <-.
        apply Hnin'. unfold que_act. rewrite Hs1. destruct (Z.eq_dec sc sc); [| contradiction]. apply in_app_iff. left. exact Hinl. }
      rewrite (relink_nonmember x mt Hxg Hxl) in *. apply (wf_unlinked A HW x mt aib sl Hx0 Hr').
      intros Hin. apply Hnin'. unfold que_act. destruct (Z.eq_dec (mt_sc mt) sc) as [E | Hne]; [| exact Hin].
      exfalso. apply Hxl. rewrite <- Hl, <- E. exact Hin.
    - intros c x mt' Hin Hne Hx. destruct (GINV x mt' Hx) as (mt & Hx0 & ->).
      rewrite MallocInv_wf3.rl_avail, MallocInv_wf3.rl_freed.
      unfold que_act in Hin, Hne. destruct (Z.eq_dec c sc) as [-> | Hc]; [| exact (wf_act_nonhead A HW c x mt Hin Hne Hx0)].
      apply MEM in Hin. destruct Hin as [Hin | ->].
      + apply (wf_act_nonhead A HW sc x mt); [rewrite Hl; exact Hin | | exact Hx0]. rewrite hd_lg in Hne. rewrite Hl.
        assert (El : l <> []) by (intros E; rewrite E in Hin; exact Hin).
        rewrite (hd_default_ne l 0 g El), <- Hh. exact Hne.
      + rewrite Hg in Hx0. injection Hx0 as <-. destruct (list_eq_dec Z.eq_dec l []) as [El | El]; [| split; [exact (Hav0 El) | exact (Hfr1 El)]].
        exfalso. apply Hne. rewrite hd_lg, (h_nil El). reflexivity.
    - intros x mt' aib sl Hx Hr' H63. destruct (GINV x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      rewrite MallocInv_wf3.rl_sc in H63.
      rewrite (relink_otherclass x mt aib sl Hx0 Hr') by lia. exact (wf_act63 A HW x mt aib sl Hx0 Hr' H63).
    - intros c x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry.
      destruct (GINV x mtx Hx) as (mx0 & Hmx0 & ->). destruct (GINV y mty Hy) as (my0 & Hmy0 & ->). cbn in Hrx, Hry.
      rewrite !MallocInv_wf3.rl_last. unfold que_act in Hinx, Hiny.
      destruct (Z.eq_dec c sc) as [-> | Hne]; [| exact (wf_partial A HW c x mx0 aibx slx y my0 aiby sly Hinx Hiny Hmx0 Hrx Hmy0 Hry)].
      apply MEM in Hinx. apply MEM in Hiny. intros Hpx Hpy.
      destruct Hinx as [Hinx | ->]; destruct Hiny as [Hiny | ->].
      + rewrite <- Hl in Hinx, Hiny. exact (wf_partial A HW sc x mx0 aibx slx y my0 aiby sly Hinx Hiny Hmx0 Hrx Hmy0 Hry Hpx Hpy).
      + exfalso. rewrite Hg in Hmy0. injection Hmy0 as <-. rewrite Hrg in Hry. injection Hry as <- <-. exact (Hfull ltac:(intros E; rewrite E in Hinx; exact Hinx) Hpy).
      + exfalso. rewrite Hg in Hmx0. injection Hmx0 as <-. rewrite Hrg in Hrx. injection Hrx as <- <-. exact (Hfull ltac:(intros E; rewrite E in Hiny; exact Hiny) Hpx).
      + reflexivity.
    - intros x mt' Hx Hr'. destruct (GINV x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      rewrite (relink_nongroup x mt Hx0) by (intros (aib & sl & R); rewrite Hr' in R; discriminate R). exact (wf_avail_zero A HW x mt Hx0 Hr').
    - intros x mt' Hx Hr'. destruct (GINV x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      rewrite (relink_nongroup x mt Hx0) by (intros (aib & sl & R); rewrite Hr' in R; discriminate R). exact (wf_free_zero A HW x mt Hx0 Hr').
  Qed.

  Lemma dom_queA : forall x, dom queA x <-> dom A x.
  Proof. intros x. apply (MallocInv_wf3.dom_relists A qP qN que_act (a_freelist A) None I). Qed.

  Lemma VMok_queA : forall hh, VMok A hh -> VMok queA hh.
  Proof. intros hh HV. apply (MallocInv_wf3.VMok_relists A qP qN que_act (a_freelist A) None I). exact HV. Qed.

  (* [comment removed for export] *)
  Lemma has_queA_intro : forall f, has A f ->
    f <> FCT (caddr (KActive sc)) 8 (a_ctx A (KActive sc)) ->
    (forall x mt fl, a_meta A x = Some mt -> f = FCT (x + moff fl) (mlen fl) (mt_f mt fl) ->
       (fl = FNext -> x <> t /\ x <> g) /\ (fl = FPrev -> x <> h /\ x <> g)) ->
    has queA f.
  Proof.
    clear Hfull Hfr1 Hav0 Hscg Hrg Hg mg aibg slg. 
    intros f Hf Hne Hlk. destruct Hf as [(k & Hk & ->) | [Har | [Hm | Hgr]]].
    - replace (a_ctx A k) with (a_ctx queA k); [apply (MallocInv_wf3.relists_has_ctx A qP qN que_act (a_freelist A) None k Hk)|].
      rewrite (queA_ctx_valid k Hk). destruct (cslot_eq_dec k (KActive sc)) as [-> | _]; [exfalso; apply Hne; reflexivity | reflexivity].
    - apply MallocInv_wf3.relists_has_area. exact Har.
    - destruct Hm as (x & mt & fl & Hx & ->).
      replace (mt_f mt fl) with (mt_f (MallocInv_wf3.relink qP qN x mt) fl).
      + apply (MallocInv_wf3.relists_has_meta A qP qN que_act (a_freelist A) None x _ fl).
        change (MallocInv_wf3.g' A qP qN None x) with (a_meta queA x). rewrite queA_meta, Hx. reflexivity.
      + destruct (Hlk x mt fl Hx eq_refl) as [HN HP].
        unfold MallocInv_wf3.relink. rewrite mt_f_MT. destruct fl; try reflexivity.
        * destruct (HP eq_refl) as [H1 H2]. unfold qP. rewrite (proj2 (Z.eqb_neq x h) H1), (proj2 (Z.eqb_neq x g) H2). reflexivity.
        * destruct (HN eq_refl) as [H1 H2]. unfold qN. rewrite (proj2 (Z.eqb_neq x t) H1), (proj2 (Z.eqb_neq x g) H2). reflexivity.
    - apply MallocInv_wf3.relists_has_grp_kept; [exact I | exact Hgr].
  Qed.

  Lemma has_queA_ctx : has queA (FCT (caddr (KActive sc)) 8 h).
  Proof.
    clear Hfull Hfr1 Hav0 Hscg Hrg Hg mg aibg slg. 
    replace h with (a_ctx queA (KActive sc)) at 1.
    - apply (MallocInv_wf3.relists_has_ctx A qP qN que_act (a_freelist A) None (KActive sc)). exact Hsc.
    - rewrite (queA_ctx_valid (KActive sc) Hsc). destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
  Qed.

  Lemma has_queA_meta : forall x mt fl, a_meta A x = Some mt ->
    has queA (FCT (x + moff fl) (mlen fl) (mt_f (MallocInv_wf3.relink qP qN x mt) fl)).
  Proof.
    intros x mt fl Hx. apply (MallocInv_wf3.relists_has_meta A qP qN que_act (a_freelist A) None x _ fl).
    change (MallocInv_wf3.g' A qP qN None x) with (a_meta queA x). rewrite queA_meta, Hx. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma has_queA_inv : forall f, has queA f ->
    has A f \/ f = FCT (caddr (KActive sc)) 8 h \/
    exists x mt fl, a_meta A x = Some mt /\ (fl = FNext \/ fl = FPrev) /\ (x = g \/ x = h \/ x = t) /\
      f = FCT (x + moff fl) (mlen fl) (mt_f (MallocInv_wf3.relink qP qN x mt) fl).
  Proof.
    clear Hfull Hfr1 Hav0 Hscg Hrg Hg mg aibg slg. 
    intros f Hf. destruct (MallocInv_wf3.relists_has_inv A qP qN que_act (a_freelist A) None I f Hf) as [(k & Hk & ->) | Hrest].
    - change (MallocInv_wf3.c' A que_act (a_freelist A) k) with (a_ctx queA k). rewrite (queA_ctx_valid k Hk).
      destruct (cslot_eq_dec k (KActive sc)) as [-> | Hne]; [right; left; reflexivity | left; left; exists k; auto].
    - destruct Hrest as [Har | [(x & mt' & fl & Hx & ->) | Hgr]].
      + left. right; left. exact Har.
      + change (MallocInv_wf3.g' A qP qN None x) with (a_meta queA x) in Hx. destruct (queA_meta_inv x mt' Hx) as (mt & Hx0 & ->).
        destruct (Z.eq_dec x g) as [-> | H1].
        * destruct fl; try (left; right; right; left; exists g, mt; eexists; split; [exact Hx0 | unfold MallocInv_wf3.relink; rewrite mt_f_MT; reflexivity]).
          -- right; right. exists g, mt, FPrev. auto 10.
          -- right; right. exists g, mt, FNext. auto 10.
        * destruct (Z.eq_dec x h) as [-> | H2].
          -- destruct fl; try (left; right; right; left; exists h, mt; eexists; split; [exact Hx0 | unfold MallocInv_wf3.relink; rewrite mt_f_MT; reflexivity]).
             ++ right; right. exists h, mt, FPrev. auto 10.
             ++ right; right. exists h, mt, FNext. auto 10.
          -- destruct (Z.eq_dec x t) as [-> | H3].
             ++ destruct fl; try (left; right; right; left; exists t, mt; eexists; split; [exact Hx0 | unfold MallocInv_wf3.relink; rewrite mt_f_MT; reflexivity]).
                ** right; right. exists t, mt, FPrev. auto 10.
                ** right; right. exists t, mt, FNext. auto 10.
             ++ left. right; right; left. exists x, mt, fl. rewrite (relink_other x mt H1 H2 H3). auto.
      + left. right; right; right. exact Hgr.
  Qed.
End Queue.

End WithLayout.
