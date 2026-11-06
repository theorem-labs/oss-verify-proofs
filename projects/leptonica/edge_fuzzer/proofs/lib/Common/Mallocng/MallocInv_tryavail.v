(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_ameta_iface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_group (mt : meta_rec) : Prop := exists aib sl, mt_role mt = RGroup aib sl.

Record tkeep (A A' : astate) (sc : Z) : Prop := {
  tk_live : a_live A' = a_live A;
  tk_areas : a_areas A' = a_areas A;
  tk_fl : a_freelist A' = a_freelist A;
  tk_pages : a_pages A' = a_pages A;
  (* [comment removed for export] *)
  tk_nongrp : forall x mt, a_meta A x = Some mt -> ~ is_group mt -> a_meta A' x = Some mt;
  (* [comment removed for export] *)
  tk_grp : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl /\ mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt;
  (* [comment removed for export] *)
  tk_back : forall x mt', a_meta A' x = Some mt' ->
    exists mt, a_meta A x = Some mt /\ (mt' = mt \/ (is_group mt /\ is_group mt' /\ mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt /\
                                        forall aib sl aib' sl', mt_role mt = RGroup aib sl -> mt_role mt' = RGroup aib' sl' -> sl' = sl));
  tk_act : forall c, c <> sc -> a_active A' c = a_active A c;
  tk_ctx : forall k, cvalid k -> k <> KActive sc -> (forall i, k <> KBounce i) -> a_ctx A' k = a_ctx A k
}.

Lemma tkeep_refl : forall A sc, tkeep A A sc.
Proof.
  intros A sc. constructor; auto.
  - intros x mt aib sl Hx Hr. exists mt, aib. auto.
  - intros x mt' Hx. exists mt'. auto.
Qed.

Lemma tkeep_trans : forall A B C sc, tkeep A B sc -> tkeep B C sc -> tkeep A C sc.
Proof.
  intros A B C sc [L1 Ar1 F1 P1 N1 G1 K1 T1 X1] [L2 Ar2 F2 P2 N2 G2 K2 T2 X2]. constructor.
  - rewrite L2. exact L1.
  - rewrite Ar2. exact Ar1.
  - rewrite F2. exact F1.
  - rewrite P2. exact P1.
  - intros x mt Hx Hng. apply N2; [apply N1; assumption | exact Hng].
  - intros x mt aib sl Hx Hr. destruct (G1 x mt aib sl Hx Hr) as (mt1 & aib1 & H1 & R1 & W1 & M1).
    destruct (G2 x mt1 aib1 sl H1 R1) as (mt2 & aib2 & H2 & R2 & W2 & M2).
    exists mt2, aib2. rewrite W2, M2. auto.
  - intros x mt2 Hx2. destruct (K2 x mt2 Hx2) as (mt1 & Hx1 & D2). destruct (K1 x mt1 Hx1) as (mt0 & Hx0 & D1).
    exists mt0. split; [exact Hx0|].
    destruct D1 as [-> | (G0 & G1' & W1 & M1 & S1)]; [exact D2|].
    destruct D2 as [-> | (G1'' & G2' & W2 & M2 & S2)]; [right; auto|].
    right. split; [exact G0|]. split; [exact G2'|]. rewrite W2, M2. split; [exact W1|]. split; [exact M1|].
    intros aib sl aib' sl' R0 R2. destruct G1' as (aib1 & sl1 & R1). rewrite (S2 aib1 sl1 aib' sl' R1 R2). exact (S1 aib sl aib1 sl1 R0 R1).
  - intros c Hc. rewrite (T2 c Hc). exact (T1 c Hc).
  - intros k Hv H1 H2. rewrite (X2 k Hv H1 H2). exact (X1 k Hv H1 H2).
Qed.

Section TkeepFacts.
  Variables (A A' : astate) (sc : Z).
  Hypothesis TK : tkeep A A' sc.

  Lemma tk_grp_back : forall x mt' aib' sl, a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl ->
    exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt.
  Proof.
    intros x mt' aib' sl Hx Hr. destruct (tk_back _ _ _ TK x mt' Hx) as (mt & Hm & [-> | (G0 & G1 & W & M & S)]).
    - exists mt, aib'. auto.
    - destruct G0 as (aib & sl0 & R0). exists mt, aib. rewrite (S aib sl0 aib' sl R0 Hr). auto.
  Qed.

  Lemma tk_dom : forall x, dom A' x <-> dom A x.
  Proof.
    intros x. unfold dom. rewrite (tk_areas _ _ _ TK), (tk_pages _ _ _ TK). split.
    - intros [Ha | [(y & mty & aib & sl & Hy & Hry & Hml & R) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      destruct (tk_grp_back y mty aib sl Hy Hry) as (mt & aib0 & Hm & Hr & W & M).
      exists y, mt, aib0, sl. unfold mt_maplen, grp_map_len, mt_maplen in *. rewrite <- W, <- M. auto.
    - intros [Ha | [(y & mt & aib & sl & Hy & Hry & Hml & R) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      destruct (tk_grp _ _ _ TK y mt aib sl Hy Hry) as (mt' & aib' & Hm & Hr & W & M).
      exists y, mt', aib', sl. unfold mt_maplen, grp_map_len, mt_maplen in *. rewrite W, M. auto.
  Qed.

  Lemma tk_usage : forall c, usage_of A' c = usage_of A c.
  Proof.
    intros c. apply usage_of_ext; [exact (tk_areas _ _ _ TK)|].
    intros ma. unfold meta_usage.
    destruct (a_meta A ma) as [mt|] eqn:E.
    - destruct (mt_role mt) as [| | |aib sl] eqn:Er.
      1-3: rewrite (tk_nongrp _ _ _ TK ma mt E) by (intros (aib & sl & R); rewrite Er in R; discriminate R); rewrite Er; reflexivity.
      destruct (tk_grp _ _ _ TK ma mt aib sl E Er) as (mt' & aib' & -> & -> & W & M).
      unfold mt_sc, mt_cnt, mt_last. rewrite W. reflexivity.
    - destruct (a_meta A' ma) as [mt'|] eqn:E'; [| reflexivity].
      destruct (tk_back _ _ _ TK ma mt' E') as (mt & Hm & _). rewrite E in Hm. discriminate Hm.
  Qed.

  Lemma tk_UsOK : UsOK A -> (forall c, 0 <= c < 48 -> a_ctx A' (KUsage c) = a_ctx A (KUsage c)) -> UsOK A'.
  Proof. intros HU HC c Hc. rewrite (HC c Hc), tk_usage. exact (HU c Hc). Qed.

  Lemma tk_AvOK : AvOK A -> a_ctx A' KAmc = a_ctx A KAmc -> AvOK A'.
  Proof.
    intros HA HC ma mt Hma Hr. rewrite HC, (tk_areas _ _ _ TK).
    destruct (tk_back _ _ _ TK ma mt Hma) as (mt0 & Hm0 & [-> | (G0 & G1 & _)]).
    - exact (HA ma mt0 Hm0 Hr).
    - exfalso. destruct G1 as (aib & sl & R). rewrite Hr in R. discriminate R.
  Qed.

  Lemma tk_deads : forall D, deads A D -> deads A' D.
  Proof.
    intros D HD x. split.
    - intros (mt & Hx & Hr). apply (proj1 (HD x)).
      destruct (tk_back _ _ _ TK x mt Hx) as (mt0 & Hm0 & [-> | (G0 & G1 & _)]); [exists mt0; auto|].
      exfalso. destruct G1 as (aib & sl & R). rewrite Hr in R. discriminate R.
    - intros Hin. destruct (proj2 (HD x) Hin) as (mt & Hx & Hr). exists mt. split; [| exact Hr].
      apply (tk_nongrp _ _ _ TK x mt Hx). intros (aib & sl & R). rewrite Hr in R. discriminate R.
  Qed.

  Lemma tk_spare : a_ctx A' KAmc = a_ctx A KAmc -> spare A' = spare A.
  Proof. intros HC. unfold spare. rewrite HC, (tk_fl _ _ _ TK). reflexivity. Qed.
End TkeepFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dll_transfer : forall (A A' : astate) l, dll A l ->
  (forall y mt, In y l -> a_meta A y = Some mt ->
     exists mt', a_meta A' y = Some mt' /\ mt_next mt' = mt_next mt /\ mt_prev mt' = mt_prev mt) ->
  dll A' l.
Proof.
  intros A A' l Hd Hk k x Hk'. destruct (Hd k x Hk') as (mt & Hx & Hn & Hp).
  destruct (Hk x mt (nth_error_In _ _ Hk') Hx) as (mt' & Hx' & En & Ep). exists mt'. rewrite En, Ep. auto.
Qed.

Definition PN : Z -> option Z := fun _ => None.

Lemma relink_PN : forall x mt, MallocInv_wf3.relink PN PN x mt = mt.
Proof.
  intros x mt. unfold MallocInv_wf3.relink. apply meta_ext; [reflexivity|]. intros fl. rewrite mt_f_MT. destruct fl; reflexivity.
Qed.

Lemma hd_app_single : forall (rest : list Z) h, hd 0 (rest ++ [h]) = nth (1 mod length (h :: rest)) (h :: rest) 0.
Proof.
  intros rest h. destruct rest as [|r rest']; [reflexivity|].
  cbn [length]. rewrite Nat.mod_small by (cbn; llia). reflexivity.
Qed.

Section Rotate.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (sc h : Z) (rest : list Z) (mth : meta_rec).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A sc = h :: rest.
  Hypothesis Hh : a_meta A h = Some mth.
  Hypothesis Hav0 : mt_avail mth = 0.
  Hypothesis Hfr0 : mt_freed mth <> 0.

  Definition rot_act : Z -> list Z := fun c => if Z.eq_dec c sc then rest ++ [h] else a_active A c.
  Definition rotA : astate := MallocInv_wf3.A' A PN PN rot_act (a_freelist A) None.

  Lemma rotA_meta : forall x, a_meta rotA x = a_meta A x.
  Proof.
    intros x. unfold rotA, MallocInv_wf3.A', MallocInv_wf3.g'. cbn.
    destruct (a_meta A x) as [mt|]; [cbn; rewrite relink_PN|]; reflexivity.
  Qed.

  Lemma rotA_active : forall c, a_active rotA c = rot_act c.
  Proof. reflexivity. Qed.
  Lemma rotA_active_sc : a_active rotA sc = rest ++ [h].
  Proof. unfold rotA, MallocInv_wf3.A', rot_act. cbn. destruct (Z.eq_dec sc sc); [reflexivity | contradiction]. Qed.
  Lemma rotA_active_other : forall c, c <> sc -> a_active rotA c = a_active A c.
  Proof. intros c Hc. unfold rotA, MallocInv_wf3.A', rot_act. cbn. destruct (Z.eq_dec c sc); [contradiction | reflexivity]. Qed.

  Lemma rot_next : mt_next mth = hd 0 (rest ++ [h]).
  Proof.
    pose proof (wf_act_dll A HW sc Hsc) as Hd. rewrite Hact in Hd.
    destruct (Hd 0%nat h eq_refl) as (mt & Hm & Hn & Hp). rewrite Hh in Hm. injection Hm as <-.
    rewrite Hn. symmetry. apply hd_app_single.
  Qed.

  Lemma rotA_ctx : forall k, a_ctx rotA k =
    match k with KActive c => if Z.eq_dec c sc then mt_next mth else hd 0 (a_active A c) | _ => a_ctx A k end.
  Proof.
    intros k. unfold rotA, MallocInv_wf3.A', MallocInv_wf3.c', rot_act. cbn.
    destruct k; try reflexivity.
    - symmetry. apply (wf_fl_head A HW).
    - destruct (Z.eq_dec i sc); [rewrite rot_next; reflexivity | reflexivity].
  Qed.

  Lemma rotA_ctx_valid : forall k, cvalid k -> a_ctx rotA k = if cslot_eq_dec k (KActive sc) then mt_next mth else a_ctx A k.
  Proof.
    intros k Hk. rewrite rotA_ctx. destruct k; try reflexivity.
    destruct (Z.eq_dec i sc) as [-> | Hne].
    - destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
    - destruct (cslot_eq_dec (KActive i) (KActive sc)) as [E | _]; [injection E; llia|]. symmetry. apply (wf_act_head A HW). exact Hk.
  Qed.

  Lemma h_notin_rest : ~ In h rest.
  Proof. intros Hin. pose proof (proj1 (NoDup_ListNoDup _) (wf_act_nodup A HW sc)) as ND. rewrite Hact in ND. apply List.NoDup_cons_iff in ND. destruct ND as [H1 _]. exact (H1 Hin). Qed.

  Theorem WF_rotA : WF rotA.
  Proof.
    assert (MEM : forall x, In x (rest ++ [h]) <-> In x (h :: rest)).
    { intros x. rewrite in_app_iff. cbn. tauto. }
    apply WF_relists; try exact HW.
    - exact I.
    - exact (wf_fl_nodup A HW).
    - intros x. rewrite (wf_fl_mem A HW x). unfold MallocInv_wf3.g'. destruct (a_meta A x) as [mt|]; cbn; rewrite ?relink_PN; [tauto|].
      split; intros (mt & Hm & _); discriminate Hm.
    - apply (dll_transfer A rotA _ (wf_fl_dll A HW)). intros y mt _ Hy. exists mt. rewrite rotA_meta. auto.
    - intros c. unfold rot_act. destruct (Z.eq_dec c sc) as [-> | Hne]; [| exact (wf_act_nodup A HW c)].
      pose proof (proj1 (NoDup_ListNoDup _) (wf_act_nodup A HW sc)) as ND. rewrite Hact in ND. apply List.NoDup_cons_iff in ND. destruct ND as [ND1 ND2].
      apply (proj2 (NoDup_ListNoDup _)). apply List.NoDup_app; [exact ND2 | constructor; [intros [] | constructor] |].
      intros x Hx [<- | []]. exact (ND1 Hx).
    - intros c Hc. apply (dll_transfer A rotA).
      + unfold rot_act. destruct (Z.eq_dec c sc) as [-> | Hne]; [| exact (wf_act_dll A HW c Hc)].
        apply dll_rotate. rewrite <- Hact. exact (wf_act_dll A HW sc Hsc).
      + intros y mt _ Hy. exists mt. rewrite rotA_meta. auto.
    - intros c x Hin. unfold rot_act in Hin.
      assert (Hin' : In x (a_active A c)).
      { destruct (Z.eq_dec c sc) as [-> | Hne]; [rewrite Hact; apply MEM; exact Hin | exact Hin]. }
      destruct (wf_act_mem A HW c x Hin') as (mt & aib & sl & Hx & Hr & Hs). exists mt, aib, sl.
      change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x). rewrite rotA_meta. auto.
    - intros x mt aib sl Hx Hr Hnin. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx.
      apply (wf_unlinked A HW x mt aib sl Hx Hr). unfold rot_act in Hnin.
      destruct (Z.eq_dec (mt_sc mt) sc) as [E | Hne]; [| exact Hnin]. rewrite E, Hact. intros Hin. apply Hnin. apply MEM. exact Hin.
    - intros c x mt Hin Hne Hx. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx.
      unfold rot_act in Hin, Hne. destruct (Z.eq_dec c sc) as [-> | Hc]; [| exact (wf_act_nonhead A HW c x mt Hin Hne Hx)].
      apply MEM in Hin. destruct Hin as [<- | Hin].
      + rewrite Hh in Hx. injection Hx as <-. auto.
      + apply (wf_act_nonhead A HW sc x mt); [rewrite Hact; right; exact Hin | | exact Hx].
        rewrite Hact. cbn. intros ->. exact (h_notin_rest Hin).
    - intros x mt aib sl Hx Hr. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx.
      exact (wf_act63 A HW x mt aib sl Hx Hr).
    - intros c x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry.
      change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx.
      change (MallocInv_wf3.g' A PN PN None y) with (a_meta rotA y) in Hy. rewrite rotA_meta in Hy.
      unfold rot_act in Hinx, Hiny.
      assert (Hinx' : In x (a_active A c)) by (destruct (Z.eq_dec c sc) as [-> | Hne]; [rewrite Hact; apply MEM; exact Hinx | exact Hinx]).
      assert (Hiny' : In y (a_active A c)) by (destruct (Z.eq_dec c sc) as [-> | Hne]; [rewrite Hact; apply MEM; exact Hiny | exact Hiny]).
      exact (wf_partial A HW c x mtx aibx slx y mty aiby sly Hinx' Hiny' Hx Hrx Hy Hry).
    - intros x mt Hx Hr. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx. exact (wf_avail_zero A HW x mt Hx Hr).
    - intros x mt Hx Hr. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx. exact (wf_free_zero A HW x mt Hx Hr).
  Qed.

  Lemma tkeep_rotA : tkeep A rotA sc.
  Proof.
    constructor; try reflexivity.
    - intros x mt Hx _. rewrite rotA_meta. exact Hx.
    - intros x mt aib sl Hx Hr. exists mt, aib. rewrite rotA_meta. auto.
    - intros x mt' Hx. rewrite rotA_meta in Hx. exists mt'. auto.
    - exact rotA_active_other.
    - intros k Hk H1 H2. rewrite (rotA_ctx_valid k Hk). destruct (cslot_eq_dec k (KActive sc)); [contradiction | reflexivity].
  Qed.

  Lemma has_rotA : forall f, has rotA f ->
    (has A f /\ (forall x, f_a f <= x < f_a f + f_n f -> ~ (caddr (KActive sc) <= x < caddr (KActive sc) + 8))) \/
    f = FCT (caddr (KActive sc)) 8 (mt_next mth).
  Proof.
    intros f Hf. destruct (MallocInv_wf3.relists_has_inv A PN PN rot_act (a_freelist A) None I f Hf) as [(k & Hk & ->) | Hrest].
    - change (MallocInv_wf3.c' A rot_act (a_freelist A) k) with (a_ctx rotA k). rewrite (rotA_ctx_valid k Hk).
      destruct (cslot_eq_dec k (KActive sc)) as [-> | Hne]; [right; reflexivity | left].
      split; [left; exists k; auto|]. cbn [f_a f_n]. intros x Hx.
      destruct (ctx_slot_disj k (KActive sc) Hk ltac:(exact Hsc) Hne); cbn in *; llia.
    - left.
      assert (Hf0 : has A f).
      { destruct Hrest as [Har | [(x & mt' & fl & Hx & ->) | Hg]].
        - right; left. exact Har.
        - right; right; left. exists x, mt', fl. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx. auto.
        - right; right; right. exact Hg. }
      split; [exact Hf0|].
      assert (Hnc : has_area A f \/ has_meta A f \/ has_grp A f).
      { destruct Hrest as [Har | [(x & mt' & fl & Hx & ->) | Hg]]; [left; exact Har | right; left | right; right; exact Hg].
        exists x, mt', fl. change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x) in Hx. rewrite rotA_meta in Hx. auto. }
      intros x Hx. destruct (nonctx_fact_avoids_ctx A HW f Hnc (KActive sc) ltac:(exact Hsc)); cbn in *; llia.
  Qed.

  Lemma has_rotA_intro : forall f, has A f -> f <> FCT (caddr (KActive sc)) 8 (a_ctx A (KActive sc)) -> has rotA f.
  Proof.
    intros f Hf Hne. destruct Hf as [(k & Hk & ->) | [Har | [Hm | Hg]]].
    - replace (a_ctx A k) with (a_ctx rotA k); [apply (MallocInv_wf3.relists_has_ctx A PN PN rot_act (a_freelist A) None k Hk)|].
      rewrite (rotA_ctx_valid k Hk). destruct (cslot_eq_dec k (KActive sc)) as [-> | _]; [exfalso; apply Hne; reflexivity | reflexivity].
    - apply MallocInv_wf3.relists_has_area. exact Har.
    - destruct Hm as (x & mt & fl & Hx & ->). apply (MallocInv_wf3.relists_has_meta A PN PN rot_act (a_freelist A) None x mt fl).
      change (MallocInv_wf3.g' A PN PN None x) with (a_meta rotA x). rewrite rotA_meta. exact Hx.
    - apply MallocInv_wf3.relists_has_grp_kept; [exact I | exact Hg].
  Qed.

  Lemma has_rotA_new : has rotA (FCT (caddr (KActive sc)) 8 (mt_next mth)).
  Proof.
    replace (mt_next mth) with (a_ctx rotA (KActive sc)).
    - apply (MallocInv_wf3.relists_has_ctx A PN PN rot_act (a_freelist A) None (KActive sc)). exact Hsc.
    - rewrite (rotA_ctx_valid (KActive sc) Hsc). destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
  Qed.

  Lemma dom_rotA : forall x, dom rotA x <-> dom A x.
  Proof. intros x. apply (MallocInv_wf3.dom_relists A PN PN rot_act (a_freelist A) None I). Qed.

  Lemma VMok_rotA : forall hh, VMok A hh -> VMok rotA hh.
  Proof. intros hh HV. apply (MallocInv_wf3.VMok_relists A PN PN rot_act (a_freelist A) None I). exact HV. Qed.
End Rotate.

(* [comment removed for export] *)
Lemma act_member_meta : forall A sc x, WF A -> In x (a_active A sc) ->
  exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt = sc /\
    0x1000 <= x /\ x + 40 <= alloc_ceiling /\ (forall j, 0 <= j < 40 -> dom A (x + j)) /\
    exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ x = meta_addr pg k.
Proof.
  intros A sc x HW Hin. destruct (wf_act_mem A HW sc x Hin) as (mt & aib & sl & Hx & Hr & Hs).
  exists mt, aib, sl. split; [exact Hx|]. split; [exact Hr|]. split; [exact Hs|].
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & Hk & ->).
  destruct (wf_areas_al A HW pg Hpg) as [Hpal Hph]. unfold heap_range in Hph.
  pose proof (meta_addr_range pg k Hk) as Hmr.
  split; [llia|]. split; [llia|]. split.
  - intros j Hj. left. exists pg. split; [exact Hpg | llia].
  - exists pg, k. auto.
Qed.

Section RotateCPS.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (sc h : Z) (rest : list Z) (mth : meta_rec).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A sc = h :: rest.
  Hypothesis Hh : a_meta A h = Some mth.
  Hypothesis Hav0 : mt_avail mth = 0.
  Hypothesis Hfr0 : mt_freed mth <> 0.
  Implicit Types (P : R -> mstate -> Prop).

  Let A1 := rotA A sc h rest.

  Lemma rot_next_range : 0x1000 <= mt_next mth /\ mt_next mth + 40 <= alloc_ceiling.
  Proof.
    pose proof (ii_is HII) as [HW _ _ _ _ _].
    assert (Hin : In (mt_next mth) (a_active A sc)).
    { rewrite (rot_next A HW sc h rest mth Hsc Hact Hh). rewrite Hact.
      assert (M : In (hd 0 (rest ++ [h])) (rest ++ [h])).
      { destruct rest as [|r rest']; cbn; [left; reflexivity | left; reflexivity]. }
      apply in_app_iff in M. cbn in M. cbn. tauto. }
    destruct (act_member_meta A sc _ HW Hin) as (mt & aib & sl & _ & _ & _ & H1 & H2 & _). llia.
  Qed.

  Theorem ts_rotate : forall (K : unit -> M R) P,
    (forall s', II sp0 argv envp cb D A1 s' -> FR A s A1 s' -> ms_vm s' = ms_vm s ->
       tsafe (K tt s') P) ->
    tsafe ((x <- m_sd (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 (mt_next mth)) ;; K x) s) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof rot_next_range as [N1 N2]. ceil.
    pose proof (ctx_slot_range (KActive sc) Hsc) as (C1 & C2 & C3). unfold LOCKA, CTX_END in C1, C2, C3. cbn [clen] in C2, C3.
    unfold m_sd. eapply (ts_st_ctxw A s (ms_mem s) [] (KActive sc)); [apply repw_init; [exact HW | exact HR] | exact HWIN | exact Hsc |].
    pose proof (repw_st_ctx A s (ms_mem s) [] (KActive sc) (Z_to_bv 64 (mt_next mth)) (repw_init A _ HW HR) Hsc) as RW1.
    set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (caddr (KActive sc))) (word_to_le_bytes (Z.to_nat (clen (KActive sc))) (Z_to_bv 64 (mt_next mth)))) in RW1 |- *.
    pose proof (WF_rotA A HW sc h rest mth Hsc Hact Hh Hav0 Hfr0) as HW1.
    pose proof (tkeep_rotA A HW sc h rest mth Hsc Hact Hh) as TK.
    assert (HR1 : Rep A1 m1).
    { apply (repw_commit A A1 (ms_mem s) _ m1 RW1).
      - intros x b (f & Hf & Hfb). destruct (has_rotA A HW sc h rest mth Hsc Hact Hh f Hf) as [(Hf0 & Hdis) | ->].
        + left. exists f. auto.
        + right. destruct Hfb as [Hx ->]. cbn [f_a f_n] in Hx. rewrite wlook_hit by (cbn [f_a f_n clen]; llia). discriminate.
      - intros x b (f & Hf & Hfb) Hw. destruct (has_rotA A HW sc h rest mth Hsc Hact Hh f Hf) as [(Hf0 & Hdis) | ->].
        + exfalso. apply Hw. destruct Hfb as [Hx _]. cbn [wlook]. replace (wcov _ x) with false; [reflexivity|].
          symmetry. apply Bool.not_true_iff_false. intros Hc. apply wcov_spec in Hc. cbn [f_a f_n clen] in Hc. exact (Hdis x Hx Hc).
        + destruct Hfb as [Hx ->]. cbn [f_a f_n f_v] in Hx |- *. rewrite wlook_hit by (cbn [f_a f_n clen]; llia). cbn [f_a f_v].
          rewrite uZ by llia. reflexivity.
      - intros x Hx. apply (proj1 (dom_rotA A sc h rest x)). exact Hx. }
    apply HK.
    - constructor.
      + apply (IS_wbytes sp0 argv envp cb A A1 s _ _ HI HW1 HR1); rewrite ?length_N_to_le_bytes; cbn [clen]; change (Z.of_nat (Z.to_nat 8)) with 8; try llia.
        intros x Hx. unfold mzone, CTX, CTX_END. right; right; right. llia.
      + cbn [ms_vm upd]. apply (VMok_rotA A sc h rest). exact (ii_vm HII).
      + apply (tk_AvOK A A1 sc TK (ii_av HII)). apply (tk_ctx _ _ _ TK); [exact I | discriminate | discriminate].
      + apply (tk_UsOK A A1 sc TK (ii_us HII)). intros c Hc. apply (tk_ctx _ _ _ TK); [exact Hc | discriminate | discriminate].
      + apply (tk_deads A A1 sc TK). exact (ii_dd HII).
    - apply (FR_memA A A1 s m1 HW).
      + intros x. apply (dom_rotA A sc h rest).
      + reflexivity.
      + assert (Hlen : Z.of_nat (length (word_to_le_bytes (Z.to_nat (clen (KActive sc))) (Z_to_bv 64 (mt_next mth)))) = 8) by (rewrite length_N_to_le_bytes; reflexivity).
        intros a. pose proof (u64_range a).
        destruct (Z.lt_ge_cases (bv_unsigned a) (caddr (KActive sc))) as [Hl|Hl]; [left; unfold m1; rewrite wbytes_other_Z by (rewrite ?Hlen; llia); reflexivity|].
        destruct (Z.lt_ge_cases (bv_unsigned a) (caddr (KActive sc) + 8)) as [Hi|Hi]; [right; left; unfold LOCKA, CTX_END; llia|].
        left; unfold m1; rewrite wbytes_other_Z by (rewrite ?Hlen; llia); reflexivity.
      + assert (Hlen : Z.of_nat (length (word_to_le_bytes (Z.to_nat (clen (KActive sc))) (Z_to_bv 64 (mt_next mth)))) = 8) by (rewrite length_N_to_le_bytes; reflexivity).
        intros a Ha. unfold m1. apply wbytes_keeps; [rewrite uZ by llia; llia | exact Ha].
    - reflexivity.
  Qed.
End RotateCPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition links_only (A A' : astate) : Prop :=
  forall x mt, a_meta A x = Some mt ->
    exists mt', a_meta A' x = Some mt' /\ mt_role mt' = mt_role mt /\
      forall fl, fl <> FPrev -> fl <> FNext -> mt_f mt' fl = mt_f mt fl.

Lemma links_only_refl : forall A, links_only A A.
Proof. intros A x mt Hx. exists mt. auto. Qed.

Lemma metas_apart : forall A x mtx y mty, WF A -> a_meta A x = Some mtx -> a_meta A y = Some mty -> x <> y ->
  x + 40 <= y \/ y + 40 <= x.
Proof.
  intros A x mtx y mty HW Hx Hy Hne.
  destruct (other_meta_avoid_meta A HW x mtx Hx y mty FPrev Hy ltac:(congruence)) as [H | H]; cbn in H; [right | left]; try llia.
  destruct (other_meta_avoid_meta A HW y mty Hy x mtx FPrev Hx Hne) as [H' | H']; cbn in H'; llia.
Qed.

Lemma meta_img : forall A x mtx, WF A -> a_meta A x = Some mtx -> x + 40 <= IMG_LO \/ IMG_HI <= x.
Proof.
  intros A x mtx HW Hx.
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & Hk & ->).
  destruct (wf_areas_al A HW pg Hpg) as [_ Hph]. unfold heap_range in Hph. pose proof (meta_addr_range pg k Hk). llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Dequeue.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (sc g : Z) (l1 l2 : list Z).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A sc = l1 ++ g :: l2.

  Let l := l1 ++ g :: l2.
  Let n := length l.
  Let i := length l1.
  Let xn := nth (S i mod n) l 0.
  Let xp := nth ((i + n - 1) mod n)%nat l 0.

  Definition deqP : Z -> option Z := fun x => if x =? g then Some 0 else if x =? xn then Some xp else None.
  Definition deqN : Z -> option Z := fun x => if x =? g then Some 0 else if x =? xp then Some xn else None.
  Definition deq_act : Z -> list Z := fun c => if Z.eq_dec c sc then l1 ++ l2 else a_active A c.
  Definition deqA : astate := MallocInv_wf3.A' A deqP deqN deq_act (a_freelist A) None.

  Lemma dq_mem : forall x, In x l -> exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt = sc /\
    0x1000 <= x /\ x + 40 <= alloc_ceiling /\ (forall j, 0 <= j < 40 -> dom A (x + j)) /\
    exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ x = meta_addr pg k.
  Proof. intros x Hx. apply (act_member_meta A sc x HW). rewrite Hact. exact Hx. Qed.

  Lemma g_in : In g l. Proof. unfold l. apply in_app_iff. right. left. reflexivity. Qed.
  Lemma i_lt_n : (i < n)%nat. Proof. unfold i, n, l. rewrite length_app. cbn. llia. Qed.
  Lemma xn_in : In xn l.
  Proof. unfold xn. apply nth_In. apply Nat.mod_upper_bound. pose proof i_lt_n. llia. Qed.
  Lemma xp_in : In xp l.
  Proof. unfold xp. apply nth_In. apply Nat.mod_upper_bound. pose proof i_lt_n. llia. Qed.
  Lemma sub_in : forall x, In x (l1 ++ l2) -> In x l.
  Proof. intros x Hx. unfold l. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [H|H]; [left; exact H | right; right; exact H]. Qed.

  Lemma dq_nodup : List.NoDup l.
  Proof. apply (proj1 (NoDup_ListNoDup _)). unfold l. rewrite <- Hact. exact (wf_act_nodup A HW sc). Qed.
  Lemma dq_g_notin : ~ In g (l1 ++ l2).
  Proof. apply List.NoDup_remove_2. exact dq_nodup. Qed.
  Lemma dq_nodup_sub : List.NoDup (l1 ++ l2).
  Proof. apply (List.NoDup_remove_1 _ _ g). exact dq_nodup. Qed.

  Lemma nth_error_g : nth_error l i = Some g.
  Proof. unfold l, i. rewrite nth_error_app_r by llia. rewrite Nat.sub_diag. reflexivity. Qed.

  Lemma g_links : exists mtg aib sl, a_meta A g = Some mtg /\ mt_role mtg = RGroup aib sl /\ mt_sc mtg = sc /\
    mt_next mtg = xn /\ mt_prev mtg = xp.
  Proof.
    destruct (dq_mem g g_in) as (mt & aib & sl & Hm & Hr & Hs & _).
    pose proof (wf_act_dll A HW sc Hsc) as Hd. rewrite Hact in Hd. destruct (Hd i g nth_error_g) as (mt' & Hm' & Hn & Hp).
    rewrite Hm in Hm'. injection Hm' as <-. exists mt, aib, sl. repeat split; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_l : hd 0 l = match l1 with [] => g | a :: _ => a end.
  Proof. unfold l. destruct l1; reflexivity. Qed.

  Lemma nonhead_kept : forall x, In x (l1 ++ l2) -> x <> hd 0 (l1 ++ l2) -> x <> hd 0 l.
  Proof.
    intros x Hx Hne. rewrite hd_l. pose proof dq_g_notin as NG. destruct l1 as [|a l1'].
    - intros ->. exact (NG Hx).
    - exact Hne.
  Qed.

  Lemma single_links : l1 ++ l2 = [] -> xn = g /\ xp = g.
  Proof.
    intros Er. destruct l1; [| discriminate Er]. destruct l2; [| discriminate Er].
    unfold xn, xp, i, n, l. cbn. auto.
  Qed.

  Lemma multi_links : l1 ++ l2 <> [] -> In xn (l1 ++ l2) /\ In xp (l1 ++ l2) /\ xn <> g /\ xp <> g /\ (2 <= n)%nat.
  Proof.
    intros Er.
    assert (Hn2 : (2 <= n)%nat).
    { unfold n, l. rewrite length_app. cbn. destruct l1; [destruct l2; [exfalso; exact (Er eq_refl)|]|]; cbn; llia. }
    pose proof i_lt_n as Hin. pose proof dq_nodup as ND.
    assert (INJ : forall a b, (a < n)%nat -> (b < n)%nat -> nth a l 0 = nth b l 0 -> a = b).
    { intros a b Ha Hb E. apply (proj1 (NoDup_nth l 0) ND a b Ha Hb E). }
    assert (Hg : nth i l 0 = g) by (apply nth_error_nth; exact nth_error_g).
    assert (Hxn_ne : xn <> g).
    { unfold xn. intros E. rewrite <- Hg in E. apply INJ in E; [| apply Nat.mod_upper_bound; llia | llia].
      destruct (Nat.eq_dec (S i) n) as [En | En].
      - rewrite En, Nat.Div0.mod_same in E. llia.
      - rewrite Nat.mod_small in E by llia. llia. }
    assert (Hxp_ne : xp <> g).
    { unfold xp. intros E. rewrite <- Hg in E. apply INJ in E; [| apply Nat.mod_upper_bound; llia | llia].
      destruct (Nat.eq_dec i 0) as [E0 | E0].
      - rewrite E0 in E. rewrite Nat.add_0_l, Nat.mod_small in E by llia. llia.
      - replace (i + n - 1)%nat with ((i - 1) + 1 * n)%nat in E by llia. rewrite Nat.Div0.mod_add, Nat.mod_small in E by llia. llia. }
    assert (MEM : forall x, In x l -> x <> g -> In x (l1 ++ l2)).
    { intros x Hx Hxg. unfold l in Hx. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [H | [H | H]]; [left; exact H | exfalso; exact (Hxg (eq_sym H)) | right; exact H]. }
    split; [apply MEM; [exact xn_in | exact Hxn_ne]|]. split; [apply MEM; [exact xp_in | exact Hxp_ne]|]. auto.
  Qed.

  Lemma hd_sub : l1 ++ l2 <> [] -> hd 0 (l1 ++ l2) = match l1 with [] => xn | a :: _ => a end.
  Proof.
    intros Er. destruct l1 as [|a l1']; [| reflexivity].
    destruct l2 as [|b l2']; [exfalso; exact (Er eq_refl)|].
    unfold xn, i, n, l. cbn [app length hd]. rewrite Nat.mod_small by llia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma relink_other : forall x mt, x <> g -> x <> xn -> x <> xp ->
    MallocInv_wf3.relink deqP deqN x mt = mt.
  Proof.
    intros x mt H1 H2 H3. unfold MallocInv_wf3.relink, deqP, deqN.
    rewrite (proj2 (Z.eqb_neq x g) H1), (proj2 (Z.eqb_neq x xn) H2), (proj2 (Z.eqb_neq x xp) H3).
    apply meta_ext; [reflexivity|]. intros fl. rewrite mt_f_MT. destruct fl; reflexivity.
  Qed.

  Lemma relink_nonmember : forall x mt, a_meta A x = Some mt -> ~ In x l -> MallocInv_wf3.relink deqP deqN x mt = mt.
  Proof.
    intros x mt Hx Hnin. apply relink_other; intros ->; [exact (Hnin g_in) | exact (Hnin xn_in) | exact (Hnin xp_in)].
  Qed.

  Lemma relink_nongroup : forall x mt, a_meta A x = Some mt -> ~ is_group mt -> MallocInv_wf3.relink deqP deqN x mt = mt.
  Proof.
    intros x mt Hx Hng. apply (relink_nonmember x mt Hx). intros Hin.
    destruct (dq_mem x Hin) as (mt' & aib & sl & Hx' & Hr' & _). rewrite Hx in Hx'. injection Hx' as <-. apply Hng. exists aib, sl. exact Hr'.
  Qed.

  Lemma relink_otherclass : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl -> mt_sc mt <> sc ->
    MallocInv_wf3.relink deqP deqN x mt = mt.
  Proof.
    intros x mt aib sl Hx Hr Hs. apply (relink_nonmember x mt Hx). intros Hin.
    destruct (dq_mem x Hin) as (mt' & aib' & sl' & Hx' & Hr' & Hs' & _). rewrite Hx in Hx'. injection Hx' as <-. exact (Hs Hs').
  Qed.

  Lemma deqA_meta : forall x, a_meta deqA x = option_map (MallocInv_wf3.relink deqP deqN x) (a_meta A x).
  Proof. reflexivity. Qed.

  Lemma deqA_meta_inv : forall x mt', a_meta deqA x = Some mt' -> exists mt, a_meta A x = Some mt /\ mt' = MallocInv_wf3.relink deqP deqN x mt.
  Proof.
    intros x mt' Hx. rewrite deqA_meta in Hx. destruct (a_meta A x) as [mt|]; [| discriminate Hx]. cbn in Hx. injection Hx as <-. exists mt. auto.
  Qed.

  Lemma deqA_active_sc : a_active deqA sc = l1 ++ l2.
  Proof. unfold deqA, MallocInv_wf3.A', deq_act. cbn. destruct (Z.eq_dec sc sc); [reflexivity | contradiction]. Qed.
  Lemma deqA_active_other : forall c, c <> sc -> a_active deqA c = a_active A c.
  Proof. intros c Hc. unfold deqA, MallocInv_wf3.A', deq_act. cbn. destruct (Z.eq_dec c sc); [contradiction | reflexivity]. Qed.

  Lemma deqA_ctx_valid : forall k, cvalid k -> a_ctx deqA k = if cslot_eq_dec k (KActive sc) then hd 0 (l1 ++ l2) else a_ctx A k.
  Proof.
    intros k Hk. unfold deqA, MallocInv_wf3.A', MallocInv_wf3.c', deq_act. cbn.
    destruct k; try reflexivity.
    - symmetry. apply (wf_fl_head A HW).
    - destruct (Z.eq_dec i0 sc) as [-> | Hne].
      + destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
      + destruct (cslot_eq_dec (KActive i0) (KActive sc)) as [E | _]; [injection E; llia|]. symmetry. apply (wf_act_head A HW). exact Hk.
  Qed.

  Theorem WF_deqA : WF deqA.
  Proof.
    destruct g_links as (mtg & aibg & slg & Hm & Hrm & Hsm & Hnx & Hpv).
    assert (RESTM : forall x, In x (l1 ++ l2) -> x <> g /\ In x l).
    { intros x Hx. split; [intros ->; exact (dq_g_notin Hx) | exact (sub_in x Hx)]. }
    assert (GONLY : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
              MallocInv_wf3.g' A deqP deqN None x = Some (MallocInv_wf3.relink deqP deqN x mt)).
    { intros x mt aib sl Hx Hr. change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x). rewrite deqA_meta, Hx. reflexivity. }
    apply WF_relists; try exact HW.
    - exact I.
    - exact (wf_fl_nodup A HW).
    - intros x. rewrite (wf_fl_mem A HW x). change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x). rewrite deqA_meta.
      destruct (a_meta A x) as [mt|]; cbn; [| split; intros (mt & Hmt & _); discriminate Hmt].
      split; intros (mt' & E & Hr); [injection E as <-; eexists; split; [reflexivity | exact Hr]|].
      injection E as <-. exists mt. cbn in Hr. auto.
    - apply (dll_transfer A deqA _ (wf_fl_dll A HW)). intros y mt Hin Hy.
      destruct (proj1 (wf_fl_mem A HW y) Hin) as (mt' & Hy' & Hr'). rewrite Hy in Hy'. injection Hy' as <-.
      exists mt. rewrite deqA_meta, Hy. cbn. rewrite (relink_nongroup y mt Hy) by (intros (aib & sl & R); rewrite Hr' in R; discriminate R). auto.
    - intros c. unfold deq_act. destruct (Z.eq_dec c sc) as [-> | Hne]; [| exact (wf_act_nodup A HW c)].
      apply (proj2 (NoDup_ListNoDup _)). exact dq_nodup_sub.
    - intros c Hc. unfold deq_act. destruct (Z.eq_dec c sc) as [-> | Hne].
      + destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []) as [Er | Er]; [rewrite Er; intros k x Hk; destruct k; discriminate Hk|].
        pose proof (dll_remove A deqA l1 g l2) as DR. apply DR.
        * exact dq_nodup.
        * exact Er.
        * pose proof (wf_act_dll A HW sc Hsc) as X. rewrite Hact in X. exact X.
        * intros k y mty Hk Hy. pose proof (nth_error_In _ _ Hk) as Hin. destruct (RESTM y Hin) as (Hne & _).
          exists (MallocInv_wf3.relink deqP deqN y mty). rewrite deqA_meta, Hy. split; [reflexivity|].
          unfold MallocInv_wf3.relink, deqP, deqN, mt_next, mt_prev. cbn [mt_f].
          rewrite (proj2 (Z.eqb_neq y g) Hne).
          fold l. fold n. fold i. fold xn. fold xp.
          split; [destruct (y =? xp); reflexivity | destruct (y =? xn); reflexivity].
      + apply (dll_transfer A deqA (a_active A c) (wf_act_dll A HW c Hc)).
        intros y mty Hin Hy. destruct (wf_act_mem A HW c y Hin) as (mt0 & aib & sl & Hy0 & Hr0 & Hs0). rewrite Hy in Hy0. injection Hy0 as <-.
        exists mty. rewrite deqA_meta, Hy. cbn. rewrite (relink_otherclass y mty aib sl Hy Hr0) by llia. auto.
    - intros c x Hin. unfold deq_act in Hin.
      assert (Hin' : In x (a_active A c)).
      { destruct (Z.eq_dec c sc) as [-> | Hne]; [rewrite Hact; exact (sub_in x Hin) | exact Hin]. }
      destruct (wf_act_mem A HW c x Hin') as (mt & aib & sl & Hx & Hr & Hs). exists (MallocInv_wf3.relink deqP deqN x mt), aib, sl.
      rewrite (GONLY x mt aib sl Hx Hr). cbn. auto.
    - intros x mt' aib sl Hx Hr' Hnin. change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x) in Hx.
      destruct (deqA_meta_inv x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      replace (mt_sc (MallocInv_wf3.relink deqP deqN x mt)) with (mt_sc mt) in Hnin by reflexivity.
      destruct (Z.eq_dec x g) as [-> | Hneg].
      + unfold MallocInv_wf3.relink, deqP, deqN, mt_prev, mt_next. cbn [mt_f]. rewrite Z.eqb_refl. cbn. auto.
      + assert (Hnin0 : ~ In x l).
        { intros Hinl.
          destruct (dq_mem x Hinl) as (mt0 & aib0 & sl0 & Hx1 & Hr1 & Hs1 & _). rewrite Hx0 in Hx1. injection Hx1 as <-.
          apply Hnin. unfold deq_act. rewrite Hs1. destruct (Z.eq_dec sc sc); [| contradiction].
          unfold l in Hinl. apply in_app_iff in Hinl. apply in_app_iff. destruct Hinl as [H | [H | H]]; [left; exact H | exfalso; exact (Hneg (eq_sym H)) | right; exact H]. }
        rewrite (relink_nonmember x mt Hx0 Hnin0) in *. apply (wf_unlinked A HW x mt aib sl Hx0 Hr').
        intros Hin. apply Hnin. unfold deq_act. destruct (Z.eq_dec (mt_sc mt) sc) as [E | Hne]; [| exact Hin].
        exfalso. apply Hnin0. unfold l. rewrite <- Hact, <- E. exact Hin.
    - intros c x mt' Hin Hne Hx. change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x) in Hx.
      destruct (deqA_meta_inv x mt' Hx) as (mt & Hx0 & ->). unfold mt_avail, mt_freed. cbn [MallocInv_wf3.relink mt_f].
      unfold deq_act in Hin, Hne. destruct (Z.eq_dec c sc) as [-> | Hc]; [| exact (wf_act_nonhead A HW c x mt Hin Hne Hx0)].
      apply (wf_act_nonhead A HW sc x mt); [rewrite Hact; exact (sub_in x Hin) | rewrite Hact; exact (nonhead_kept x Hin Hne) | exact Hx0].
    - intros x mt' aib sl Hx Hr' H63. change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x) in Hx.
      destruct (deqA_meta_inv x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      replace (mt_sc (MallocInv_wf3.relink deqP deqN x mt)) with (mt_sc mt) in H63 by reflexivity.
      rewrite (relink_otherclass x mt aib sl Hx0 Hr') by llia. exact (wf_act63 A HW x mt aib sl Hx0 Hr' H63).
    - intros c x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry.
      destruct (MallocInv_wf3.g'_group A deqP deqN None I x mtx aibx slx Hx Hrx) as (mx0 & Hmx0 & Hrx0 & ->).
      destruct (MallocInv_wf3.g'_group A deqP deqN None I y mty aiby sly Hy Hry) as (my0 & Hmy0 & Hry0 & ->).
      cbn [MallocInv_wf3.relink mt_last mt_w32 mt_f]. unfold deq_act in Hinx, Hiny.
      assert (Hinx' : In x (a_active A c)) by (destruct (Z.eq_dec c sc) as [-> | Hne]; [rewrite Hact; exact (sub_in x Hinx) | exact Hinx]).
      assert (Hiny' : In y (a_active A c)) by (destruct (Z.eq_dec c sc) as [-> | Hne]; [rewrite Hact; exact (sub_in y Hiny) | exact Hiny]).
      exact (wf_partial A HW c x mx0 aibx slx y my0 aiby sly Hinx' Hiny' Hmx0 Hrx0 Hmy0 Hry0).
    - intros x mt' Hx Hr'. change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x) in Hx.
      destruct (deqA_meta_inv x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      rewrite (relink_nongroup x mt Hx0) by (intros (aib & sl & R); rewrite Hr' in R; discriminate R). exact (wf_avail_zero A HW x mt Hx0 Hr').
    - intros x mt' Hx Hr'. change (MallocInv_wf3.g' A deqP deqN None x) with (a_meta deqA x) in Hx.
      destruct (deqA_meta_inv x mt' Hx) as (mt & Hx0 & ->). cbn in Hr'.
      unfold mt_mem, mt_avail, mt_freed, mt_w32. cbn. exact (wf_free_zero A HW x mt Hx0 Hr').
  Qed.

  Lemma links_only_deqA : links_only A deqA.
  Proof.
    intros x mt Hx. exists (MallocInv_wf3.relink deqP deqN x mt). rewrite deqA_meta, Hx. split; [reflexivity|]. split; [reflexivity|].
    intros fl H1 H2. destruct fl; cbn; try reflexivity; contradiction.
  Qed.

  Lemma tkeep_deqA : tkeep A deqA sc.
  Proof.
    constructor; try reflexivity.
    - intros x mt Hx Hng. rewrite deqA_meta, Hx. cbn. rewrite (relink_nongroup x mt Hx Hng). reflexivity.
    - intros x mt aib sl Hx Hr. exists (MallocInv_wf3.relink deqP deqN x mt), aib. rewrite deqA_meta, Hx. cbn. auto.
    - intros x mt' Hx. destruct (deqA_meta_inv x mt' Hx) as (mt & Hx0 & ->). exists mt. split; [exact Hx0|].
      destruct (mt_role mt) as [| | |aib sl] eqn:Er.
      1-3: left; apply (relink_nongroup x mt Hx0); intros (aib & sl & R); rewrite Er in R; discriminate R.
      right. split; [exists aib, sl; exact Er|]. split; [exists aib, sl; cbn; exact Er|]. split; [reflexivity|]. split; [reflexivity|].
      intros aib0 sl0 aib' sl' R0 R'. cbn in R'. rewrite Er in R'. injection R0 as E1 E2. injection R' as E3 E4. congruence.
    - exact deqA_active_other.
    - intros k Hk H1 H2. rewrite (deqA_ctx_valid k Hk). destruct (cslot_eq_dec k (KActive sc)); [contradiction | reflexivity].
  Qed.

  Lemma dom_deqA : forall x, dom deqA x <-> dom A x.
  Proof. intros x. apply (MallocInv_wf3.dom_relists A deqP deqN deq_act (a_freelist A) None I). Qed.

  Lemma VMok_deqA : forall hh, VMok A hh -> VMok deqA hh.
  Proof. intros hh HV. apply (MallocInv_wf3.VMok_relists A deqP deqN deq_act (a_freelist A) None I). exact HV. Qed.
End Dequeue.

(* [comment removed for export] *)

End WithLayout.
