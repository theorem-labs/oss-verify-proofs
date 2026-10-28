(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs RT_state RT_rep RT_init RT_sys_stmt RT_sys_fixed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma Permutation_map_remove : forall l l' a, Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof.
  intros l l' a H. unfold map_remove. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [List.filter].
  - constructor.
  - destruct (negb (bv_eqb (fst x) a)); [constructor|]; exact IH.
  - destruct (negb (bv_eqb (fst x) a)), (negb (bv_eqb (fst y) a)); try constructor; apply Permutation_refl.
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma FOP_filter : forall {X} (R : X -> X -> Prop) f l, ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
  intros X R f l H. induction H as [|x l Hx Hl IH]; cbn [List.filter]; [constructor|].
  destruct (f x); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

Lemma zcount_map_remove : forall (l : list (word * word)) (a : word),
  (length (map_remove l a) + length (List.filter vpos l) <= length l + length (List.filter vpos (map_remove l a)))%nat.
Proof.
  intros l a. unfold map_remove. induction l as [|e l IH]; [cbn; lia|]. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) a)) eqn:Eb; destruct (vpos e) eqn:Ev; cbn [List.filter length]; rewrite ?Ev; cbn [length]; lia.
Qed.

Lemma zbound_map_remove : forall (l : list (word * word)) (a : word),
  Z.of_nat (length l) <= Z.of_nat (length (List.filter vpos l)) + 1 ->
  Z.of_nat (length (map_remove l a)) <= Z.of_nat (length (List.filter vpos (map_remove l a))) + 1.
Proof. intros l a H. pose proof (zcount_map_remove l a) as C. lia. Qed.

Lemma FOP_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
  intros X R Hs l l' H. induction H as [|x l l' Hp IH|x y l|l l' l'' _ IH1 _ IH2]; intros HF.
  - constructor.
  - inversion HF as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl)].
    apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hx). exact (Permutation_in _ (Permutation_sym Hp) Hz).
  - inversion HF as [|? ? Hy Hl]; subst. inversion Hl as [|? ? Hx Hl']; subst.
    inversion Hy as [|? ? Hyx Hyl]; subst.
    constructor; [constructor; [exact (Hs _ _ Hyx)| exact Hx]|]. constructor; [exact Hyl| exact Hl'].
  - exact (IH2 (IH1 HF)).
Qed.

Lemma FOP_In_apart : forall {X} (R : X -> X -> Prop) l x y, ForallOrdPairs R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l x y H. induction H as [|p l Hp Hl IH]; intros Hx Hy Hne; [destruct Hx|].
  destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (proj1 (Forall_forall _ _) Hp y Hy).
  - right. exact (proj1 (Forall_forall _ _) Hp x Hx).
  - exact (IH Hx Hy Hne).
Qed.

Lemma FOP_app_cross : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|p l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  cbn [app] in H. inversion H as [|? ? Hp Hl]; subst. destruct Hx as [<-|Hx].
  - apply (proj1 (Forall_forall _ _) Hp). apply in_or_app. right. exact Hy.
  - exact (IH l2 Hl x y Hx Hy).
Qed.

Lemma iv_apart_sym : forall p q, iv_apart p q -> iv_apart q p.
Proof. intros p q H. unfold iv_apart in *. lia. Qed.

Lemma sum_count_ext_on : forall P Q l,
  (forall p, In p l -> forall x, B p <= x < B p + S p -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. induction l as [|p l IH]; cbn [sum_count]; [reflexivity|].
  rewrite IH by (intros q Hq; apply H; now right). f_equal. unfold iv_count. apply zcount_ext.
  intros x Hx. pose proof (S_range p). rewrite Z2Nat.id in Hx by lia. exact (H p (or_introl eq_refl) x Hx).
Qed.

Lemma sum_count_partition : forall P f l,
  sum_count P l = sum_count P (List.filter f l) + sum_count P (List.filter (fun p => negb (f p)) l).
Proof.
  intros P f l. induction l as [|p l IH]; cbn [List.filter sum_count]; [reflexivity|].
  destruct (f p); cbn [negb sum_count]; rewrite IH; lia.
Qed.

Lemma sum_count_In_ge : forall P l p, In p l -> iv_count P p <= sum_count P l.
Proof.
  intros P l. induction l as [|q l IH]; intros p Hp; [destruct Hp|]. cbn [sum_count].
  pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))). pose proof (sum_count_nonneg P l). unfold iv_count in *.
  destruct Hp as [<-|Hp]; [lia|]. specialize (IH p Hp). unfold iv_count in IH. lia.
Qed.

Lemma eager_munmap_exact : forall mo (a n : word), model_ivs_wf mo ->
  ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo)) -> In (a, n) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  (forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
     covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false) ->
  eager_used (mdl_munmap mo a n) + bv_unsigned n <= eager_used mo.
Proof.
  intros mo a n Hwf Hsep Hin Hpos Hnc. pose proof Hwf as (Wm & Wn & Wl & _). pose proof (u64_range n) as Rn.
  remember (bv_unsigned a) as lo eqn:Elo. remember (lo + bv_unsigned n) as hi eqn:Ehi.
  assert (Hlh : lo <= hi) by lia.
  assert (Wr : ivs_wf (map_remove (vm_maps (m_vmmaps mo)) a)) by (apply ivs_wf_filter; exact Wm).
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_munmap mo a n)))) by (rewrite mdl_munmap_vmmaps; exact Wr).
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_munmap_vmmaps, mdl_munmap_lazy.
  cbn [vm_maps vm_noaccess]. rewrite <- Elo, <- Ehi.
  set (l := vm_maps (m_vmmaps mo)) in *.
  set (Q := fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)).

  assert (E1 : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps mo)) lo hi
                                                   ++ maps_subtract (m_vm_lazy mo) lo hi) x)) (map_remove l a)
               = sum_count Q (map_remove l a)).
  { apply sum_count_ext_on. intros p Hp x Hx. apply filter_In in Hp as [Hp Hb]. apply negb_true_iff in Hb.
    assert (Hne : p <> (a, n)) by (intros ->; cbn [fst] in Hb; rewrite bv_eqb_refl in Hb; discriminate).
    destruct (FOP_In_apart _ _ _ _ Hsep Hp Hin Hne) as [D|D]; unfold iv_apart in D; cbn [fst snd] in D;
      unfold B, S in Hx; rewrite <- Elo in D.
    all: assert (Hout : x < lo \/ hi <= x) by lia.
    all: assert (Hr : in_rng lo hi x = false) by (unfold in_rng; apply andb_false_iff;
                                                  destruct Hout; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    all: unfold Q; rewrite !covered_app, (covered_subtract _ lo hi x Wn Hlh), (covered_subtract _ lo hi x Wl Hlh), Hr.
    all: cbn [negb]; rewrite !andb_true_r; reflexivity. }
  rewrite E1. rewrite (sum_count_partition Q (fun p => bv_eqb (fst p) a) l). fold (map_remove l a).
  replace (List.filter (fun p => negb (bv_eqb (fst p) a)) l) with (map_remove l a) by reflexivity.

  assert (Hin' : In (a, n) (List.filter (fun p => bv_eqb (fst p) a) l)) by (apply filter_In; split; [exact Hin| apply bv_eqb_refl]).
  pose proof (sum_count_In_ge Q _ _ Hin') as Hge.
  assert (Hn : iv_count Q (a, n) = bv_unsigned n).
  { unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_true by (intros x Hx; rewrite Z2Nat.id in Hx by lia; unfold Q;
      rewrite (Hnc x ltac:(lia)); reflexivity). apply Z2Nat.id. lia. }
  lia.
Qed.

Lemma lazy_in_maps_munmap' : forall mo (a n : word), model_ivs_wf mo -> lazy_in_maps mo ->
  ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo)) -> In (a, n) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  lazy_in_maps (mdl_munmap mo a n).
Proof.
  intros mo a n (_ & _ & Wl & _) H Hsep Hin Hpos iv Hiv Hsz. rewrite mdl_munmap_lazy in Hiv. rewrite mdl_munmap_vmmaps. cbn [vm_maps].
  destruct (maps_subtract_pieces' _ _ _ iv Wl Hiv) as (r & Hr & P1 & P2 & P3).
  destruct (H r Hr ltac:(lia)) as (e & He & E1 & E2). exists e. split; [|lia].
  unfold map_remove. apply filter_In. split; [exact He|].
  destruct (bv_eqb (fst e) a) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb.
  destruct (FOP_In_apart _ _ _ _ Hsep He Hin) as [D|D].
  - intros ->. cbn [fst snd] in *. lia.
  - unfold iv_apart in D. rewrite Eb in D, E1, E2. cbn [fst snd] in D. lia.
  - unfold iv_apart in D. rewrite Eb in D, E1, E2. cbn [fst snd] in D. lia.
Qed.

Theorem munmap_ok : munmap_node.
Proof.
  intros Σ Σ' PMc Pm K mb len HPMc _ EL Eaw Hsm Hperm' Heg HL Haw Heg38 Hlen Hlal Hmb0 Hal Hend Hm.
  assert (EA : rtA_allow Σ' = rtA_allow Σ) by (unfold rtA_allow; rewrite Eaw, EL; reflexivity).
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite EA.
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  apply (ast_munmap bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
           K (fun mo => ARTM_A Σ' mo /\ PMc mo) mb len).
  - lia.
  - exact Hmb0.
  - unfold page_size. exact Hal.
  - rewrite Hrd. unfold TASK_SIZE. lia.
  - intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4). rewrite Hrd. repeat (split; [assumption|]). exact S4.
  - intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
    rewrite Hrd.
    assert (Eua : bv_unsigned (Z_to_bv 64 mb) = mb) by (apply unsigned_lit; lia).
    assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    assert (HinR : In (Z_to_bv 64 mb, Z_to_bv 64 len) (rt_maps Σ)) by (unfold rt_maps; apply in_or_app; left; exact Hsm).
    assert (Hin : In (Z_to_bv 64 mb, Z_to_bv 64 len) (vm_maps (m_vmmaps mo))) by exact (artm_in_maps Σ mo _ HA HinR).
    assert (HsepR : ForallOrdPairs iv_apart (rt_maps Σ)) by exact (FOP_perm _ iv_apart_sym _ _ Hperm (FOP_filter _ vpos _ Hsep)).

    assert (Hnc : forall x, bv_unsigned (Z_to_bv 64 mb) <= x < bv_unsigned (Z_to_bv 64 mb) + bv_unsigned (Z_to_bv 64 len) ->
                  covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false).
    { intros x Hx. destruct (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x) eqn:Hc; [|reflexivity].
      exfalso. pose proof (Hcf x Hc) as H0. unfold covered in H0. apply existsb_exists in H0 as (q & Hq & Hqx).
      unfold rt_maps in HsepR. pose proof (FOP_app_cross _ _ _ HsepR _ q Hsm Hq) as D.
      unfold in_iv, in_rng, B, S in Hqx. apply andb_prop in Hqx as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
      unfold iv_apart in D. cbn [fst snd] in D. lia. }
    split; [exact Hwf|].
    split.
    { unfold map_has. apply existsb_exists. exists (Z_to_bv 64 mb, Z_to_bv 64 len). split; [exact Hin|].
      cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    split.
    { rewrite overlap_sum_zero; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
      apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq Hb]. apply negb_true_iff in Hb.
      assert (Hne : q <> (Z_to_bv 64 mb, Z_to_bv 64 len)) by (intros ->; cbn [fst] in Hb; rewrite bv_eqb_refl in Hb; discriminate).
      destruct (FOP_In_apart _ _ _ _ Hsep Hq Hin Hne) as [D|D]; unfold iv_apart in D; cbn [fst snd] in D; rewrite Eua, Eul in D;
        unfold B, S; lia. }
    split.
    +
      split.
      { rewrite mdl_munmap_vmmaps. cbn [vm_maps]. rewrite filter_map_remove.
        exact (Permutation_trans (Permutation_map_remove _ _ _ Hperm) (Permutation_sym Hperm')). }
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_reserved]; exact Eres|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_limit]; exact Elim|].
      split.
      { pose proof (eager_munmap_exact mo _ _ Hwf Hsep Hin ltac:(rewrite Eul; lia) Hnc) as Hle. rewrite Eul in Hle. lia. }
      pose proof Hwf as (Wm & Wn & Wl & _).
      split; [apply model_ivs_wf_munmap; exact Hwf|].
      split; [exact (lazy_in_maps_munmap' mo _ _ Hwf Hlz Hsep Hin ltac:(rewrite Eul; lia))|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_maps]; apply FOP_filter; exact Hsep|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
      split.
      { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_munmap_vmmaps, mdl_munmap_lazy in Hz.
        cbn [vm_noaccess] in Hz. rewrite covered_app in Hz |- *. rewrite Eua, Eul in Hz.
        apply orb_true_iff in Hz as [Hz|Hz]; apply orb_true_iff;
          [left; refine (covered_subtract_le _ _ _ _ Wn _ Hz); lia | right; refine (covered_subtract_le _ _ _ _ Wl _ Hz); lia]. }
      split.
      { apply (shadow_lazy_cut_nc mo _ mb (mb + len) Hwf ltac:(lia) Hal ltac:(rewrite Z.add_mod, Hal, Hlal by lia; reflexivity) Hsl).
        - rewrite mdl_munmap_lazy, Eua, Eul. reflexivity.
        - rewrite mdl_munmap_vmmaps. cbn [vm_noaccess]. rewrite Eua, Eul. reflexivity.
        - intros x Hx. pose proof (Hnc x ltac:(rewrite Eua, Eul; lia)) as C. rewrite covered_app in C.
          apply orb_false_iff in C as [_ C]. exact C. }

      split; [unfold maps_zbound; rewrite mdl_munmap_vmmaps; cbn [vm_maps]; exact (zbound_map_remove _ _ Hzb)|].

      apply NodesA_madv.noaccess_pos_munmap; [exact Hwf| exact Hnp].
    + apply (HPMc mo); [apply mdl_munmap_fds| apply mdl_munmap_fs| exact HPc].
Qed.

End GWIN.
