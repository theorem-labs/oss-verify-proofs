(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint remove_nth {A} (j : nat) (l : list A) : list A :=
  match l, j with
  | [], _ => []
  | _ :: r, O => r
  | x :: r, Datatypes.S j' => x :: remove_nth j' r
  end.

Lemma remove_nth_In : forall {A} j (l : list A) x, In x (remove_nth j l) -> In x l.
Proof.
  intros A j l. revert j. induction l as [|y r IH]; intros j x H.
  - destruct j; cbn in H; destruct H.
  - destruct j as [|j]; cbn [remove_nth] in H; [right; exact H|].
    destruct H as [H|H]; [left; exact H | right; exact (IH j x H)].
Qed.

Lemma nomark_remove : forall j gs, nomark gs = true -> nomark (remove_nth j gs) = true.
Proof.
  intros j gs H. unfold nomark in *. rewrite forallb_forall in *. intros g Hg. exact (H g (remove_nth_In j gs g Hg)).
Qed.
Lemma remove_nth_Forall : forall {A} (P : A -> Prop) j l, Forall P l -> Forall P (remove_nth j l).
Proof. intros A P j l H. apply Forall_forall. intros x Hx. rewrite Forall_forall in H. exact (H x (remove_nth_In j l x Hx)). Qed.

Lemma pdisj_remove : forall j l, pdisj l -> pdisj (remove_nth j l).
Proof.
  intros j l. revert j. induction l as [|x r IH]; intros [|j] H; cbn [remove_nth]; try exact H; [exact (proj2 H)|].
  destruct H as [H1 H2]. split; [|exact (IH j H2)]. apply Forall_forall. intros y Hy. rewrite Forall_forall in H1.
  exact (H1 y (remove_nth_In j r y Hy)).
Qed.

Lemma remove_nth_map : forall {A B} (f : A -> B) j l, List.map f (remove_nth j l) = remove_nth j (List.map f l).
Proof. intros A B f j l. revert j. induction l as [|x r IH]; intros [|j]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma filter_neq_base : forall (q : word * word) r, Forall (iv_disj q) r -> 0 < bv_unsigned (snd q) ->
  Forall (fun q' => 0 < bv_unsigned (snd q')) r -> List.filter (fun p => negb (bv_eqb (fst p) (fst q))) r = r.
Proof.
  intros q r Hd Hq Hr. induction r as [|q' r' IH]; [reflexivity|]. inversion Hd as [|? ? Hd' Hd1']; subst.
  inversion Hr as [|? ? Hq' Hr']; subst. cbn [List.filter].
  replace (bv_eqb (fst q') (fst q)) with false.
  - cbn [negb]. f_equal. exact (IH Hd1' Hr').
  - symmetry. unfold bv_eqb. apply Z.eqb_neq. unfold iv_disj, B, S in Hd'. lia.
Qed.

(* [comment removed for export] *)
Lemma map_remove_nth : forall (l : list (word * word)) j p, pdisj l -> Forall (fun q => 0 < bv_unsigned (snd q)) l ->
  nth_error l j = Some p -> map_remove l (fst p) = remove_nth j l.
Proof.
  intros l. induction l as [|q r IH]; intros j p Hd Hpos Hj; [destruct j; cbn in Hj; discriminate|].
  inversion Hpos as [|? ? Hq Hr]; subst. destruct Hd as [Hd1 Hd2].
  unfold map_remove. cbn [List.filter]. destruct j as [|j]; cbn [nth_error remove_nth] in Hj |- *.
  - injection Hj as <-. rewrite bv_eqb_refl. cbn [negb]. exact (filter_neq_base q r Hd1 Hq Hr).
  - replace (bv_eqb (fst q) (fst p)) with false.
    + cbn [negb]. f_equal. exact (IH j p Hd2 Hr Hj).
    + symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Forall_forall in Hd1. pose proof (Hd1 p (nth_error_In _ _ Hj)) as Hdp.
      rewrite Forall_forall in Hr. pose proof (Hr p (nth_error_In _ _ Hj)) as Hpp. unfold iv_disj, B, S in Hdp. lia.
Qed.

Lemma nth_remove_In : forall {A} (l : list A) i j q, nth_error l i = Some q -> i <> j -> In q (remove_nth j l).
Proof.
  intros A l. induction l as [|x r IH]; intros i j q Hi Hne; [destruct i; discriminate|].
  destruct i as [|i], j as [|j].
  - lia.
  - injection Hi as <-. left. reflexivity.
  - cbn [nth_error remove_nth] in Hi |- *. exact (nth_error_In _ _ Hi).
  - cbn [nth_error remove_nth] in Hi |- *. right. exact (IH i j q Hi ltac:(lia)).
Qed.

Lemma remove_nth_pos : forall {A} (l : list A) j q, In q (remove_nth j l) -> exists i, i <> j /\ nth_error l i = Some q.
Proof.
  intros A l. induction l as [|x r IH]; intros j q Hq; [destruct j; cbn in Hq; destruct Hq|].
  destruct j as [|j].
  - cbn [remove_nth] in Hq. apply In_nth_error in Hq as (i & Hi). exists (Datatypes.S i). split; [lia | exact Hi].
  - cbn [remove_nth] in Hq. destruct Hq as [<-|Hq]; [exists O; split; [lia | reflexivity]|].
    destruct (IH j q Hq) as (i & Hi & Hn). exists (Datatypes.S i). split; [lia | exact Hn].
Qed.

Definition munmap_post (L : sst) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (lconst 0)) (s_rgs L) (s_facts L) (s_next L) (s_resv L).
Definition munmap_M (M : smodel) (j : nat) : smodel :=
  SM (remove_nth j (sm_maps M)) (sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) [].

Lemma mn_vmmaps : forall a n m, m_vmmaps (munmap_next a n m) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
    (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. intros a n m. destruct m; reflexivity. Qed.
Lemma mn_lazy : forall a n m, m_vm_lazy (munmap_next a n m) = maps_subtract (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. intros a n m. destruct m; reflexivity. Qed.
Lemma mn_mat : forall a n m, m_vm_materialized (munmap_next a n m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros a n m. destruct m; reflexivity. Qed.
Lemma mn_other : forall a n m, let m' := munmap_next a n m in
  m_proc m' = m_proc m /\ m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_lim m' = m_lim m /\ m_time m' = m_time m.
Proof. intros a n m. destruct m; cbn; repeat split; reflexivity. Qed.

Section Unmap.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem munmap_den : forall E L M ms model (j : nat) (g : lin * lin * gkind),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  nth_error (sm_maps M) j = Some g ->
  (forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     ~ (uE E (fst (fst g)) <= w < uE E (fst (fst g)) + gsz E g)) ->
  (forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     ~ (uE E (fst (fst g)) / 8 + SH_OFF <= w < (uE E (fst (fst g)) + gsz E g) / 8 + SH_OFF)) ->
  (forall w, uE E (fst (fst g)) <= w < uE E (fst (fst g)) + gsz E g -> in_zr (sm_zr M) w = false) ->
  eager_sum (s_facts L) (remove_nth j (sm_maps M)) + allow_bound (sm_allow M) <= LIMIT -> sm_own M = [] -> nomark (sm_maps M) = true ->
  DEN segs LIMIT model0 mem0 E (munmap_post L) (munmap_M M j)
      (advance_past_svc (apply_effect (svc_set ms) (mkEffectU (Z_to_bv 64 0) [] [] [(lden E (fst (fst g)), Z_to_bv 64 (gsz E g))] [] [])))
      (munmap_next (lden E (fst (fst g))) (Z_to_bv 64 (gsz E g)) model).
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E L M ms model j g Hd Hj Hsep Hsep8 Hnzr Hbud Hon Hnm.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  den_noblob Hnm.
  assert (Hnm' : nomark (sm_maps (munmap_M M j)) = true) by (cbn [sm_maps munmap_M]; exact (nomark_remove j _ Hnm)).
  set (av := lden E (fst (fst g))) in *. set (u := uE E (fst (fst g))) in *. set (n := gsz E g) in *.
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hgj) as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5). fold n u in Gs1, Gs2, Gs3, Gs4, Gs5.
  assert (Hua : bv_unsigned av = u) by reflexivity.
  assert (HnZw : bv_unsigned (Z_to_bv 64 n) = n) by (apply fg64; unfold two64; lia).
  set (model' := munmap_next av (Z_to_bv 64 n) model).
  set (M' := munmap_M M j).
  set (H := Hof E M model) in *.
  set (H' := Hof E M' model').
  pose proof (u_lt av) as Ra. fold u in Ra.
  assert (HA' : allowA E M' = allowA E M) by reflexivity.
  assert (Hvm' : m_vmmaps model' = _) by exact (mn_vmmaps av (Z_to_bv 64 n) model).
  assert (Hlz' : m_vm_lazy model' = _) by exact (mn_lazy av (Z_to_bv 64 n) model).
  assert (Hmat' : m_vm_materialized model' = _) by exact (mn_mat av (Z_to_bv 64 n) model).
  assert (Hoth' := mn_other av (Z_to_bv 64 n) model). cbv zeta in Hoth'.
  rewrite Hua, HnZw in Hvm', Hlz', Hmat'.
  destruct Hivwf as [Hwna Hwlz].
  assert (Hrng : forall x, in_rng u (u + n) x = true <-> u <= x < u + n).
  { intros x. unfold in_rng. split; intros Hx; [apply andb_prop in Hx as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hcovl : forall x, covered (m_vm_lazy model') x = true -> covered (m_vm_lazy model) x = true /\ ~ (u <= x < u + n)).
  { intros x Hx. rewrite Hlz' in Hx. destruct (maps_subtract_sem (m_vm_lazy model) u (u + n) Hwlz ltac:(lia)) as (_ & _ & Hc).
    rewrite Hc in Hx. apply andb_prop in Hx as [Hx1 Hx2]. split; [exact Hx1|]. intros Hin. apply Hrng in Hin. rewrite Hin in Hx2. discriminate. }
  assert (Hposl : Forall (fun q => 0 < bv_unsigned (snd q)) (List.map (gden E) (sm_maps M))).
  { apply Forall_map. eapply Forall_impl; [|exact Hgsh]. intros q (Q1 & _ & _ & Q4 & _). unfold gden. cbn [snd].
    exact Q1. }
  assert (Hjg : nth_error (List.map (gden E) (sm_maps M)) j = Some (gden E g)) by (rewrite nth_error_map, Hj; reflexivity).
  assert (Hmaps' : vm_maps (m_vmmaps model') = List.map (gden E) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' munmap_M]. rewrite remove_nth_map. rewrite Hmaps.
    assert (Hpd' : pdisj (List.map (gden E) (sm_maps M))) by (rewrite <- Hmaps; exact Hpd).
    exact (map_remove_nth (List.map (gden E) (sm_maps M)) j (gden E g) Hpd' Hposl Hjg). }
  assert (Hrem_In : forall i q, nth_error (sm_maps M) i = Some q -> i <> j -> In q (remove_nth j (sm_maps M)))
    by (intros i q Hi Hne; exact (nth_remove_In _ i j q Hi Hne)).
  assert (Hrem_pos : forall q, In q (remove_nth j (sm_maps M)) -> exists i, i <> j /\ nth_error (sm_maps M) i = Some q)
    by (intros q Hq; exact (remove_nth_pos _ j q Hq)).
  (* [comment removed for export] *)
  assert (Hother : forall i q x, nth_error (sm_maps M) i = Some q -> i <> j -> in_iv (gden E q) x = true -> ~ (u <= x < u + n)).
  { intros i q x Hi Hne Hx Hin. rewrite Hmaps in Hpd.
    assert (Hi' : nth_error (List.map (gden E) (sm_maps M)) i = Some (gden E q)) by (rewrite nth_error_map, Hi; reflexivity).
    pose proof (pdisj_nth _ _ _ _ _ Hpd Hi' Hjg Hne) as Hdis. unfold iv_disj, B, S in Hdis. unfold gden in Hdis, Hx. cbn [fst snd] in Hdis.
    rewrite in_iv_word in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    destruct (Hgsh0 q (nth_error_In _ _ Hi)) as (Q1 & _ & _ & Q4 & _). pose proof (u_lt (lden E (fst (fst q)))).
    assert (E1 : bv_unsigned (lden E (snd (fst q))) = gsz E q) by reflexivity.
    rewrite E1 in Hdis, X2. fold av in Hdis. change (bv_unsigned (lden E (snd (fst g)))) with n in Hdis. rewrite Hua in Hdis. unfold uE in *. lia. }
  assert (Hcovm : forall x, covered (vm_maps (m_vmmaps model)) x = true -> ~ (u <= x < u + n) -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx Hnr. rewrite Hmaps'. rewrite Hmaps in Hx. unfold covered in Hx. apply existsb_exists in Hx as (q & Hq & Hqx).
    apply in_map_iff in Hq as (g0 & <- & Hg0). apply In_nth_error in Hg0 as (i & Hi).
    destruct (Nat.eq_dec i j) as [->|Hne].
    - exfalso. rewrite Hj in Hi. injection Hi as <-. apply Hnr. unfold gden in Hqx. rewrite in_iv_word in Hqx.
      apply andb_prop in Hqx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
      change (bv_unsigned (lden E (fst (fst g)))) with u in X1, X2. change (bv_unsigned (lden E (snd (fst g)))) with n in X2. lia.
    - apply (covered_In _ (gden E g0)); [apply in_map; exact (Hrem_In i g0 Hi Hne) | exact Hqx]. }
  assert (HH' : forall w, H w = false -> H' w = false).
  { intros w Hw. unfold H', Hof. rewrite HA', Hlz'. unfold H, Hof in Hw. unfold mkH in *.
    destruct (page_in_ranges (page_base w) (maps_subtract (m_vm_lazy model) u (u + n))) eqn:Hp2; [|reflexivity].
    rewrite (page_in_ms_sub _ _ _ _ Hwlz Hp2) in Hw. exact Hw. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  set (mem' := apply_zeros (apply_unmaps (ms_mem ms) [(av, Z_to_bv 64 n)]) []).
  assert (Hmout : forall w, ~ (u <= bv_unsigned w < u + n) -> mem' w = ms_mem ms w).
  { intros w Hw. unfold mem'. cbn [apply_zeros]. apply apply_unmaps_out. rewrite zeros_cover_one, Hua, HnZw.
    apply not_true_iff_false. intros Hb. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia. }
  assert (Hpt : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R ->
             mrestrict H' mem' (Z_to_bv 64 (uE E (rg_base R) + i)) = mrestrict H (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. rewrite Forall_forall in HG0. pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR) i Hi) as Hv.
    destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR.
    unfold mrestrict. rewrite Hv, (HH' _ Hv). apply Hmout. rewrite fg64 by (unfold uE in *; lia).
    exact (Hsep R HR (uE E (rg_base R) + i) ltac:(lia)). }
  assert (Hsden : sden segs E (munmap_post L)
                    (restrict H' (advance_past_svc (apply_effect (svc_set ms) (mkEffectU (Z_to_bv 64 0) [] [] [(av, Z_to_bv 64 n)] [] []))))).
  { rewrite (restrict_adv_eff H' ms (Z_to_bv 64 0) [] [(av, Z_to_bv 64 n)] [] (s_pc L) Hpc0). fold mem'.
    intros E'' Ha''. cbn [munmap_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    unfold sden0, munmap_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | rewrite lden_lconst; reflexivity]|].
    split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
    intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. exact (Hpt R HR' i Hi). }
  assert (Hhl' : m_halted model' = m_halted model) by (unfold model', m_halted; rewrite (proj1 Hoth'); reflexivity).
  assert (Htd' : m_tid model' = m_tid model) by (unfold model', m_tid; rewrite (proj1 Hoth'); reflexivity).
  assert (Hgsh' : Forall (gshape_ok E) (sm_maps M')) by (cbn [sm_maps M' munmap_M]; exact (remove_nth_Forall _ j _ Hgsh)).
  assert (Hcovna : forall x, covered (vm_noaccess (m_vmmaps model')) x = (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng u (u + n) x))%bool).
  { intros x. rewrite Hvm'. cbn [vm_noaccess]. exact (proj2 (proj2 (maps_subtract_sem _ u (u + n) Hwna ltac:(lia))) x). }
  assert (Hcovlz : forall x, covered (m_vm_lazy model') x = (covered (m_vm_lazy model) x && negb (in_rng u (u + n) x))%bool).
  { intros x. rewrite Hlz'. exact (proj2 (proj2 (maps_subtract_sem _ u (u + n) Hwlz ltac:(lia))) x). }
  assert (Hkind' : Forall (kind_ok E model') (sm_maps M')).
  { cbn [sm_maps M' munmap_M]. apply Forall_forall. intros q Hq. destruct (Hrem_pos q Hq) as (i & Hne & Hi).
    rewrite Forall_forall in Hkind. split.
    2:{ intros Hgn. pose proof (proj2 (Hkind q (nth_error_In _ _ Hi)) Hgn) as Hin0. rewrite Hvm'. cbn [vm_noaccess].
        rewrite Hmaps in Hpd.
        assert (Hi' : nth_error (List.map (gden E) (sm_maps M)) i = Some (gden E q)) by (rewrite nth_error_map, Hi; reflexivity).
        pose proof (pdisj_nth _ _ _ _ _ Hpd Hi' Hjg Hne) as Hdis. unfold iv_disj, B, S in Hdis. unfold gden in Hdis, Hin0 |- *. cbn [fst snd] in Hdis |- *.
        destruct (Hgsh0 q (nth_error_In _ _ Hi)) as (Q1 & _ & _ & Q4 & _). pose proof (u_lt (lden E (fst (fst q)))).
        assert (E1 : bv_unsigned (lden E (snd (fst q))) = gsz E q) by reflexivity.
        rewrite E1 in Hdis. fold av in Hdis. change (bv_unsigned (lden E (snd (fst g)))) with n in Hdis. rewrite Hua in Hdis.
        apply In_maps_subtract_disj; [exact Hin0 | lia | rewrite E1; unfold uE in *; lia | rewrite E1; lia]. }
    intros Hk0 x Hx. pose proof (proj1 (Hkind q (nth_error_In _ _ Hi)) Hk0 x Hx) as Hc.
    rewrite covered_app, Hcovna, Hcovlz. rewrite covered_app in Hc.
    destruct (in_rng u (u + n) x) eqn:Hr; [exfalso; apply Hrng in Hr; exact (Hother i q x Hi Hne Hx Hr)|].
    cbn [negb]. rewrite !andb_true_r. exact Hc. }
  assert (Hbud' : eager_used model' + A_bytes (allowA E M') <= LIMIT).
  { pose proof (eager_le_old E model' (s_facts L) (sm_maps M') HF0 Hmaps' Hgsh' Hkind') as He.
    pose proof (A_bytes_allowA E M' Hanz) as Hb. cbn [sm_maps sm_allow M' munmap_M] in He, Hb. lia. }
  assert (Hlzm' : forall x, covered (m_vm_lazy model') x = true -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. destruct (Hcovl x Hx) as [H1 H2]. exact (Hcovm x (Hlzm x H1) H2). }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved]. apply Hmres. rewrite Hmaps' in Hx. rewrite Hmaps. unfold covered in *.
    apply existsb_exists in Hx as (q & Hq & Hqx). apply existsb_exists. exists q. split; [|exact Hqx].
    apply in_map_iff in Hq as (g0 & <- & Hg0). apply in_map. exact (remove_nth_In j _ g0 Hg0). }
  constructor.
  - exact Hsden.
  - cbn [munmap_post s_next]. destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp). pose proof (sm_wf_frz _ M Hwf) as Hwz.
    unfold M', munmap_M. apply sm_wf_intro; cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own]; try assumption; try apply Forall_nil.
    pose proof (sm_wf_sizes _ M Hwf) as Hws.
    apply Forall_forall. intros q Hq. rewrite Forall_forall in Hwg, Hws. exact (conj (Hwg q (remove_nth_In j _ q Hq)) (Hws q (remove_nth_In j _ q Hq))).
  - exact Hbw.
  - rewrite Hhl'. exact Hh.
  - exact Hawf.
  - exact Hanz.
  - rewrite (AM_nil model0 _ _ Hblob0). destruct Hminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hmat'.
    + exact (NoDup_filter _ N1).
    + intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
    + intros p Hp. apply filter_In in Hp as [Hp _]. rewrite HA'. exact (N3 p Hp).
    + intros p Hp. apply filter_In in Hp as [Hp Hout]. rewrite Hlz'.
      exact (page_in_ms_keep _ u (u + n) p Hwlz ltac:(lia) Gs3 ltac:(rewrite Z.add_mod, Gs3, Gs2 by lia; reflexivity) (N2 p Hp) Hout (N4 p Hp)).
    + rewrite Hvm'. cbn [vm_limit]. rewrite Hlim. exact Hbud'.
  - unfold H', Hof. apply (hoff_of segs _ _ (vm_maps (m_vmmaps model')) (vm_reserved (m_vmmaps model')) Hsegb);
      [rewrite Hvm'; exact Hres | exact Hlzm' | exact Hmres'].
  - rewrite Hvm'. exact Hres.
  - rewrite Hvm'. exact Hlim.
  - rewrite Hvm'. exact Hsp.
  - rewrite Hvm'. exact Hspok.
  - rewrite Hvm'. exact Hbrk.
  - rewrite Hvm'. exact Hsbrk.
  - rewrite Htd'. exact Htid.
  - rewrite (lden_maps_nomark _ _ _ Hnm'). exact Hmaps'.
  - exact Hgsh'.
  - cbn [sm_maps M' munmap_M]. apply remove_nth_Forall. rewrite Hvm'. exact Hgtop.
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. split; [exact (proj1 (maps_subtract_sem _ u (u + n) Hwna ltac:(lia))) | exact (proj1 (maps_subtract_sem _ u (u + n) Hwlz ltac:(lia)))].
  - rewrite Hmaps'. cbn [sm_maps M' munmap_M]. rewrite remove_nth_map. rewrite <- Hmaps. exact (pdisj_remove j _ Hpd).
  - exact Hmres'.
  - exact Hkind'.
  - exact Hlzm'.
  - exact Hzrsh.
  - intros w Hw. change (in_zr (sm_zr M) w = true) in Hw. apply (Hcovm w (Hzrm w Hw)). intros Hin. rewrite (Hnzr w Hin) in Hw. discriminate.
  - intros w Hw Hout. change (in_zr (sm_zr M) w = true) in Hw. rewrite adv_eff_mem. fold mem'. cbn [munmap_post s_rgs] in Hout.
    rewrite Hmout by (pose proof (Hzrsh w Hw) as Hs; unfold in_shadow, SH_LO, SH_HI in Hs; apply andb_prop in Hs as [S1 S2];
                      apply Z.leb_le in S1; apply Z.ltb_lt in S2; rewrite fg64 by (unfold two64; lia);
                      intros Hin; rewrite (Hnzr w Hin) in Hw; discriminate).
    exact (fun _ _ => Hzr w Hw Hout (own_pt_nil E M w Hon)).
  - rewrite Forall_forall in Hrl |- *. intros R HR. pose proof (Hrl R HR) as [Hpos Hcase]. split; [exact Hpos|].
    assert (Htop' : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
    destruct Hcase as [Happ | (Hoff & HX & Hpc)]; [left | right].
    + intros w Hw. destruct (Happ w Hw) as (Hc & Hns & Hb). split; [|split; assumption]. rewrite (atop_pg_eq _ _ Htop').
      destruct Hc as [Hc|Hc]; [left|right; exact Hc]. replace (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
      rewrite covered_app in *.
      apply orb_prop in Hc as [Hc|Hc]; [rewrite Hc; reflexivity|]. rewrite (Hcovm w Hc (Hsep R HR w Hw)), orb_true_r. reflexivity.
    + split; [exact Hoff|]. split.
      * intros x Hx. destruct (HX x Hx) as (Hc & Hns & Hb). split; [|split; assumption]. rewrite (atop_pg_eq _ _ Htop').
        destruct Hc as [Hc|Hc]; [left|right; exact Hc]. replace (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
        rewrite covered_app in *.
        apply orb_prop in Hc as [Hc|Hc]; [rewrite Hc; reflexivity|]. rewrite (Hcovm x Hc), orb_true_r; [reflexivity|].
        intros Hin. apply (Hsep8 R HR (x / 8 + SH_OFF)).
        -- pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
        -- split; [apply Z.add_le_mono_r, Z.div_le_mono; lia|]. apply Z.add_lt_mono_r.
           pose proof (Z.div_mod (u + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (u + n) 8 ltac:(lia)).
           assert (Hn8 : (u + n) mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists ((u / 4096 + n / 4096) * 512);
             pose proof (Z.div_mod u 4096 ltac:(lia)); pose proof (Z.div_mod n 4096 ltac:(lia)); lia).
           pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
      * intros w Hw. destruct (Hpc w Hw) as [Hs Hc]. split; [exact Hs|]. exact (Hcovm w Hc (Hsep R HR w Hw)).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct Hoth' as (Hp & Hf & Hi & Hs & Hl & Ht).
    unfold model'. rewrite Hf, Hi, Hs, Hl, Ht. repeat split; assumption.
  - rewrite Htd'. destruct Hoth' as (Hp & _). unfold model'. rewrite Hp. exact Hproc.
  - assert (Hgt : u + n <= alloc_top (m_vmmaps model)) by (rewrite Forall_forall in Hgtop; exact (Hgtop g Hgj)).
    apply (frz_keep mem0 E E L (munmap_post L) M M' ms _ model model' Hwf (agree_refl _ _) eq_refl); [unfold alloc_top; rewrite Hvm'; reflexivity | | | exact Hfrz].
    + intros w _ Ho. exact Ho.
    + intros w Hw Ho. rewrite adv_eff_mem. fold mem'. rewrite Hmout; [reflexivity|]. rewrite fg64 by (unfold two64; lia). lia.
  - rom_tac.
  - apply own_nil. reflexivity.
  - rewrite Hblob0. apply blob_ok_nil. exact Hnm'.
Qed.
End Unmap.

Lemma map_has_intro' : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

Definition munmap_ok (res : list (word * word)) (LIMIT : Z) (L : sst) (M : smodel) (j : nat) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in
  match a7c L, arg L 1, nth_error (sm_maps M) j, srl_lin fs 3 a with
  | Some c7, Some len, Some g, Some pb =>
      match gsz_c g with
      | Some z =>
      (Z.eqb c7 215 && lin_eqb a (fst (fst g)) && negb (w_is0 (Z_to_bv 64 len)) && Z.eqb (page_round_up_Z len) z &&
       (let ar := irange fs a in let pr := irange fs (laddc pb SH_OFF) in      (* [comment removed for export] *)
        forallb (fun R => (rgs_sepA fs a ar z R ||| sep_app2_b fs (sm_maps M) j (sm_sp M) a z R ||| sep_res_b res R) &&&      (* [comment removed for export] *)
                          (rgs_sepA fs (laddc pb SH_OFF) pr (z / 8) R ||| sep_pc_b fs (sm_maps M) j (sm_sp M) R ||| sep_pres_b res R)) (s_rgs L)) &&
       (zr_sep fs a z (sm_zr M) ||| sep_noshadow_b fs (RGz a z RZ TEmpty)) &&
       Z.leb (eager_sum fs (remove_nth j (sm_maps M)) + allow_bound (sm_allow M)) LIMIT)%bool
      | None => false
      end
  | _, _, _, _ => false
  end.

Section UnmapNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem den_munmap : forall E L M ms model T j,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] -> nomark (sm_maps M) = true ->
  munmap_ok (segments_reserved segs) LIMIT L M j = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (munmap_post L) (munmap_M M j) ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T j Hd Hon Hnm Hok Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (eq_sym Hmaps) as HmapsL. den_noblob Hnm. apply eq_sym in HmapsL.
  unfold munmap_ok in Hok. set (a := rget (s_regs L) (rkey a0r)) in *.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 1) as [len|] eqn:H1; [|discriminate].
  destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate]. destruct (srl_lin (s_facts L) 3 a) as [pb|] eqn:Hpb; [|discriminate].
  destruct (gsz_c g) as [z|] eqn:Hgc; [|discriminate]. pose proof (gsz_const E g z Hgc) as Hgz.
  apply andb_prop in Hok as [Hok Hbud]. apply Z.leb_le in Hbud. apply andb_prop in Hok as [Hok Hzrc].
  apply andb_prop in Hok as [Hok Hsepc]. apply andb_prop in Hok as [Hok Hlen]. apply Z.eqb_eq in Hlen.
  apply andb_prop in Hok as [Hok Hnz0]. apply negb_true_iff in Hnz0. apply andb_prop in Hok as [Hc7 Ha]. apply Z.eqb_eq in Hc7.
  apply lin_eqb_eq in Ha. subst c7.
  set (H := Hof E M model) in *. set (ms1 := svc_set ms).
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & _ & HF0 & _).
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hgj) as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5).
  rewrite Hgz in Gs1, Gs2, Gs4.
  assert (HuA : uE E a = uE E (fst (fst g))) by (rewrite Ha; reflexivity).
  pose proof (srl_lin_sound E (s_facts L) 3 a pb HF0 ltac:(lia) Hpb) as Hsb. rewrite Z.shiftr_div_pow2 in Hsb by lia. change (2 ^ 3) with 8 in Hsb.
  assert (HuP : uE E (laddc pb SH_OFF) = uE E a / 8 + SH_OFF).
  { unfold uE. rewrite lden_laddc, Hsb. apply fg64. pose proof (u_lt (lden E a)).
    assert (bv_unsigned (lden E a) / 8 < 2305843009213693952) by (apply Z.div_lt_upper_bound; unfold two64 in *; lia).
    split; [pose proof (Z.div_pos (bv_unsigned (lden E a)) 8 ltac:(lia) ltac:(lia)); unfold SH_OFF; lia | unfold SH_OFF, two64; lia]. }
  assert (Hsep : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
            ~ (uE E (fst (fst g)) <= w < uE E (fst (fst g)) + z)).
  { intros R HR w Hw. rewrite forallb_forall in Hsepc. destruct (andb_prop _ _ (Hsepc R HR)) as [S1 _].
    rewrite Forall_forall in HG0. destruct (HG0 R HR) as (HRs & HRw & _). rewrite <- HuA.
    apply orb_prop in S1 as [S1|S1]; [apply orb_prop in S1 as [S1|S1]|].
    - exact (rgs_sepA_sound E (s_facts L) a z R HF0 ltac:(lia) ltac:(rewrite HuA; lia) HRw S1 w Hw).
    - exact (sep_app2_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 HmapsL Hpd Hgsh Hgtop Hsp (proj2 Hspok)
               j g a z R Hj (nomark_in _ g Hnm (nth_error_In _ _ Hj)) ltac:(lia) ltac:(lia) ltac:(unfold uE, two64 in *; lia) HRs HRw S1 w Hw).
    - rewrite <- Hres in S1. exact (sep_res_sound E (sm_maps M) model _ HmapsL Hgsh Hmres
               j g a z R Hj (nomark_in _ g Hnm (nth_error_In _ _ Hj)) ltac:(lia) ltac:(lia) S1 w Hw). }
  assert (Hsep8 : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
     ~ (uE E (fst (fst g)) / 8 + SH_OFF <= w < (uE E (fst (fst g)) + z) / 8 + SH_OFF)).
  { intros R HR w Hw Hin. rewrite forallb_forall in Hsepc. destruct (andb_prop _ _ (Hsepc R HR)) as [_ S2].
    rewrite Forall_forall in HG0. destruct (HG0 R HR) as (HRs & HRw & _).
    assert (Hn8 : (uE E (fst (fst g)) + z) / 8 = uE E (fst (fst g)) / 8 + z / 8).
    { pose proof (Z.div_mod z 4096 ltac:(lia)). rewrite Gs2 in H0.
      replace (uE E (fst (fst g)) + z) with (uE E (fst (fst g)) + (z / 4096 * 512) * 8) by lia.
      rewrite Z.div_add by lia. f_equal. pose proof (Z.div_mod z 8 ltac:(lia)).
      assert (z mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (z / 4096 * 512); lia). lia. }
    assert (Hd8 : z / 8 <= z) by (apply Z.div_le_upper_bound; lia).
    assert (Ha8 : uE E a mod 8 = 0).
    { rewrite HuA. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Gs3; [|lia]. destruct Gs3 as [q Hq]. exists (512 * q). unfold uE in *. lia. }
    assert (Hs8 : z mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Gs2; [|lia]; destruct Gs2 as [q Hq]; exists (512 * q); lia).
    apply orb_prop in S2 as [S2|S2]; [apply orb_prop in S2 as [S2|S2]|].
    - apply (rgs_sepA_sound E (s_facts L) (laddc pb SH_OFF) (z / 8) R HF0 ltac:(apply Z.div_pos; lia)
               ltac:(rewrite HuP, HuA; assert (uE E (fst (fst g)) / 8 <= uE E (fst (fst g))) by (apply Z.div_le_upper_bound; unfold uE in *; lia); unfold SH_OFF in *; lia)
               HRw S2 w Hw).
      rewrite HuP, HuA. lia.
    - assert (HP1 : SH_LO <= uE E a / 8 + SH_OFF) by (pose proof (Z.div_pos (uE E a) 8 ltac:(unfold uE; apply bv_unsigned_in_range) ltac:(lia)); unfold SH_LO, SH_OFF; lia).
      assert (HP2 : uE E a / 8 + SH_OFF + z / 8 <= SH_HI).
      { rewrite HuA. assert (Hdv : (uE E (fst (fst g)) + z) / 8 <= 0x800000000000 / 8) by (apply Z.div_le_mono; unfold uE in *; lia).
        rewrite Hn8 in Hdv. unfold SH_HI, SH_OFF. change (0x800000000000 / 8) with 17592186044416 in Hdv. lia. }
      refine (sep_pc_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 HmapsL Hpd Hgsh Hgtop Hsp (proj2 Hspok)
               j g a z R Hj (nomark_in _ g Hnm (nth_error_In _ _ Hj)) ltac:(lia) ltac:(lia) Ha8 Hs8 Gs1 HP1 HP2 HRs HRw S2 w Hw _).
      rewrite HuA. rewrite Hn8 in Hin. lia.
    - rewrite <- Hres in S2.
      refine (sep_pres_sound E (sm_maps M) model _ HmapsL Hgsh Hmres j g a z R Hj (nomark_in _ g Hnm (nth_error_In _ _ Hj)) ltac:(lia) ltac:(lia)
                Ha8 Hs8 S2 w Hw _). rewrite HuA. rewrite Hn8 in Hin. lia. }
  assert (Hnzr : forall w, uE E (fst (fst g)) <= w < uE E (fst (fst g)) + z -> in_zr (sm_zr M) w = false).
  { intros w Hw. rewrite <- HuA in Hw. apply orb_prop in Hzrc as [Hzrc|Hzrc]; [exact (zr_sep_sound E (s_facts L) a _ _ HF0 Hzrc w Hw)|].
    apply not_true_iff_false. intros Hz. pose proof (Hzrsh w Hz) as Hs.
    rewrite (noshadow_sound E (s_facts L) (RGz a z RZ TEmpty) HF0 Hzrc w) in Hs; [discriminate|].
    cbn [rg_base]. rewrite rsz_RGz by (unfold two64; lia). exact Hw. }
  rewrite <- Hgz in Hsep, Hsep8, Hnzr.
  pose proof (munmap_den segs LIMIT model0 mem0 Hsegb E L M ms model j g Hd Hj Hsep Hsep8 Hnzr Hbud Hon Hnm) as HD'. rewrite Hgz in HD'.
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 215) by exact (a7_const segs E L (restrict H ms) ms 215 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = lden E (fst (fst g))) by (pose proof (gpr_lin segs E L (restrict H ms) ms Hsd eq_refl) as Hx; fold a in Hx; rewrite Ha in Hx; exact Hx).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 len) by exact (gpr_const segs E L (restrict H ms) ms 1 len Hsd eq_refl ltac:(lia) H1).
  destruct (is_const_sound E _ len H1) as [_ Hlen64].
  assert (HnZ : Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = Z_to_bv 64 z) by (rewrite fg64 by exact Hlen64; rewrite Hlen; reflexivity).
  eapply rzc_silent1; [|exact (Hk _ _ HD')].
  pose proof (node_munmap_exact segs cfg ms1 model (ms_reg ms 17) Hh eq_refl ltac:(rewrite Hx8; reflexivity)) as Hn.
  rewrite Hg0, Hg1, HnZ in Hn. apply Hn.
  - unfold page_size. apply Z.eqb_eq. exact Gs3.
  - exact Hnz0.
  - rewrite fg64 by exact Hlen64. rewrite Hlen. apply Z.ltb_ge. unfold TASK_SIZE. unfold uE in *. lia.
  - rewrite Hmaps. apply (map_has_intro' (List.map (gden E) (sm_maps M)) (lden E (fst (fst g))) (Z_to_bv 64 z)).
    replace (Z_to_bv 64 z) with (lden E (snd (fst g))) by exact (proj1 (is_const_sound E _ z Hgc)).
    exact (in_map (gden E) _ _ Hgj).
Qed.
End UnmapNode.
