(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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

Module FxChNorep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition piece_rgs (pcs : list (lin * lin * Z)) : list region := List.map (fun p => RG (fst (fst p)) (snd (fst p)) RZ TEmpty) pcs.
Definition piece_allow (pcs : list (lin * lin * Z)) : list (lin * Z) := List.map (fun p => (fst (fst p), snd p)) pcs.
Definition norep_post (L : sst) (b : Z) (pcs : list (lin * lin * Z)) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (lconst b)) (piece_rgs pcs ++ s_rgs L) (s_facts L) (s_next L) (s_resv L).
Definition norep_M (M : smodel) (b k : Z) (kd : gkind) (pcs : list (lin * lin * Z)) (zr : bool) : smodel :=
  SM ((lconst b, lconst k, kd) :: sm_maps M) (piece_allow pcs ++ sm_allow M) (if zr then (b, b + k) :: sm_zr M else sm_zr M)
     (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) [].

(* [comment removed for export] *)
Definition piece_ok (E : valu) (model : Model) (b k : Z) (p : lin * lin * Z) : Prop :=
  let A := uE E (fst (fst p)) in let s := uE E (snd (fst p)) in
  0 < s /\ s <= snd p /\ b <= A /\ A + s <= b + k /\ SH_OFF <= A /\
  (forall x, 8 * (A - SH_OFF) <= x < 8 * (A - SH_OFF + s) -> app_pt model x).

Lemma piece_rgs_In : forall pcs R, In R (piece_rgs pcs) -> exists p, In p pcs /\ R = RG (fst (fst p)) (snd (fst p)) RZ TEmpty.
Proof. intros pcs R H. unfold piece_rgs in H. apply in_map_iff in H as (p & <- & Hp). exists p. auto. Qed.

Section NorepPost.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem norep_den : forall E L M ms model (b k : Z) (kd : gkind) (flags : word) (na : bool) (pcs : list (lin * lin * Z)) (zr : bool),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  0 <= b < two64 ->
  place_ok model k (Z_to_bv 64 b) -> 0 < k -> k mod 4096 = 0 ->
  (forall w, b <= w < b + k -> in_shadow w = true) ->
  mmap_noreserve_b flags = true ->
  kd = (if na then GN else GL) ->
  (na = true -> pcs = [] /\ zr = false) ->
  Forall (piece_ok E model b k) pcs -> forallb (fun p => lwf (s_next L) (fst (fst p)) && lwf (s_next L) (snd (fst p)))%bool pcs = true ->
  rgs_disj E (piece_rgs pcs) ->
  eager_sum (s_facts L) ((lconst b, lconst k, kd) :: sm_maps M) + allow_bound (piece_allow pcs ++ sm_allow M) <= LIMIT ->
  Forall (fun p => 0 <= snd p) pcs -> sm_own M = [] -> nomark (sm_maps M) = true ->
  DEN segs LIMIT model0 mem0 E (norep_post L b pcs) (norep_M M b k kd pcs zr)
      (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na (Z_to_bv 64 b) (Z_to_bv 64 k))))
      (fresh_next na flags (Z_to_bv 64 b) (Z_to_bv 64 k) model).
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E L M ms model b k kd flags na pcs zr Hd Hb64 Hplace HnZ Hnal Hsh Hnr Hk Hna Hpcs Hpw Hpd' Hbud Hpnz Hon Hnm.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  den_noblob Hnm.
  assert (Hnm' : nomark (sm_maps (norep_M M b k kd pcs zr)) = true).
  { cbn [sm_maps norep_M nomark forallb].
    assert (Hb4 : is_mark (lconst b, lconst k, kd) = false); [|rewrite Hb4; cbn [negb andb]; exact Hnm].
    unfold is_mark. cbn [fst snd]. destruct (is_const (lconst b)) as [c|] eqn:Hc; [|reflexivity].
    destruct (is_const_sound E _ _ Hc) as [Hcv Hcr]. rewrite lden_lconst in Hcv. apply (f_equal bv_unsigned) in Hcv.
    rewrite !fg64 in Hcv by (unfold two64 in *; lia). subst c.
    assert (Hbm : Z.eqb b MARKB = false); [|rewrite Hbm; reflexivity]. apply Z.eqb_neq.
    pose proof (Hsh b ltac:(lia)) as Hs. unfold in_shadow, SH_LO in Hs. apply andb_prop in Hs as [Hs _]. apply Z.leb_le in Hs.
    unfold MARKB. lia. }
  set (a := Z_to_bv 64 b).
  assert (Hua : bv_unsigned a = b) by (unfold a; apply fg64; exact Hb64).
  destruct Hplace as (Hal & Hpos & Htop & Hfree). fold a in Hal, Hpos, Htop, Hfree. rewrite Hua in Hal, Hpos, Htop. unfold page_size in Hal.
  assert (HTOP : b + k <= TOPW).
  { destruct Hspok as [_ Hsp2]. unfold alloc_top, stack_max_size in Htop. unfold TOPW, sp_window_hi in *. lia. }
  assert (HnZw : bv_unsigned (Z_to_bv 64 k) = k) by (apply fg64; unfold TOPW, two64 in *; lia).
  assert (Htpg : b + k <= atop_pg (m_vmmaps model)) by (apply grant_le_atop_pg; [exact Hal | exact Hnal | rewrite ?HnZw in Htop; exact Htop]).
  assert (Hnc : forall x, b <= x < b + k -> covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = false).
  { intros x Hx. apply (region_free_pt _ a (Z_to_bv 64 k)); [exact Hfree | rewrite HnZw, Hua; exact Hx]. }
  set (model' := fresh_next na flags a (Z_to_bv 64 k) model).
  set (M' := norep_M M b k kd pcs zr).
  set (H := Hof E M model) in *.
  set (H' := Hof E M' model').
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  assert (HA' : allowA E M' = List.map (allow1 E) (piece_allow pcs) ++ allowA E M) by (unfold allowA, M', norep_M; cbn [sm_allow]; apply map_app).
  assert (Hli : lazy_interior a (Z_to_bv 64 k) = [(a, Z_to_bv 64 k)]).
  { apply lazy_interior_aligned; rewrite ?HnZw, ?Hua; unfold page_size; try lia. unfold TOPW in HTOP. lia. }
  assert (Hlz' : m_vm_lazy model' = (a, Z_to_bv 64 k) :: m_vm_lazy model).
  { unfold model'. rewrite (fn_lazy na flags a (Z_to_bv 64 k) model), Hnr, Hli. reflexivity. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  (* [comment removed for export] *)
  assert (Hold : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (b <= w < b + k)).
  { intros R HR w Hw Hin. rewrite Forall_forall in Hrl. destruct (Hrl R HR) as [_ [Happ | (_ & _ & Hpc)]].
    - destruct (Happ w Hw) as [[Hc|Hc] _]; [rewrite (Hnc w Hin) in Hc; discriminate | lia].
    - destruct (Hpc w Hw) as [_ Hc]. pose proof (Hnc w Hin) as Hf. rewrite covered_app, Hc, orb_true_r in Hf. discriminate. }
  (* [comment removed for export] *)
  assert (Hpcs' : forall p, In p pcs -> piece_ok E model b k p) by (rewrite Forall_forall in Hpcs; exact Hpcs).
  assert (Hpts : forall R w, In R (piece_rgs pcs) -> uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> b <= w < b + k).
  { intros R w HR Hw. destruct (piece_rgs_In _ _ HR) as (p & Hp & ->). destruct (Hpcs' p Hp) as (Hs & Hub & H1 & H2 & _).
    unfold rsz in Hw. cbn [rg_base rg_size] in Hw. unfold uE in *. lia. }
  (* [comment removed for export] *)
  assert (Hvold : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R -> H' (Z_to_bv 64 (uE E (rg_base R) + i)) = false).
  { intros R HR i Hi. rewrite Forall_forall in HG0.
    pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR) i Hi) as Hv.
    destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR. unfold uE in *.
    unfold H', Hof. rewrite Hlz', HA'. change ((a, Z_to_bv 64 k) :: m_vm_lazy model) with ([(a, Z_to_bv 64 k)] ++ m_vm_lazy model).
    apply mkH_grow; [exact Hv|].
    intros Hp. apply page_in_one in Hp. rewrite HnZw, Hua in Hp. rewrite fg64 in Hp by lia.
    exact (Hold R HR (bv_unsigned (lden E (rg_base R)) + i) ltac:(unfold uE; lia) Hp). }
  assert (Hvpc : forall p y, In p pcs -> uE E (fst (fst p)) <= y < uE E (fst (fst p)) + uE E (snd (fst p)) -> H' (Z_to_bv 64 y) = false).
  { intros p y Hp Hy. destruct (Hpcs' p Hp) as (Hs & Hub & H1 & H2 & _). unfold H', Hof. rewrite HA'. apply mkH_allowed. apply page_allowedb_app_l.
    unfold piece_allow. destruct (in_split _ _ Hp) as (l1 & l2 & ->). rewrite !map_app. apply page_allowedb_app_r. cbn [List.map].
    change (allow1 E (fst (fst p), snd p) :: List.map (allow1 E) (List.map (fun p0 => (fst (fst p0), snd p0)) l2))
      with ([allow1 E (fst (fst p), snd p)] ++ List.map (allow1 E) (List.map (fun p0 => (fst (fst p0), snd p0)) l2)).
    apply page_allowedb_app_l. apply allow1_covers; [unfold TOPW, two64 in *; lia | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  set (mem' := fresh_mem na (ms_mem ms) a (Z_to_bv 64 k)).
  assert (Hmold : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R ->
                    mem' (Z_to_bv 64 (uE E (rg_base R) + i)) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR. unfold uE in *.
    apply fresh_mem_out. rewrite HnZw, Hua. rewrite fg64 by lia.
    exact (Hold R HR (bv_unsigned (lden E (rg_base R)) + i) ltac:(unfold uE; lia)). }
  assert (Hmnew : na = false -> forall y, b <= y < b + k -> mem' (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
  { intros Hn y Hy. unfold mem'. rewrite Hn. apply fresh_mem_in. rewrite HnZw, Hua, fg64 by (unfold TOPW, two64 in *; lia). lia. }
  (* [comment removed for export] *)
  assert (Hsden : sden segs E (norep_post L b pcs) (restrict H' (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a (Z_to_bv 64 k)))))).
  { rewrite (fresh_restrict H' ms na a (Z_to_bv 64 k) (s_pc L) Hpc0).
    intros E'' Ha''. cbn [norep_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    assert (HpE : forall p, In p pcs -> uE E'' (fst (fst p)) = uE E (fst (fst p)) /\ uE E'' (snd (fst p)) = uE E (snd (fst p))).
    { intros p Hp. unfold uE. rewrite forallb_forall in Hpw. destruct (andb_prop _ _ (Hpw p Hp)) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    assert (HprE : forall R, In R (piece_rgs pcs) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. destruct (piece_rgs_In _ _ HR') as (p & Hp & ->). cbn [rg_base]. split; [exact (proj1 (HpE p Hp))|].
      unfold rsz. cbn [rg_size]. exact (proj2 (HpE p Hp)). }
    unfold sden0, norep_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | rewrite lden_lconst; reflexivity]|].
    split; [|split; [|split; [exact HF | exact Hfrm]]].
    - apply Forall_app. split.
      + apply Forall_forall. intros R HR'. destruct (piece_rgs_In _ _ HR') as (p & Hp & ->).
        destruct (Hpcs' p Hp) as (Hs & Hub & H1 & H2 & _). destruct (HpE p Hp) as [He1 He2]. rewrite <- He1 in H1. rewrite <- He1, <- He2 in H2.
        apply rg_ok_fresh_rz_gen; [unfold uE, TOPW, two64 in *; lia|].
        intros i Hi. unfold mrestrict. rewrite (Hvpc p _ Hp) by (rewrite <- He1, <- He2; unfold uE, rsz in *; cbn [rg_size] in Hi; lia).
        destruct na; [destruct (Hna eq_refl) as [Hp0 _]; rewrite Hp0 in Hp; destruct Hp|]. apply Hmnew; [reflexivity | unfold uE, rsz in *; cbn [rg_size] in Hi; lia].
      + apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
        intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. unfold mrestrict.
        rewrite (Hvold R HR' i Hi). rewrite Forall_forall in HG0.
        rewrite (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR') i Hi). exact (Hmold R HR' i Hi).
    - apply rgs_disj_app; [| exact HD |].
      + apply (rgs_disj_agree (s_next L) E E'' (piece_rgs pcs)); [|exact Ha'' | exact Hpd'].
        apply forallb_forall. intros R HR'. destruct (piece_rgs_In _ _ HR') as (p & Hp & ->). unfold rwf. cbn [rg_base rg_size rg_cont].
        rewrite forallb_forall in Hpw. rewrite (Hpw p Hp). reflexivity.
      + intros R1 R2 H1 H2. unfold rg_disj. cbv zeta.
        change (bv_unsigned (lden E'' (rg_base R1))) with (uE E'' (rg_base R1)).
        change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)).
        rewrite (proj1 (HprE R1 H1)), (proj2 (HprE R1 H1)), (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
        pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
        destruct (piece_rgs_In _ _ H1) as (p & Hp & Hp1). destruct (Hpcs' p Hp) as (Hs & Hub & H1' & H2' & _).
        assert (Hs1 : 0 < rsz E R1) by (rewrite Hp1; unfold rsz; cbn [rg_size]; exact Hs).
        apply iv_pts_disj; [exact Hs1 | exact Hpos2|]. intros w Hw1 Hw2. exact (Hold R2 H2 w Hw2 (Hpts R1 w H1 Hw1)). }
  (* [comment removed for export] *)
  assert (Hvm' : m_vmmaps model' = mkVmMapsFull (vm_reserved (m_vmmaps model)) ((a, Z_to_bv 64 k) :: vm_maps (m_vmmaps model))
    (if na then (a, Z_to_bv 64 k) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model))
    (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model)) (vm_mmap_base (m_vmmaps model))
    (vm_init_sp (m_vmmaps model))) by exact (fn_vmmaps na flags a (Z_to_bv 64 k) model).
  assert (Hmat' : m_vm_materialized model' = m_vm_materialized model) by exact (fn_mat na flags a (Z_to_bv 64 k) model).
  assert (Hhl' : m_halted model' = m_halted model) by exact (fn_halted na flags a (Z_to_bv 64 k) model).
  assert (Htd' : m_tid model' = m_tid model) by exact (fn_tid na flags a (Z_to_bv 64 k) model).
  assert (Hoth' : m_proc model' = m_proc model /\ m_fd model' = m_fd model /\ m_io model' = m_io model /\ m_fsys model' = m_fsys model
                  /\ m_lim model' = m_lim model /\ m_time model' = m_time model) by exact (fn_other na flags a (Z_to_bv 64 k) model).
  assert (Hmaps' : vm_maps (m_vmmaps model') = List.map (gden E) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' norep_M List.map]. unfold gden at 1. cbn [fst snd]. rewrite !lden_lconst, Hmaps. reflexivity. }
  assert (Hgsh' : Forall (gshape_ok E) (sm_maps M')).
  { cbn [sm_maps M' norep_M]. constructor; [|exact Hgsh]. unfold gshape_ok, gsz, uE. cbn [fst snd]. rewrite !lden_lconst. fold a. rewrite Hua, HnZw.
    unfold TOPW in HTOP. lia. }
  assert (Hcovm : forall x, covered (vm_maps (m_vmmaps model')) x = (in_iv (a, Z_to_bv 64 k) x || covered (vm_maps (m_vmmaps model)) x)%bool)
    by (intros x; rewrite Hvm'; reflexivity).
  assert (Hinv : forall x, in_iv (a, Z_to_bv 64 k) x = true -> b <= x < b + k).
  { intros x Hx. rewrite in_iv_word, HnZw, Hua in Hx. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert (Hinv' : forall x, b <= x < b + k -> in_iv (a, Z_to_bv 64 k) x = true).
  { intros x Hx. rewrite in_iv_word, HnZw, Hua. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hlzm' : forall x, covered (m_vm_lazy model') x = true -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hcovm. rewrite Hlz', covered_cons in Hx. apply orb_prop in Hx as [H1|H1]; [rewrite H1; reflexivity|].
    rewrite (Hlzm x H1), orb_true_r. reflexivity. }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved]. rewrite Hcovm in Hx. apply orb_prop in Hx as [Hx|Hx]; [|exact (Hmres x Hx)].
    pose proof (Hnc x (Hinv x Hx)) as Hf. rewrite covered_app in Hf. apply orb_false_iff in Hf. exact (proj1 Hf). }
  assert (Hkind' : Forall (kind_ok E model') (sm_maps M')).
  { cbn [sm_maps M' norep_M]. constructor.
    - unfold kind_ok, gden. cbn [fst snd]. rewrite !lden_lconst. fold a. split.
      + intros Hne x Hx. rewrite Hvm'. cbn [vm_noaccess].
        rewrite covered_app, Hlz'. destruct na; cbn [covered existsb]; rewrite Hx; [reflexivity | rewrite orb_true_r; reflexivity].
      + intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. rewrite Hk in Hgn. destruct na; [left; reflexivity | discriminate].
    - rewrite Forall_forall in Hkind |- *. intros g Hg. split.
      + intros Hne x Hx. pose proof (proj1 (Hkind g Hg) Hne x Hx) as Hkx.
        rewrite Hvm'. cbn [vm_noaccess]. rewrite Hlz'. rewrite !covered_app in *. apply orb_prop in Hkx as [H1|H1].
        * destruct na; [rewrite covered_cons, H1, orb_true_r; reflexivity | rewrite H1; reflexivity].
        * rewrite covered_cons, H1, !orb_true_r. reflexivity.
      + intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. pose proof (proj2 (Hkind g Hg) Hgn) as Hi0. destruct na; [right; exact Hi0 | exact Hi0]. }
  assert (Hanz' : Forall (fun p => 0 <= snd p) (sm_allow M')).
  { cbn [sm_allow M' norep_M]. apply Forall_app. split; [|exact Hanz]. unfold piece_allow. apply Forall_map.
    eapply Forall_impl; [|exact Hpnz]. intros p Hp. exact Hp. }
  assert (Hbud' : eager_used model' + A_bytes (allowA E M') <= LIMIT).
  { assert (HFL : Forall (fact_ok E) (s_facts L)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
    pose proof (eager_le_old E model' (s_facts L) (sm_maps M') HFL Hmaps' Hgsh' Hkind') as He.
    pose proof (A_bytes_allowA E M' Hanz') as Hb. cbn [sm_maps sm_allow M' norep_M] in He, Hb. lia. }
  assert (Hcovrm : forall x, covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = true ->
                     covered (vm_reserved (m_vmmaps model') ++ vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app in *. apply orb_prop in Hx as [Hx|Hx];
      [rewrite Hx; reflexivity | rewrite covered_cons, Hx, !orb_true_r; reflexivity]. }
  assert (Hcovm' : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_maps (m_vmmaps model')) x = true)
    by (intros x Hx; rewrite Hcovm, Hx, orb_true_r; reflexivity).
  assert (Htop' : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
  constructor.
  - exact Hsden.
  - cbn [norep_post s_next]. unfold M', norep_M. apply sm_wf_cons; [exact Hwf | reflexivity | reflexivity |].
    apply forallb_forall. intros q Hq. unfold piece_allow in Hq. apply in_map_iff in Hq as (p & <- & Hp). rewrite forallb_forall in Hpw.
    cbn [fst]. exact (proj1 (andb_prop _ _ (Hpw p Hp))).
  - cbn [norep_post s_next s_rgs]. unfold bases_wf. rewrite forallb_app. apply andb_true_intro. split; [|exact Hbw].
    apply forallb_forall. intros R HR'. destruct (piece_rgs_In _ _ HR') as (p & Hp & ->). cbn [rg_base rg_size].
    rewrite forallb_forall in Hpw. exact (Hpw p Hp).
  - rewrite Hhl'. exact Hh.
  - rewrite HA'. unfold A_wf. apply Forall_app. split; [|exact Hawf]. apply A_wf_map_allow1. unfold piece_allow. apply Forall_map.
    eapply Forall_impl; [|exact Hpnz]. intros p Hp. exact Hp.
  - exact Hanz'.
  - rewrite (AM_nil model0 _ _ Hblob0). destruct Hminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hmat'.
    + exact N1.
    + exact N2.
    + intros p Hp. rewrite HA'. apply page_allowedb_app_r. exact (N3 p Hp).
    + intros p Hp. rewrite Hlz'. change ((a, Z_to_bv 64 k) :: m_vm_lazy model) with ([(a, Z_to_bv 64 k)] ++ m_vm_lazy model).
      rewrite page_in_ranges_app, (N4 p Hp), orb_true_r. reflexivity.
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
  - cbn [sm_maps M' norep_M]. constructor.
    + cbn [fst snd]. unfold gsz, uE. cbn [fst snd]. rewrite !lden_lconst. fold a. rewrite Hua, HnZw, Htop'. exact Htop.
    + rewrite Htop'. exact Hgtop.
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. destruct Hivwf as [Hw1 Hw2].
    assert (Hiv : iv_wf (a, Z_to_bv 64 k)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite HnZw, Hua; unfold TOPW in HTOP; lia).
    split; [destruct na; [apply ivs_wf_cons; [exact Hiv | exact Hw1] | exact Hw1] | apply ivs_wf_cons; [exact Hiv | exact Hw2]].
  - rewrite Hvm'. cbn [vm_maps pdisj]. split; [|exact Hpd]. apply Forall_forall. intros q Hq. destruct q as [bb sz].
    assert (Hq' : In (bb, sz) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) by (apply in_or_app; right; exact Hq).
    destruct (region_free_avoid _ _ _ _ _ Hfree Hq') as [H1|H1]; unfold iv_disj, B, S; cbn [fst snd]; lia.
  - exact Hmres'.
  - exact Hkind'.
  - exact Hlzm'.
  - cbn [sm_zr M' norep_M]. intros w Hw. destruct zr; [|exact (Hzrsh w Hw)].
    cbn [in_zr existsb] in Hw. apply orb_prop in Hw as [Hw|Hw]; [|exact (Hzrsh w Hw)].
    cbn [fst snd] in Hw. apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Hsh. lia.
  - cbn [sm_zr M' norep_M]. intros w Hw. destruct zr; [|exact (Hcovm' w (Hzrm w Hw))].
    cbn [in_zr existsb] in Hw. apply orb_prop in Hw as [Hw|Hw]; [|exact (Hcovm' w (Hzrm w Hw))].
    cbn [fst snd] in Hw. apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    rewrite Hcovm, (Hinv' w ltac:(lia)). reflexivity.
  - intros w Hw Hout _ _. cbn [sm_zr M' norep_M] in Hw. rewrite fresh_full_mem. fold mem'.
    unfold outside in Hout. cbn [norep_post s_rgs] in Hout. apply Forall_app in Hout as [_ Hout].
    assert (Hw64 : 0 <= w < two64).
    { destruct zr; [cbn [in_zr existsb] in Hw; apply orb_prop in Hw as [Hw|Hw]|].
      - cbn [fst snd] in Hw. apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold TOPW, two64 in *. lia.
      - pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO, SH_HI in Hs. apply andb_prop in Hs as [H1 H2].
        apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64. lia.
      - pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO, SH_HI in Hs. apply andb_prop in Hs as [H1 H2].
        apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64. lia. }
    destruct (Z_lt_le_dec w b) as [Hlt|Hge]; [|destruct (Z_lt_le_dec w (b + k)) as [Hlt2|Hge2]].
    + unfold mem'. rewrite fresh_mem_out by (rewrite HnZw, Hua, fg64 by exact Hw64; lia).
      destruct zr; [cbn [in_zr existsb] in Hw; apply orb_prop in Hw as [Hw|Hw]|];
        [cbn [fst snd] in Hw; apply andb_prop in Hw as [H1 _]; apply Z.leb_le in H1; lia | |];
        (apply (Hzr w Hw); [exact Hout | exact (own_pt_nil E M w Hon)]).
    + (* [comment removed for export] *)
      destruct na.
      * exfalso. destruct zr.
        -- destruct (Hna eq_refl) as [_ Hz]. discriminate.
        -- pose proof (Hnc w ltac:(lia)) as Hf. rewrite covered_app, (Hzrm w Hw), orb_true_r in Hf. discriminate.
      * apply Hmnew; [reflexivity | lia].
    + unfold mem'. rewrite fresh_mem_out by (rewrite HnZw, Hua, fg64 by exact Hw64; lia).
      destruct zr; [cbn [in_zr existsb] in Hw; apply orb_prop in Hw as [Hw|Hw]|];
        [cbn [fst snd] in Hw; apply andb_prop in Hw as [_ H2]; apply Z.ltb_lt in H2; lia | |];
        (apply (Hzr w Hw); [exact Hout | exact (own_pt_nil E M w Hon)]).
  - cbn [norep_post s_rgs]. apply Forall_app. split.
    + apply Forall_forall. intros R HR'. destruct (piece_rgs_In _ _ HR') as (p & Hp & ->). destruct (Hpcs' p Hp) as (Hs & Hub & H1 & H2 & H3 & H4).
      unfold rl_ok, rsz. cbn [rg_base rg_size]. fold (uE E (snd (fst p))). split; [exact Hs|]. right.
      split; [exact H3|]. split.
      * intros x Hx. destruct (H4 x Hx) as (Hc & Hns & Hb). split; [|split; assumption].
        rewrite (atop_pg_eq _ _ Htop'). destruct Hc as [Hc|Hc]; [left; exact (Hcovrm x Hc) | right; exact Hc].
      * intros w Hw. split; [apply Hsh; lia|]. rewrite Hcovm, (Hinv' w ltac:(lia)). reflexivity.
    + rewrite Forall_forall in Hrl |- *. intros R HR. exact (rl_ok_mono E model model' R Hcovrm Hcovm' Htop' (Hrl R HR)).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct Hoth' as (Hp & Hf & Hi & Hs & Hl & Ht).
    rewrite Hf, Hi, Hs, Hl, Ht. repeat split; assumption.
  - destruct Hoth' as (Hp & _). rewrite Hp, Htd'. exact Hproc.
  - pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
    assert (Hns : forall w, alloc_top (m_vmmaps model) <= w -> ~ (b <= w < b + k)).
    { intros w Hw Hin. pose proof (Hsh w Hin) as Hs. unfold in_shadow, SH_HI in Hs. apply andb_prop in Hs as [_ Hs]. apply Z.ltb_lt in Hs. lia. }
    apply (frz_keep mem0 E E L (norep_post L b pcs) M M' ms _ model model' Hwf (agree_refl _ _) eq_refl Htop'); [| | exact Hfrz].
    + intros w Hw Ho. unfold outside in *. cbn [norep_post s_rgs]. apply Forall_app. split; [|exact Ho].
      apply Forall_forall. intros R HR. assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold two64; lia). rewrite Hw64.
      destruct (Z_lt_le_dec w (uE E (rg_base R))) as [H1|H1]; [left; exact H1|]. right.
      destruct (Z_lt_le_dec w (uE E (rg_base R) + rsz E R)) as [H2|H2]; [|exact H2].
      exfalso. exact (Hns w (proj1 Hw) (Hpts R w HR ltac:(lia))).
    + intros w Hw Ho. rewrite fresh_full_mem. fold mem'. unfold mem'. rewrite fresh_mem_out; [reflexivity|].
      rewrite HnZw, Hua, fg64 by (unfold two64; lia). exact (Hns w (proj1 Hw)).
  - rom_tac.
  - apply own_nil. reflexivity.
  - rewrite Hblob0. apply blob_ok_nil. exact Hnm'.
Qed.
End NorepPost.

(* [comment removed for export] *)
Definition div8_lin (l : lin) : bool := (Z.eqb (l_c l mod 8) 0 && forallb (fun '(_, k) => Z.eqb (k mod 8) 0) (l_t l))%bool.

Lemma tsum_div8 : forall E t, forallb (fun '(_, k) => Z.eqb (k mod 8) 0) t = true -> tsum E t mod 8 = 0.
Proof.
  intros E t. induction t as [|[x k] t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. cbn [tsum]. rewrite Z.add_mod by lia. rewrite (IH H2), Z.add_0_r.
  rewrite Z.mul_mod by lia. rewrite H1. reflexivity.
Qed.

Lemma div8_sound : forall E l, div8_lin l = true -> bv_unsigned (lden E l) mod 8 = 0.
Proof.
  intros E l H. unfold div8_lin in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  rewrite u_lden_mod. rewrite Z.mod_mod_divide by (unfold two64; exists 2305843009213693952; lia).
  unfold lz. rewrite Z.add_mod, H1, (tsum_div8 E _ H2) by lia. reflexivity.
Qed.

Definition piece_of (fs : list fact) (R : region) (ub : Z) : option (lin * lin * Z) :=
  match srl_lin fs 3 (rg_base R), srl_lin fs 3 (rg_size R) with
  | Some pb, Some ps => Some (laddc pb SH_OFF, ps, ub)
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition src_ok (fs : list fact) (n : positive) (wlo whi : Z) (R : region) (ub : Z) : bool :=
  match piece_of fs R ub with
  | Some (pb, ps, _) =>
      (div8_lin (rg_base R) && div8_lin (rg_size R) && Z.leb wlo (fst (irange fs (rg_base R))) &&
       Z.ltb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) two64 &&
       Z.leb (snd (irange fs (ladd (rg_base R) (rg_size R)))) whi && Z.leb (snd (irange fs ps)) ub &&
       lwf n pb && lwf n ps)%bool
  | None => false
  end.

Fixpoint pieces_of (fs : list fact) (rgs : list region) (idxs : list (nat * Z)) : option (list (lin * lin * Z)) :=
  match idxs with
  | [] => Some []
  | (i, ub) :: r => match nth_error rgs i with
                    | Some R => match piece_of fs R ub, pieces_of fs rgs r with Some p, Some ps => Some (p :: ps) | _, _ => None end
                    | None => None
                    end
  end.

Fixpoint srcs_ok (fs : list fact) (n : positive) (wlo whi : Z) (rgs : list region) (idxs : list (nat * Z)) : bool :=
  match idxs with
  | [] => true
  | (i, ub) :: r => match nth_error rgs i with Some R => (src_ok fs n wlo whi R ub && srcs_ok fs n wlo whi rgs r)%bool | None => false end
  end.

(* [comment removed for export] *)
Fixpoint idx_incr (idxs : list (nat * Z)) : bool :=
  match idxs with
  | (i, _) :: (((j, _) :: _) as r) => (Nat.ltb i j && idx_incr r)%bool
  | _ => true
  end.

Lemma ladd_u : forall E a b, bv_unsigned (lden E a) + bv_unsigned (lden E b) < two64 ->
  bv_unsigned (lden E (ladd a b)) = bv_unsigned (lden E a) + bv_unsigned (lden E b).
Proof.
  intros E a b H. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E a)). pose proof (bv_unsigned_in_range _ (lden E b)).
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma src_piece_ok : forall E fs n model (b k wlo whi : Z) R ub p,
  Forall (fact_ok E) fs -> rl_ok E model R -> src_ok fs n wlo whi R ub = true -> piece_of fs R ub = Some p ->
  (whi <= SH_LO \/ SH_HI <= wlo) -> 0 <= wlo -> b <= wlo / 8 + SH_OFF -> whi / 8 + SH_OFF <= b + k ->
  piece_ok E model b k p /\ lwf n (fst (fst p)) = true /\ lwf n (snd (fst p)) = true /\
  uE E (fst (fst p)) = uE E (rg_base R) / 8 + SH_OFF /\ uE E (snd (fst p)) = rsz E R / 8 /\
  uE E (rg_base R) mod 8 = 0 /\ rsz E R mod 8 = 0 /\ wlo <= uE E (rg_base R) /\ uE E (rg_base R) + rsz E R <= whi.
Proof.
  intros E fs n model b k wlo whi R ub p HF Hrl Hok Hp Hwin Hwlo Hb Hk.
  unfold src_ok in Hok. rewrite Hp in Hok. unfold piece_of in Hp.
  destruct (srl_lin fs 3 (rg_base R)) as [pb|] eqn:Hpb; [|discriminate]. destruct (srl_lin fs 3 (rg_size R)) as [ps|] eqn:Hps; [|discriminate].
  injection Hp as <-. cbn [fst snd] in *.
  apply andb_prop in Hok as [Hok Hwps]. apply andb_prop in Hok as [Hok Hwpb]. apply andb_prop in Hok as [Hok Hub].
  apply andb_prop in Hok as [Hok Hwhi]. apply andb_prop in Hok as [Hok Hnw]. apply andb_prop in Hok as [Hok Hwl].
  apply andb_prop in Hok as [Hd1 Hd2].
  apply Z.leb_le in Hub, Hwhi, Hwl. apply Z.ltb_lt in Hnw.
  pose proof (srl_lin_sound E fs 3 _ _ HF ltac:(lia) Hpb) as Hsb. pose proof (srl_lin_sound E fs 3 _ _ HF ltac:(lia) Hps) as Hss.
  rewrite Z.shiftr_div_pow2 in Hsb, Hss by lia. change (2 ^ 3) with 8 in Hsb, Hss.
  pose proof (irange_sound E fs (rg_base R) HF) as Ib. pose proof (irange_sound E fs (rg_size R) HF) as Is.
  pose proof (irange_sound E fs (ladd (rg_base R) (rg_size R)) HF) as Ia. pose proof (irange_sound E fs ps HF) as Ips.
  pose proof (div8_sound E _ Hd1) as D1. pose proof (div8_sound E _ Hd2) as D2.
  rewrite (ladd_u E (rg_base R) (rg_size R) ltac:(lia)) in Ia.
  assert (HA : uE E (laddc pb SH_OFF) = uE E (rg_base R) / 8 + SH_OFF).
  { unfold uE. rewrite lden_laddc, Hsb. apply fg64. pose proof (u_lt (lden E (rg_base R))).
    assert (bv_unsigned (lden E (rg_base R)) / 8 < 2305843009213693952) by (apply Z.div_lt_upper_bound; unfold two64 in *; lia).
    split; [pose proof (Z.div_pos (bv_unsigned (lden E (rg_base R))) 8 ltac:(lia) ltac:(lia)); unfold SH_OFF; lia | unfold SH_OFF, two64; lia]. }
  assert (HS : uE E ps = rsz E R / 8) by (unfold uE, rsz; exact Hss).
  destruct Hrl as [Hpos Hcase].
  set (u := uE E (rg_base R)) in *. set (s := rsz E R) in *. unfold uE in u. unfold rsz in s.
  assert (Hu8 : u = 8 * (u / 8)) by (pose proof (Z.div_mod u 8 ltac:(lia)); lia).
  assert (Hs8 : s = 8 * (s / 8)) by (pose proof (Z.div_mod s 8 ltac:(lia)); lia).
  assert (Hus : (u + s) / 8 = u / 8 + s / 8) by (rewrite Hu8 at 1; rewrite Hs8 at 1; rewrite <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (Hwd : u / 8 >= wlo / 8) by (apply Z.le_ge, Z.div_le_mono; lia).
  assert (Hwu : (u + s) / 8 <= whi / 8) by (apply Z.div_le_mono; lia).
  split; [|split; [exact Hwpb | split; [exact Hwps | split; [exact HA | split; [exact HS | split; [exact D1 | split; [exact D2 | split; lia]]]]]]].
  unfold piece_ok. cbn [fst snd]. fold u. rewrite HA, HS. fold s.
  assert (Hs0 : 0 < s / 8) by lia.
  split; [exact Hs0|]. split; [rewrite <- HS; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros x Hx. replace (8 * (u / 8 + SH_OFF - SH_OFF)) with u in Hx by lia.
  replace (8 * (u / 8 + SH_OFF - SH_OFF + s / 8)) with (u + s) in Hx by lia.
  destruct Hcase as [Happ | (_ & _ & Hpc)]; [exact (Happ x Hx)|].
  exfalso. destruct (Hpc u ltac:(lia)) as [Hsh _]. unfold in_shadow, SH_LO, SH_HI in Hsh, Hwin.
  apply andb_prop in Hsh as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma pieces_spec : forall E fs n model (b k wlo whi : Z) rgs idxs pcs,
  Forall (fact_ok E) fs -> Forall (rl_ok E model) rgs -> rgs_disj E rgs ->
  srcs_ok fs n wlo whi rgs idxs = true -> pieces_of fs rgs idxs = Some pcs ->
  (whi <= SH_LO \/ SH_HI <= wlo) -> 0 <= wlo -> b <= wlo / 8 + SH_OFF -> whi / 8 + SH_OFF <= b + k ->
  Forall (piece_ok E model b k) pcs /\
  forallb (fun p => lwf n (fst (fst p)) && lwf n (snd (fst p)))%bool pcs = true /\
  Forall (fun p => 0 <= snd p) pcs /\
  (forall p, In p pcs -> exists i R, In (i, snd p) idxs /\ nth_error rgs i = Some R /\
     uE E (fst (fst p)) = uE E (rg_base R) / 8 + SH_OFF /\ uE E (snd (fst p)) = rsz E R / 8 /\
     uE E (rg_base R) mod 8 = 0 /\ rsz E R mod 8 = 0).
Proof.
  intros E fs n model b k wlo whi rgs idxs. induction idxs as [|[i ub] r IH]; intros pcs HF Hrl Hd Hok Hp Hwin Hwlo Hb Hk.
  - injection Hp as <-. repeat split; try constructor. intros p [].
  - cbn [srcs_ok pieces_of] in Hok, Hp. destruct (nth_error rgs i) as [R|] eqn:Hi; [|discriminate].
    apply andb_prop in Hok as [Hok1 Hok2].
    destruct (piece_of fs R ub) as [p|] eqn:Hpo; [|discriminate]. destruct (pieces_of fs rgs r) as [ps|] eqn:Hps; [|discriminate].
    injection Hp as <-. destruct (IH ps HF Hrl Hd Hok2 ltac:(first [exact Hps | reflexivity]) Hwin Hwlo Hb Hk) as (P1 & P2 & P3 & P4).
    rewrite Forall_forall in Hrl. pose proof (Hrl R (nth_error_In _ _ Hi)) as HR.
    destruct (src_piece_ok E fs n model b k wlo whi R ub p HF HR Hok1 Hpo Hwin Hwlo Hb Hk) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _).
    split; [constructor; assumption|]. split; [cbn [forallb]; rewrite Q2, Q3, P2; reflexivity|].
    split; [constructor; [|exact P3]; destruct Q1 as (_ & Hub & _); unfold uE in *; pose proof (u_lt (lden E (snd (fst p)))); lia|].
    intros q [<-|Hq].
    + unfold piece_of in Hpo. destruct (srl_lin fs 3 (rg_base R)), (srl_lin fs 3 (rg_size R)); try discriminate. injection Hpo as <-.
      exists i, R. split; [left; reflexivity|]. split; [exact Hi|]. cbn [fst snd] in *. auto.
    + destruct (P4 q Hq) as (j & Rj & Hj & HRj & H1 & H2 & H3 & H4). exists j, Rj. split; [right; exact Hj|]. auto.
Qed.

Lemma idx_incr_lt : forall i ub r, idx_incr ((i, ub) :: r) = true -> idx_incr r = true /\ forall j u, In (j, u) r -> (i < j)%nat.
Proof.
  intros i ub r. revert i ub. induction r as [|[j u] r IH]; intros i ub H; [split; [reflexivity | intros j0 u0 []]|].
  cbn [idx_incr] in H. apply andb_prop in H as [H1 H2]. apply Nat.ltb_lt in H1. split; [exact H2|].
  destruct (IH j u H2) as [_ Hr]. intros j0 u0 [Heq|Hin]; [injection Heq as <- <-; exact H1 | pose proof (Hr j0 u0 Hin); lia].
Qed.

Lemma pieces_src : forall fs rgs idxs pcs, pieces_of fs rgs idxs = Some pcs ->
  Forall2 (fun iu p => exists R, nth_error rgs (fst iu) = Some R /\ piece_of fs R (snd iu) = Some p) idxs pcs.
Proof.
  intros fs rgs idxs. induction idxs as [|[i ub] r IH]; intros pcs H; cbn [pieces_of] in H; [injection H as <-; constructor|].
  destruct (nth_error rgs i) as [R|] eqn:Hi; [|discriminate].
  destruct (piece_of fs R ub) as [p|] eqn:Hp; [|discriminate]. destruct (pieces_of fs rgs r) as [ps|] eqn:Hps; [|discriminate].
  injection H as <-. constructor; [exists R; auto | apply IH; first [exact Hps | reflexivity]].
Qed.

Lemma Forall2_In_r : forall {A B} (P : A -> B -> Prop) l1 l2 y, Forall2 P l1 l2 -> In y l2 -> exists x, In x l1 /\ P x y.
Proof.
  intros A B P l1 l2 y H. induction H as [|x1 y1 l1' l2' Hxy Hr IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists x1; split; [left; reflexivity | exact Hxy]|].
  destruct (IH Hin) as (x & Hx & Hp). exists x. split; [right; exact Hx | exact Hp].
Qed.

Lemma srcs_ok_In : forall fs n wlo whi rgs idxs j u, srcs_ok fs n wlo whi rgs idxs = true -> In (j, u) idxs ->
  exists R, nth_error rgs j = Some R /\ src_ok fs n wlo whi R u = true.
Proof.
  intros fs n wlo whi rgs idxs. induction idxs as [|[i ub] r IH]; intros j u H Hin; [destruct Hin|].
  cbn [srcs_ok] in H. destruct (nth_error rgs i) as [R|] eqn:Hi; [|discriminate]. apply andb_prop in H as [H1 H2].
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; exists R; auto | exact (IH j u H2 Hin)].
Qed.

Lemma pieces_disj : forall E fs n model (b k wlo whi : Z) rgs idxs pcs,
  Forall (fact_ok E) fs -> Forall (rl_ok E model) rgs -> rgs_disj E rgs ->
  srcs_ok fs n wlo whi rgs idxs = true -> pieces_of fs rgs idxs = Some pcs -> idx_incr idxs = true ->
  (whi <= SH_LO \/ SH_HI <= wlo) -> 0 <= wlo -> b <= wlo / 8 + SH_OFF -> whi / 8 + SH_OFF <= b + k ->
  rgs_disj E (piece_rgs pcs).
Proof.
  intros E fs n model b k wlo whi rgs idxs. induction idxs as [|[i ub] r IH]; intros pcs HF Hrl Hd Hok Hp Hinc Hwin Hwlo Hb Hk.
  - injection Hp as <-. exact I.
  - cbn [srcs_ok pieces_of] in Hok, Hp. destruct (nth_error rgs i) as [R|] eqn:Hi; [|discriminate].
    apply andb_prop in Hok as [Hok1 Hok2].
    destruct (piece_of fs R ub) as [p|] eqn:Hpo; [|discriminate]. destruct (pieces_of fs rgs r) as [ps|] eqn:Hps; [|discriminate].
    injection Hp as <-. destruct (idx_incr_lt i ub r Hinc) as [Hinc' Hlt].
    cbn [piece_rgs List.map rgs_disj]. split; [|exact (IH ps HF Hrl Hd Hok2 ltac:(first [exact Hps | reflexivity]) Hinc' Hwin Hwlo Hb Hk)].
    apply Forall_forall. intros R2 HR2. unfold piece_rgs in HR2. apply in_map_iff in HR2 as (q & <- & Hq).
    pose proof (pieces_src fs rgs r ps ltac:(first [exact Hps | reflexivity])) as Hsrc.
    destruct (Forall2_In_r _ _ _ q Hsrc Hq) as ([j u] & Hj & (Rj & HRj & Hqo)). cbn [fst snd] in HRj, Hqo.
    destruct (srcs_ok_In _ _ _ _ _ _ j u Hok2 Hj) as (Rj' & HRj' & Hokj). rewrite HRj in HRj'. injection HRj' as <-.
    pose proof Hrl as Hrl'. rewrite Forall_forall in Hrl'.
    destruct (src_piece_ok E fs n model b k wlo whi R ub p HF (Hrl' R (nth_error_In _ _ Hi)) Hok1 Hpo Hwin Hwlo Hb Hk)
      as (_ & _ & _ & A1 & S1 & D1 & D1s & _).
    destruct (src_piece_ok E fs n model b k wlo whi Rj u q HF (Hrl' Rj (nth_error_In _ _ HRj)) Hokj Hqo Hwin Hwlo Hb Hk)
      as (_ & _ & _ & A2 & S2 & D2 & D2s & _).
    pose proof (rgs_disj_nth E rgs i j R Rj Hd ltac:(pose proof (Hlt j u Hj); lia) Hi HRj) as Hdis.
    unfold rg_disj in *. cbv zeta in *. unfold rsz in *. cbn [rg_base rg_size].
    change (bv_unsigned (lden E (fst (fst p)))) with (uE E (fst (fst p))). change (bv_unsigned (lden E (snd (fst p)))) with (uE E (snd (fst p))).
    change (bv_unsigned (lden E (fst (fst q)))) with (uE E (fst (fst q))). change (bv_unsigned (lden E (snd (fst q)))) with (uE E (snd (fst q))).
    rewrite A1, S1, A2, S2. unfold uE in *.
    set (u1 := bv_unsigned (lden E (rg_base R))) in *. set (s1 := bv_unsigned (lden E (rg_size R))) in *.
    set (u2 := bv_unsigned (lden E (rg_base Rj))) in *. set (s2 := bv_unsigned (lden E (rg_size Rj))) in *.
    pose proof (Z.div_mod u1 8 ltac:(lia)). pose proof (Z.div_mod s1 8 ltac:(lia)).
    pose proof (Z.div_mod u2 8 ltac:(lia)). pose proof (Z.div_mod s2 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition iv_overlapZ (a n b m : Z) : bool := (a <? b + m) && (b <? a + n).
Definition norep_free (res : list (word * word)) (M : smodel) (b k : Z) : bool :=
  (forallb (fun g => match is_const (fst (fst g)), is_const (snd (fst g)) with Some c, Some z => negb (iv_overlapZ b k c z) | _, _ => false end) (sm_maps M) &&
   region_free res (Z_to_bv 64 b) (Z_to_bv 64 k))%bool.

Lemma region_free_app : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n)%bool.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.

Lemma norep_free_sound : forall E M res b k, Forall (gshape_ok E) (sm_maps M) -> 0 <= b < two64 -> 0 <= k < two64 ->
  norep_free res M b k = true -> region_free (res ++ List.map (gden E) (sm_maps M)) (Z_to_bv 64 b) (Z_to_bv 64 k) = true.
Proof.
  intros E M res b k Hsh Hb Hk H. unfold norep_free in H. apply andb_prop in H as [H1 H2].
  rewrite region_free_app, H2. cbn [andb]. clear H2.
  induction (sm_maps M) as [|g gs IH]; [reflexivity|]. cbn [forallb] in H1. apply andb_prop in H1 as [Hg Hgs].
  inversion Hsh as [|? ? Hshg Hshgs]; subst. change (List.map (gden E) (g :: gs)) with (gden E g :: List.map (gden E) gs).
  unfold gden at 1. cbn [region_free fst snd]. rewrite (IH Hshgs Hgs), andb_true_r.
  destruct (is_const (fst (fst g))) as [c|] eqn:Hc; [|discriminate]. destruct (is_const_sound E _ c Hc) as [Hce Hcr].
  destruct (is_const (snd (fst g))) as [z|] eqn:Hz; [|discriminate]. destruct (is_const_sound E _ z Hz) as [Hze Hzr].
  rewrite Hce, Hze. unfold iv_overlap, iv_overlapZ in *. destruct Hshg as (Hs1 & _ & _ & Hs4).
  unfold gsz, uE in Hs1, Hs4. rewrite Hce, Hze, !fg64 in Hs4 by assumption. rewrite Hze, fg64 in Hs1 by exact Hzr.
  rewrite !fg64 by (unfold two64 in *; lia). exact Hg.
Qed.

Definition norep_ok (res : list (word * word)) (LIMIT : Z) (L : sst) (M : smodel) (b k : Z) (kd : gkind) (na : bool)
    (idxs : list (nat * Z)) (zr : bool) (wlo whi : Z) : bool :=
  match a7c L, arg L 0, arg L 1, arg L 2, arg L 3, arg L 5, pieces_of (s_facts L) (s_rgs L) idxs with
  | Some c7, Some c0, Some len, Some prot, Some flags, Some off, Some pcs =>
      (Z.eqb c7 222 && Z.eqb c0 b && Z.ltb 0 b && Z.ltb b two64 &&
       mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) && negb (w_is0 (Z_to_bv 64 len)) &&
       negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       (if na then mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else negb (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
             && mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       Z.eqb k (page_round_up_Z len) && Z.eqb (b mod 4096) 0 && Z.leb (b + k) 0x7fff7f800000 &&
       norep_free res M b k && Z.leb SH_LO b && Z.leb (b + k) SH_HI &&
       mmap_noreserve_b (Z_to_bv 64 flags) && gkind_eqb kd (if na then GN else GL) &&
       (negb na || (match idxs with [] => true | _ => false end && negb zr)) &&
       srcs_ok (s_facts L) (s_next L) wlo whi (s_rgs L) idxs && idx_incr idxs &&
       (Z.leb whi SH_LO || Z.leb SH_HI wlo) && Z.leb 0 wlo && Z.leb b (wlo / 8 + SH_OFF) && Z.leb (whi / 8 + SH_OFF) (b + k) &&
       Z.leb (eager_sum (s_facts L) ((lconst b, lconst k, kd) :: sm_maps M) + allow_bound (piece_allow pcs ++ sm_allow M)) LIMIT)%bool
  | _, _, _, _, _, _, _ => false
  end.

Section NorepNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hsegb Hoff"] Theorem den_norep : forall E L M ms model T b k kd na idxs zr wlo whi pcs,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] -> nomark (sm_maps M) = true ->
  norep_ok (segments_reserved segs) LIMIT L M b k kd na idxs zr wlo whi = true ->
  pieces_of (s_facts L) (s_rgs L) idxs = Some pcs ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (norep_post L b pcs) (norep_M M b k kd pcs zr) ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T b k kd na idxs zr wlo whi pcs Hd Hon Hnm Hok Hpcs Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  den_noblob Hnm.
  unfold norep_ok in Hok. rewrite Hpcs in Hok.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg L 1) as [len|] eqn:H1; [|discriminate]. destruct (arg L 2) as [prot|] eqn:H2; [|discriminate].
  destruct (arg L 3) as [flags|] eqn:H3; [|discriminate]. destruct (arg L 5) as [off|] eqn:H5; [|discriminate].
  apply andb_prop in Hok as [Hok Hbud]. apply Z.leb_le in Hbud.
  apply andb_prop in Hok as [Hok Hwk]. apply Z.leb_le in Hwk. apply andb_prop in Hok as [Hok Hwb]. apply Z.leb_le in Hwb.
  apply andb_prop in Hok as [Hok Hwlo]. apply Z.leb_le in Hwlo. apply andb_prop in Hok as [Hok Hwin].
  apply andb_prop in Hok as [Hok Hinc]. apply andb_prop in Hok as [Hok Hsrcs]. apply andb_prop in Hok as [Hok Hnaz].
  apply andb_prop in Hok as [Hok Hkd]. apply andb_prop in Hok as [Hok Hnr]. apply andb_prop in Hok as [Hok Hshi].
  apply Z.leb_le in Hshi. apply andb_prop in Hok as [Hok Hslo]. apply Z.leb_le in Hslo. apply andb_prop in Hok as [Hok Hfree].
  apply andb_prop in Hok as [Hok Htopc]. apply Z.leb_le in Htopc. apply andb_prop in Hok as [Hok Hal]. apply Z.eqb_eq in Hal.
  apply andb_prop in Hok as [Hok Hlen]. apply Z.eqb_eq in Hlen. apply andb_prop in Hok as [Hok Hsel].
  apply andb_prop in Hok as [Hok Hfrw]. apply andb_prop in Hok as [Hok Hfna]. apply andb_prop in Hok as [Hok Hnac].
  apply andb_prop in Hok as [Hok Hmod]. apply andb_prop in Hok as [Hok Hnz0]. apply andb_prop in Hok as [Hok Hanon].
  apply andb_prop in Hok as [Hok Hoffa]. apply andb_prop in Hok as [Hok Hb64]. apply Z.ltb_lt in Hb64.
  apply andb_prop in Hok as [Hok Hbpos]. apply Z.ltb_lt in Hbpos. apply andb_prop in Hok as [Hok Hc0]. apply Z.eqb_eq in Hok, Hc0.
  subst c7 c0. apply negb_true_iff in Hnz0, Hmod, Hnac, Hfna, Hfrw.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = Z_to_bv 64 b) by exact (gpr_const segs E L (restrict H ms) ms 0 b Hsd eq_refl ltac:(lia) H0).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 len) by exact (gpr_const segs E L (restrict H ms) ms 1 len Hsd eq_refl ltac:(lia) H1).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  destruct (is_const_sound E _ len H1) as [_ Hlen64].
  assert (HnZ : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = k) by (rewrite fg64 by exact Hlen64; symmetry; exact Hlen).
  assert (HnZpos : 0 < k) by (rewrite <- HnZ; exact (len_nZ_pos _ Hnz0)).
  assert (HnZal : k mod 4096 = 0) by (rewrite <- HnZ; exact (page_round_up_Z_aligned' _)).
  assert (Hub : bv_unsigned (Z_to_bv 64 b) = b) by (apply fg64; lia).
  assert (HTOP : b + k <= alloc_top (m_vmmaps model)).
  { destruct Hspok as [Hsp1 _]. unfold init_sp_ok, sp_window_lo in Hsp1. unfold alloc_top, stack_max_size. lia. }
  assert (Hrf : region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (Z_to_bv 64 b) (Z_to_bv 64 k) = true).
  { rewrite Hres, Hmaps. apply norep_free_sound; [exact Hgsh | lia | unfold SH_HI, two64 in *; lia | exact Hfree]. }
  assert (Hplace : place_ok model k (Z_to_bv 64 b)).
  { unfold place_ok, page_size. rewrite Hub. repeat split; try lia. exact Hrf. }
  assert (Hgate : fixed_gate model (Z_to_bv 64 b) (Z_to_bv 64 len)).
  { unfold fixed_gate, page_size. rewrite Hub, HnZ. repeat split; lia. }
  assert (Hsh : forall w, b <= w < b + k -> in_shadow w = true).
  { intros w Hw. unfold in_shadow. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hkk : kd = (if na then GN else GL)) by (destruct kd, na; cbn in Hkd; try discriminate; reflexivity).
  assert (Hnal : na = true -> pcs = [] /\ zr = false).
  { intros Hn. rewrite Hn in Hnaz. cbn in Hnaz. destruct idxs; [|discriminate]. cbn in Hpcs. injection Hpcs as <-.
    destruct zr; [discriminate | split; reflexivity]. }
  assert (Hwin' : whi <= SH_LO \/ SH_HI <= wlo) by (apply orb_prop in Hwin as [Hw|Hw]; [left|right]; apply Z.leb_le; exact Hw).
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & HG0 & HD0 & HF0 & _).
  destruct (pieces_spec E (s_facts L) (s_next L) model b k wlo whi (s_rgs L) idxs pcs HF0 Hrl HD0 Hsrcs Hpcs Hwin' Hwlo Hwb Hwk)
    as (P1 & P2 & P3 & _).
  pose proof (pieces_disj E (s_facts L) (s_next L) model b k wlo whi (s_rgs L) idxs pcs HF0 Hrl HD0 Hsrcs Hpcs Hinc Hwin' Hwlo Hwb Hwk) as P4.
  pose proof (norep_den segs LIMIT model0 mem0 Hsegb E L M ms model b k kd (Z_to_bv 64 flags) na pcs zr Hd ltac:(unfold two64 in *; lia) Hplace
                HnZpos HnZal Hsh Hnr Hkk Hnal P1 P2 P4 Hbud P3 Hon Hnm) as HD'.
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  destruct na.
  - (* [comment removed for export] *)
    assert (Hbr := branch_noreplace_na_free segs ms1 (ms_reg ms 17) model Hno).
    rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr.
    specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hfna Hfrw Hsel Hgate Hrf).
    eapply rzc_silent1; [|exact (Hk _ _ HD')].
    apply (node_mmap_alt_choose_at segs cfg Hoff ms1 model (ms_reg ms 17) (Z_to_bv 64 b) (fun a => a = Z_to_bv 64 b)
             (fun a => fresh_na_next (Z_to_bv 64 flags) a (Z_to_bv 64 k) model)
             (fun a => mkEffectU a [] [] [(a, Z_to_bv 64 k)] [] []) Hh Hsvc Hno Hbr).
    + intros a Ha. exact Ha.
    + reflexivity.
    + cbn [eff_ret]. apply (below_top_not_errno (m_vmmaps model) _ ENOMEM ENOMEM_range). rewrite Hub. lia.
    + intros a. apply vm_only_fresh_na_next.
    + reflexivity.
  - (* [comment removed for export] *)
    assert (Hbr := branch_noreplace_rw_free segs ms1 (ms_reg ms 17) model Hno).
    rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr.
    apply andb_prop in Hsel as [Hsel1 Hsel2]. apply negb_true_iff in Hsel1.
    specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hfna Hfrw Hsel1 Hsel2 Hgate Hrf).
    eapply rzc_silent1; [|exact (Hk _ _ HD')].
    apply (node_mmap_alt_choose_at segs cfg Hoff ms1 model (ms_reg ms 17) (Z_to_bv 64 b)
             (fun a => a = Z_to_bv 64 b /\ mmap_noreserve_backed_ok (Z_to_bv 64 flags) model k = true)
             (fun a => fresh_rw_next (Z_to_bv 64 flags) a (Z_to_bv 64 k) model)
             (fun a => mkEffect a [] [(a, Z_to_bv 64 k)]) Hh Hsvc Hno Hbr).
    + intros a [Ha _]. exact Ha.
    + split; [reflexivity|]. unfold mmap_noreserve_backed_ok. rewrite Hnr. reflexivity.
    + cbn [eff_ret]. apply (below_top_not_errno (m_vmmaps model) _ ENOMEM ENOMEM_range). rewrite Hub. lia.
    + intros a. apply vm_only_fresh_rw_next.
    + reflexivity.
Qed.
End NorepNode.
End FxChNorep.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix.FxChNorep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fixed_next (na : bool) (flags a n : word) (m : Model) : Model :=
  if na then fixed_na_next flags a n m else fixed_rw_next flags a n m.

Lemma fx_vmmaps : forall na flags a n m, m_vmmaps (fixed_next na flags a n m) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
    ((if na then [(a, n)] else []) ++ maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof.
  intros na flags a n m. unfold fixed_next, fixed_na_next, fixed_rw_next, mmap_fixed_rw_next, with_mmap_replacement, with_mmap_backing,
    vm_add_lazy, vm_forget_range.
  destruct na, (mmap_noreserve_b flags); destruct m; reflexivity.
Qed.
Lemma fx_lazy : forall na flags a n m, m_vm_lazy (fixed_next na flags a n m) =
  (if mmap_noreserve_b flags then lazy_interior a n else []) ++ maps_subtract (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
  intros na flags a n m. unfold fixed_next, fixed_na_next, fixed_rw_next, mmap_fixed_rw_next, with_mmap_replacement, with_mmap_backing,
    vm_add_lazy, vm_forget_range.
  destruct na, (mmap_noreserve_b flags); destruct m; reflexivity.
Qed.
Lemma fx_mat : forall na flags a n m, m_vm_materialized (fixed_next na flags a n m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof.
  intros na flags a n m. unfold fixed_next, fixed_na_next, fixed_rw_next, mmap_fixed_rw_next, with_mmap_replacement, with_mmap_backing,
    vm_add_lazy, vm_forget_range.
  destruct na, (mmap_noreserve_b flags); destruct m; reflexivity.
Qed.
Lemma fx_other : forall na flags a n m, let m' := fixed_next na flags a n m in
  m_proc m' = m_proc m /\ m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_lim m' = m_lim m /\ m_time m' = m_time m.
Proof.
  intros na flags a n m. unfold fixed_next, fixed_na_next, fixed_rw_next, mmap_fixed_rw_next, with_mmap_replacement, with_mmap_backing,
    vm_add_lazy, vm_forget_range.
  destruct na, (mmap_noreserve_b flags); destruct m; cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_pieces : forall (a sz : word) lo hi q, iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) ->
  bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs. unfold bv_modulus in Ra, Rs.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Ra, Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !fg_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !fg_lit by lia. lia.
Qed.

Lemma page_in_ms_sub : forall l lo hi p, ivs_wf l -> page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi p Hwf H; [exact H|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in H. unfold page_in_ranges in *. rewrite existsb_app in H.
  cbn [existsb]. apply orb_prop in H as [H|H]; [|rewrite (IH lo hi p Hl H), orb_true_r; reflexivity].
  apply existsb_exists in H as (q & Hq & Hp). destruct (iv_subtract_pieces a sz lo hi q Ha Hq) as [H1 H2].
  apply andb_prop in Hp as [P1 P2]. apply Z.leb_le in P1, P2. cbn [fst snd].
  replace ((bv_unsigned a <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned a + bv_unsigned sz))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ms_keep : forall l (lo hi : Z) (p : word), ivs_wf l -> lo <= hi -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  bv_unsigned p mod 4096 = 0 -> page_outside_range lo hi p = true ->
  page_in_ranges p l = true -> page_in_ranges p (maps_subtract l lo hi) = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi p Hwf Hlh Hlo Hhi Hp Hout H; [exact H|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. unfold page_in_ranges in *. cbn [existsb maps_subtract] in *. rewrite existsb_app.
  apply orb_prop in H as [H|H]; [|rewrite (IH lo hi p Hl Hlh Hlo Hhi Hp Hout H), orb_true_r; reflexivity].
  cbn [fst snd] in H. apply andb_prop in H as [P1 P2]. apply Z.leb_le in P1, P2. unfold page_size in P2.
  unfold page_outside_range in Hout. apply negb_true_iff, andb_false_iff in Hout.
  unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs. unfold bv_modulus in Ra, Rs.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Ra, Rs. pose proof (bv_unsigned_in_range _ p) as Rp. unfold bv_modulus in Rp.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rp.
  apply orb_true_intro. left. unfold iv_subtract. cbv zeta. rewrite existsb_app. apply orb_true_intro.
  destruct Hout as [Hout|Hout]; [apply Z.leb_gt in Hout | apply Z.ltb_ge in Hout].
  - (* [comment removed for export] *)
    assert (Hp4 : bv_unsigned p + 4096 <= lo).
    { pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). pose proof (Z.div_mod lo 4096 ltac:(lia)).
      assert (bv_unsigned p / 4096 < lo / 4096) by lia. lia. }
    left. replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia). cbn [existsb fst snd].
    rewrite orb_false_r. rewrite !fg_lit by lia. unfold page_size. apply andb_true_intro. split; apply Z.leb_le; lia.
  - right. replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia). cbn [existsb fst snd].
    rewrite orb_false_r. rewrite !fg_lit by lia. unfold page_size. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Fixpoint set_kind (j : nat) (k : gkind) (gs : list (lin * lin * gkind)) : list (lin * lin * gkind) :=
  match gs, j with
  | [], _ => []
  | g :: r, O => (fst g, k) :: r
  | g :: r, Datatypes.S j' => g :: set_kind j' k r
  end.

Lemma set_kind_gden : forall E j k gs, List.map (gden E) (set_kind j k gs) = List.map (gden E) gs.
Proof. intros E j k gs. revert j. induction gs as [|g r IH]; intros [|j]; cbn [set_kind List.map]; try reflexivity; f_equal; apply IH. Qed.

Lemma set_kind_In : forall j k gs g', In g' (set_kind j k gs) -> In g' gs \/ (exists g, nth_error gs j = Some g /\ g' = (fst g, k)).
Proof.
  intros j k gs. revert j. induction gs as [|g r IH]; intros [|j] g' H; cbn [set_kind] in H; try destruct H.
  - right. exists g. split; [reflexivity | symmetry; exact H].
  - left. right. exact H.
  - left. left. exact H.
  - destruct (IH j g' H) as [H1|H1]; [left; right; exact H1 | right; exact H1].
Qed.

(* [comment removed for export] *)
Lemma set_kind_lden : forall E BL j k gs, lden_maps E BL (set_kind j k gs) = lden_maps E BL gs.
Proof.
  intros E BL j k gs. revert j. induction gs as [|g r IH]; intros [|j]; cbn [set_kind lden_maps]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma set_kind_nomark : forall j k gs, nomark (set_kind j k gs) = nomark gs.
Proof.
  intros j k gs. revert j. induction gs as [|g r IH]; intros [|j]; cbn [set_kind nomark forallb]; try reflexivity.
  fold (nomark (set_kind j k r)). fold (nomark r). rewrite (IH j). reflexivity.
Qed.
Lemma blob_ok_set_kind : forall E M M' model model' BL j k g, nth_error (sm_maps M) j = Some g -> is_mark g = false ->
  sm_maps M' = set_kind j k (sm_maps M) -> alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) ->
  blob_ok E M model BL -> blob_ok E M' model' BL.
Proof.
  intros E M M' model model' BL j k g Hj Hm HM Ht (B1 & B2 & B3). split; [unfold blob_ent_ok in *; rewrite Ht; exact B1 | split].
  - rewrite HM, set_kind_nomark. exact B2.
  - intros g' Hg' Hm'. rewrite HM in Hg'. destruct (set_kind_In j k _ g' Hg') as [Hin | (g0 & Hg0 & ->)]; [exact (B3 g' Hin Hm')|].
    rewrite Hj in Hg0. injection Hg0 as <-. unfold is_mark in Hm, Hm'. cbn [fst snd] in Hm'. rewrite Hm in Hm'. discriminate.
Qed.

Lemma set_kind_Forall : forall (P : lin * lin * gkind -> Prop) j k gs,
  Forall P gs -> (forall g, nth_error gs j = Some g -> P (fst g, k)) -> Forall P (set_kind j k gs).
Proof.
  intros P j k gs HF Hj. apply Forall_forall. intros g' Hg'. destruct (set_kind_In j k gs g' Hg') as [H1|(g & Hg & ->)].
  - rewrite Forall_forall in HF. exact (HF g' H1).
  - exact (Hj g Hg).
Qed.

Lemma set_kind_nth : forall j k gs i g', nth_error (set_kind j k gs) i = Some g' ->
  (i <> j /\ nth_error gs i = Some g') \/ (i = j /\ exists g, nth_error gs j = Some g /\ g' = (fst g, k)).
Proof.
  intros j k gs. revert j. induction gs as [|g r IH]; intros [|j] [|i] g' H; cbn [set_kind nth_error] in H; try discriminate.
  - injection H as <-. right. split; [reflexivity|]. exists g. auto.
  - left. split; [lia | exact H].
  - injection H as <-. left. split; [lia | reflexivity].
  - destruct (IH j i g' H) as [[H1 H2]|[H1 (g0 & H2 & H3)]]; [left; split; [lia | exact H2] | right; split; [lia|]; exists g0; auto].
Qed.

Lemma set_kind_Forall' : forall (P : lin * lin * gkind -> Prop) j k gs,
  (forall i g, nth_error gs i = Some g -> i <> j -> P g) -> (forall g, nth_error gs j = Some g -> P (fst g, k)) ->
  Forall P (set_kind j k gs).
Proof.
  intros P j k gs H1 H2. apply Forall_forall. intros g' Hg'. apply In_nth_error in Hg' as (i & Hi).
  destruct (set_kind_nth j k gs i g' Hi) as [[Hne Hn]|[-> (g & Hg & ->)]]; [exact (H1 i g' Hn Hne) | exact (H2 g Hg)].
Qed.

Lemma pdisj_nth : forall l i i' p q, pdisj l -> nth_error l i = Some p -> nth_error l i' = Some q -> i <> i' -> iv_disj p q.
Proof.
  induction l as [|x r IH]; intros i i' p q H Hp Hq Hne; [destruct i; discriminate|].
  destruct H as [Hx Hr]. destruct i as [|i], i' as [|i']; cbn [nth_error] in Hp, Hq; try lia.
  - injection Hp as <-. rewrite Forall_forall in Hx. exact (Hx q (nth_error_In _ _ Hq)).
  - injection Hq as <-. rewrite Forall_forall in Hx. pose proof (Hx p (nth_error_In _ _ Hp)) as Hd. unfold iv_disj in *. lia.
  - exact (IH i i' p q Hr Hp Hq ltac:(lia)).
Qed.

Definition fix_post (L : sst) (a : lin) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) a) (s_rgs L) (s_facts L) (s_next L) (s_resv L).
Definition fix_M (M : smodel) (j : nat) (k : gkind) : smodel :=
  SM (set_kind j k (sm_maps M)) (sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).

Section FixKeep.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem fix_keep_den : forall E L M ms model (a : lin) (n : Z) (na : bool) (flags : word) (j : nat) (g : lin * lin * gkind) (kd' : gkind)
    (mem0' : word -> option byte),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  lwf (s_next L) a = true ->
  nth_error (sm_maps M) j = Some g -> is_mark g = false ->
  uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g ->
  0 < n -> n mod 4096 = 0 -> uE E a mod 4096 = 0 ->
  (kd' = GE \/ (kd' = snd g /\ (na = true \/ mmap_noreserve_b flags = true))) -> kd' <> GN ->
  (forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> uE E a <= w < uE E a + n ->
      na = false /\ rg_kind R = RZ /\
      (tget (okey (w - uE E (rg_base R))) (rg_cont R) = None \/ tget (okey (w - uE E (rg_base R))) (rg_cont R) = Some (BK 0))) ->
  (mmap_noreserve_b flags = true -> forall w, uE E a <= w < uE E a + n -> page_allowedb (allowA E M) (page_base (Z_to_bv 64 w)) = true) ->
  (na = true -> forall w, uE E a <= w < uE E a + n -> in_zr (sm_zr M) w = false) ->
  eager_sum (s_facts L) (set_kind j kd' (sm_maps M)) + allow_bound (sm_allow M) <= LIMIT ->
  (* [comment removed for export] *)
  (forall w : word, ~ (uE E a <= bv_unsigned w < uE E a + n) -> mem0' w = mem0 w) ->
  (forall w, own_pt E M w -> uE E a <= bv_unsigned (Z_to_bv 64 w) < uE E a + n ->
     mem0' (Z_to_bv 64 w) = fresh_mem na (ms_mem ms) (lden E a) (Z_to_bv 64 n) (Z_to_bv 64 w)) ->
  DEN segs LIMIT model0 mem0' E (fix_post L a) (fix_M M j kd')
      (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na (lden E a) (Z_to_bv 64 n))))
      (fixed_next na flags (lden E a) (Z_to_bv 64 n) model).
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E L M ms model a n na flags j g kd' mem0' Hd Hwa Hj Hgm Hlo Hhi HnZ Hnal Hal Hkd Hkdn Hov Hallow Hnazr Hbud Hm0o Hm0i.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (av := lden E a) in *.
  set (u := uE E a) in *.
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  assert (Hgsh_j : gshape_ok E g) by (rewrite Forall_forall in Hgsh; exact (Hgsh g Hgj)).
  destruct Hgsh_j as (Hgs1 & Hgs2 & Hgs3 & Hgs4).
  assert (Hu64 : u + n <= 0x800000000000) by lia.
  assert (Hua : bv_unsigned av = u) by reflexivity.
  assert (Hu0 : 0 <= u) by (rewrite <- Hua; exact (proj1 (u_lt av))).
  assert (HnZw : bv_unsigned (Z_to_bv 64 n) = n) by (apply fg64; unfold two64; lia).
  set (model' := fixed_next na flags av (Z_to_bv 64 n) model).
  set (M' := fix_M M j kd').
  set (H := Hof E M model) in *.
  set (H' := Hof E M' model').
  assert (HA' : allowA E M' = allowA E M) by reflexivity.
  assert (Hvm' : m_vmmaps model' = _) by exact (fx_vmmaps na flags av (Z_to_bv 64 n) model).
  assert (Hlz' : m_vm_lazy model' = _) by exact (fx_lazy na flags av (Z_to_bv 64 n) model).
  assert (Hmat' : m_vm_materialized model' = _) by exact (fx_mat na flags av (Z_to_bv 64 n) model).
  assert (Hoth' := fx_other na flags av (Z_to_bv 64 n) model). cbv zeta in Hoth'.
  rewrite Hua, HnZw in Hvm', Hlz', Hmat'.
  assert (Hli : lazy_interior av (Z_to_bv 64 n) = [(av, Z_to_bv 64 n)]).
  { apply lazy_interior_aligned; rewrite ?HnZw, ?Hua; unfold page_size; try lia. }
  destruct Hivwf as [Hwna Hwlz].
  assert (Hinr : forall x, in_iv (av, Z_to_bv 64 n) x = true <-> u <= x < u + n).
  { intros x. rewrite in_iv_word, Hua, HnZw. split; intros Hx.
    - apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
    - apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  (* [comment removed for export] *)
  assert (Hcovl : forall x, covered (m_vm_lazy model') x = true -> covered (m_vm_lazy model) x = true \/ (u <= x < u + n)).
  { intros x Hx. rewrite Hlz', covered_app in Hx. apply orb_prop in Hx as [Hx|Hx].
    - right. destruct (mmap_noreserve_b flags); [|discriminate]. rewrite Hli in Hx. cbn [covered existsb] in Hx. rewrite orb_false_r in Hx.
      apply Hinr. exact Hx.
    - left. destruct (maps_subtract_sem (m_vm_lazy model) u (u + n) Hwlz ltac:(lia)) as (_ & _ & Hc). rewrite Hc in Hx.
      apply andb_prop in Hx as [Hx _]. exact Hx. }
  (* [comment removed for export] *)
  assert (Hrg : forall x, u <= x < u + n -> covered (vm_maps (m_vmmaps model)) x = true).
  { intros x Hx. rewrite Hmaps. apply (covered_In _ (gden E g)); [exact (lden_maps_in E _ _ g Hgj Hgm)|]. unfold gden. rewrite in_iv_word.
    pose proof (u_lt (lden E (fst (fst g)))). unfold gsz, uE in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  (* [comment removed for export] *)
  assert (HH' : forall w, H w = false -> (u <= bv_unsigned w < u + n -> mmap_noreserve_b flags = true -> False) -> H' w = false).
  { intros w Hw Hr. unfold H', Hof. rewrite HA', Hlz'. unfold H, Hof in Hw. unfold mkH in *.
    rewrite page_in_ranges_app. destruct (mmap_noreserve_b flags) eqn:Hnr.
    - rewrite Hli. destruct (page_in_ranges (page_base w) [(av, Z_to_bv 64 n)]) eqn:Hp1.
      + exfalso. apply page_in_one in Hp1. rewrite Hua, HnZw in Hp1. exact (Hr Hp1 eq_refl).
      + cbn [orb]. destruct (page_in_ranges (page_base w) (maps_subtract (m_vm_lazy model) u (u + n))) eqn:Hp2; [|reflexivity].
        rewrite (page_in_ms_sub _ _ _ _ Hwlz Hp2) in Hw. exact Hw.
    - cbn [app]. destruct (page_in_ranges (page_base w) (maps_subtract (m_vm_lazy model) u (u + n))) eqn:Hp2; [|reflexivity].
      rewrite (page_in_ms_sub _ _ _ _ Hwlz Hp2) in Hw. exact Hw. }
  assert (HH'r : forall w, u <= bv_unsigned w < u + n -> mmap_noreserve_b flags = true -> H' w = false).
  { intros w Hw Hnr. unfold H', Hof. rewrite HA'. apply mkH_allowed.
    pose proof (Hallow Hnr (bv_unsigned w) Hw) as Ha. rewrite Z_to_bv_bv_unsigned in Ha. exact Ha. }
  set (mem' := fresh_mem na (ms_mem ms) av (Z_to_bv 64 n)).
  (* [comment removed for export] *)
  assert (Hpt : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R ->
             mrestrict H' mem' (Z_to_bv 64 (uE E (rg_base R) + i)) = mrestrict H (ms_mem ms) (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. rewrite Forall_forall in HG0. pose proof (HG0 R HR) as HR'.
    pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff HR' i Hi) as Hv.
    destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR.
    set (w := uE E (rg_base R) + i) in *.
    assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold uE in *; lia).
    unfold mrestrict. rewrite Hv.
    destruct (Z_lt_le_dec w u) as [Hlt|Hge]; [|destruct (Z_lt_le_dec w (u + n)) as [Hlt2|Hge2]].
    - rewrite (HH' _ Hv ltac:(rewrite Hw64; lia)). apply fresh_mem_out. rewrite Hua, HnZw, Hw64. lia.
    - (* [comment removed for export] *)
      destruct (Hov R HR w ltac:(unfold w; lia) ltac:(lia)) as (Hna0 & Hk & Hc).
      assert (Hz : mrestrict H (ms_mem ms) (Z_to_bv 64 w) = Some (Z_to_bv 8 0)).
      { destruct HR' as (_ & _ & Hall & Hcont). specialize (Hall i Hi). rewrite Hk in Hall. destruct Hall as [_ Hzz].
        replace (w - uE E (rg_base R)) with i in Hc by (unfold w; lia).
        assert (Hrd : rd1 segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 w) = Some (Z_to_bv 8 0)).
        { destruct Hc as [Hc|Hc]; [exact (Hzz Hc)|].
          destruct (Hcont _ _ Hc) as [_ Hrd]. rewrite okey_pos in Hrd by lia. unfold w. exact Hrd. }
        unfold rd1 in Hrd. destruct (mrestrict H (ms_mem ms) (Z_to_bv 64 w)) as [b0|] eqn:Hm; [exact Hrd|].
        exfalso. assert (Hcm : covered (vm_maps (m_vmmaps model)) w = true) by (apply Hrg; lia).
        pose proof (Hmres w Hcm) as Hnr. rewrite Hres in Hnr.
        assert (Hfs : find_segment segs (bv_unsigned (Z_to_bv 64 w)) 1 = None).
        { destruct (find_segment segs (bv_unsigned (Z_to_bv 64 w)) 1) eqn:Hf; [|reflexivity]. exfalso.
          rewrite Hw64 in Hf. pose proof (seg_covered segs w Hsegb ltac:(unfold uE in *; lia) ltac:(rewrite Hf; discriminate)) as Hc'.
          rewrite Hnr in Hc'. discriminate. }
        rewrite (seg_rom_none segs _ Hfs) in Hrd. discriminate. }
      unfold mrestrict in Hz. rewrite Hv in Hz. rewrite Hz.
      destruct (mmap_noreserve_b flags) eqn:Hnr.
      + rewrite (HH'r _ ltac:(rewrite Hw64; lia) ltac:(first [exact Hnr | reflexivity])). unfold mem'. rewrite Hna0. apply fresh_mem_in. rewrite Hua, HnZw, Hw64. lia.
      + rewrite (HH' _ Hv ltac:(intros _ Hf; discriminate)). unfold mem'. rewrite Hna0. apply fresh_mem_in. rewrite Hua, HnZw, Hw64. lia.
    - rewrite (HH' _ Hv ltac:(rewrite Hw64; lia)). apply fresh_mem_out. rewrite Hua, HnZw, Hw64. lia. }
  (* [comment removed for export] *)
  assert (Hsden : sden segs E (fix_post L a) (restrict H' (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na av (Z_to_bv 64 n)))))).
  { rewrite (fresh_restrict H' ms na av (Z_to_bv 64 n) (s_pc L) Hpc0).
    intros E'' Ha''. cbn [fix_post s_next] in Ha''.
    destruct (Hsd E'' Ha'') as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha''), (lden_agree_wf _ E E'' _ Hb2 Ha''). split; reflexivity. }
    unfold sden0, fix_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | exact (lden_agree_wf _ E E'' a Hwa Ha'')]|].
    split; [|split; [exact HD | split; [exact HF | exact Hfrm]]].
    apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
    intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. exact (Hpt R HR' i Hi). }
  (* [comment removed for export] *)
  assert (Hhl' : m_halted model' = m_halted model) by (unfold model', m_halted; rewrite (proj1 Hoth'); reflexivity).
  assert (Htd' : m_tid model' = m_tid model) by (unfold model', m_tid; rewrite (proj1 Hoth'); reflexivity).
  assert (Hmaps' : vm_maps (m_vmmaps model') = lden_maps E (blob_of model0) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' fix_M]. rewrite set_kind_lden. exact Hmaps. }
  assert (Hblob' : blob_ok E M' model' (blob_of model0)).
  { apply (blob_ok_set_kind E M M' model model' _ j kd' g Hj Hgm eq_refl); [unfold alloc_top; rewrite Hvm'; reflexivity | exact Hblob]. }
  assert (Hgsh' : Forall (gshape_ok E) (sm_maps M')).
  { cbn [sm_maps M' fix_M]. apply set_kind_Forall; [exact Hgsh|]. intros g0 Hg0. rewrite Forall_forall in Hgsh.
    exact (Hgsh g0 (nth_error_In _ _ Hg0)). }
  assert (Hcovna : forall x, covered (vm_noaccess (m_vmmaps model')) x =
                     ((if na then in_iv (av, Z_to_bv 64 n) x else false) || (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng u (u + n) x)))%bool).
  { intros x. rewrite Hvm'. cbn [vm_noaccess]. rewrite covered_app.
    destruct (maps_subtract_sem (vm_noaccess (m_vmmaps model)) u (u + n) Hwna ltac:(lia)) as (_ & _ & Hc). rewrite Hc.
    destruct na; cbn [covered existsb]; [rewrite orb_false_r|]; reflexivity. }
  assert (Hcovlz : forall x, covered (m_vm_lazy model') x =
                     ((if mmap_noreserve_b flags then in_iv (av, Z_to_bv 64 n) x else false) || (covered (m_vm_lazy model) x && negb (in_rng u (u + n) x)))%bool).
  { intros x. rewrite Hlz', covered_app.
    destruct (maps_subtract_sem (m_vm_lazy model) u (u + n) Hwlz ltac:(lia)) as (_ & _ & Hc). rewrite Hc.
    destruct (mmap_noreserve_b flags); [rewrite Hli|]; cbn [covered existsb]; [rewrite orb_false_r|]; reflexivity. }
  assert (Hrng : forall x, in_rng u (u + n) x = true <-> u <= x < u + n).
  { intros x. unfold in_rng. split; intros Hx; [apply andb_prop in Hx as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hkind' : Forall (kind_ok E model') (sm_maps M')).
  { cbn [sm_maps M' fix_M]. apply set_kind_Forall'.
    - intros i g0 Hg0 Hij. destruct (is_mark g0) eqn:Hm0.
      { destruct (proj2 (proj2 Hblob) g0 (nth_error_In _ _ Hg0) Hm0) as [Hk0 _]. unfold kind_ok.
        split; intros Hc0; rewrite Hk0 in Hc0; [exfalso; exact (Hc0 eq_refl) | discriminate]. }
      assert (Hdis0 : iv_disj (gden E g0) (gden E g)) by (rewrite Hmaps in Hpd; exact (pdisj_lden_nth E _ _ i j g0 g Hpd Hg0 Hj Hij Hm0 Hgm)).
      rewrite Forall_forall in Hkind. split.
      2:{ intros Hgn. pose proof (proj2 (Hkind g0 (nth_error_In _ _ Hg0)) Hgn) as Hin0. rewrite Hvm'. cbn [vm_noaccess]. apply in_or_app. right.
          pose proof Hdis0 as Hdis. unfold iv_disj, B, S in Hdis. unfold gden in Hdis |- *. cbn [fst snd] in Hdis |- *.
          rewrite Forall_forall in Hgsh. destruct (Hgsh g0 (nth_error_In _ _ Hg0)) as (G1 & _ & _ & G4).
          pose proof (u_lt (lden E (fst (fst g0)))). pose proof (u_lt (lden E (fst (fst g)))). unfold gsz, uE in *.
          unfold gden in Hin0. cbn [fst snd] in Hin0.
          apply In_maps_subtract_disj; [exact Hin0 | lia | lia | lia]. }
      intros Hne x Hx. pose proof (proj1 (Hkind g0 (nth_error_In _ _ Hg0)) Hne x Hx) as Hc.
      rewrite covered_app, Hcovna, Hcovlz. rewrite covered_app in Hc.
      destruct (in_rng u (u + n) x) eqn:Hr.
      + (* [comment removed for export] *)
        exfalso. apply Hrng in Hr.
        pose proof Hdis0 as Hdis. unfold iv_disj, B, S in Hdis. unfold gden in Hdis, Hx. cbn [fst snd] in Hdis.
        rewrite in_iv_word in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        rewrite Forall_forall in Hgsh. destruct (Hgsh g0 (nth_error_In _ _ Hg0)) as (G1 & _ & _ & G4).
        pose proof (u_lt (lden E (fst (fst g0)))). pose proof (u_lt (lden E (fst (fst g)))). unfold gsz, uE in *. lia.
      + cbn [negb]. rewrite !andb_true_r. apply orb_prop in Hc as [Hc|Hc]; rewrite Hc; rewrite ?orb_true_r; reflexivity.
    - intros g0 Hg0. rewrite Hj in Hg0. injection Hg0 as <-. unfold kind_ok, gden. cbn [fst snd]. split; [|intros HGN; exfalso; exact (Hkdn HGN)].
      intros Hne x Hx.
      destruct Hkd as [->|[Hkd Hnr]]; [exfalso; exact (Hne eq_refl)|].
      rewrite covered_app, Hcovna, Hcovlz. pose proof Hkind as Hk0. rewrite Forall_forall in Hk0.
      assert (Hc : covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true).
      { apply (proj1 (Hk0 g Hgj)); [rewrite <- Hkd; exact Hne | exact Hx]. }
      rewrite covered_app in Hc. destruct (in_rng u (u + n) x) eqn:Hr.
      + apply Hrng in Hr. destruct Hnr as [Hna|Hnr]; [rewrite Hna; rewrite (proj2 (Hinr x) Hr); reflexivity|].
        rewrite Hnr, (proj2 (Hinr x) Hr), !orb_true_r. reflexivity.
      + cbn [negb]. rewrite !andb_true_r. apply orb_prop in Hc as [Hc|Hc]; rewrite Hc; rewrite ?orb_true_r; reflexivity. }
  assert (Hbud' : eager_used model' + A_bytes (AM model0 E M') <= LIMIT).
  { pose proof (eager_le E M' model' (s_facts L) _ HF0 Hmaps' Hgsh' Hkind' Hblob') as He.
    pose proof (A_bytes_allowA E M' Hanz) as Hb. unfold AM. rewrite A_bytes_app. cbn [sm_maps sm_allow M' fix_M] in He, Hb. lia. }
  assert (Hlzm' : forall x, covered (m_vm_lazy model') x = true -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hvm'. cbn [vm_maps]. destruct (Hcovl x Hx) as [H1|H1]; [exact (Hlzm x H1) | exact (Hrg x H1)]. }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false)
    by (rewrite Hvm'; exact Hmres).
  constructor.
  - exact Hsden.
  - cbn [fix_post s_next]. unfold M', fix_M, sm_wf in *. cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_own] in *.
    replace (forallb (fun g0 => (lwf (s_next L) (fst (fst g0)) && lwf (s_next L) (snd (fst g0)))%bool) (set_kind j kd' (sm_maps M))) with
            (forallb (fun g0 => (lwf (s_next L) (fst (fst g0)) && lwf (s_next L) (snd (fst g0)))%bool) (sm_maps M)); [exact Hwf|].
    clear -Hj. revert j Hj. induction (sm_maps M) as [|g0 r IH]; intros [|j'] Hj; cbn [set_kind forallb]; try reflexivity.
    f_equal. cbn in Hj. exact (IH j' Hj).
  - exact Hbw.
  - rewrite Hhl'. exact Hh.
  - exact Hawf.
  - exact Hanz.
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hmat'.
    + exact (NoDup_filter _ N1).
    + intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
    + intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
    + intros p Hp. apply filter_In in Hp as [Hp Hout]. rewrite Hlz', page_in_ranges_app.
      rewrite (page_in_ms_keep _ u (u + n) p Hwlz ltac:(lia) Hal ltac:(rewrite Z.add_mod, Hal, Hnal by lia; reflexivity) (N2 p Hp) Hout (N4 p Hp)).
      rewrite orb_true_r. reflexivity.
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
  - exact Hmaps'.
  - exact Hgsh'.
  - cbn [sm_maps M' fix_M]. apply set_kind_Forall; [rewrite Hvm'; exact Hgtop|]. intros g0 Hg0. rewrite Forall_forall in Hgtop.
    rewrite Hvm'. exact (Hgtop g0 (nth_error_In _ _ Hg0)).
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. split.
    + apply ivs_wf_app; [|exact (proj1 (maps_subtract_sem _ u (u + n) Hwna ltac:(lia)))].
      destruct na; [apply ivs_wf_cons; [|apply ivs_wf_nil] | apply ivs_wf_nil]. unfold iv_wf, B, S. cbn [fst snd]. rewrite Hua, HnZw. lia.
    + apply ivs_wf_app; [|exact (proj1 (maps_subtract_sem _ u (u + n) Hwlz ltac:(lia)))].
      destruct (mmap_noreserve_b flags); [rewrite Hli; apply ivs_wf_cons; [|apply ivs_wf_nil] | apply ivs_wf_nil].
      unfold iv_wf, B, S. cbn [fst snd]. rewrite Hua, HnZw. lia.
  - rewrite Hvm'. exact Hpd.
  - exact Hmres'.
  - exact Hkind'.
  - exact Hlzm'.
  - exact Hzrsh.
  - rewrite Hvm'. exact Hzrm.
  - intros w Hw Hout Hnow Hnb. rewrite fresh_full_mem. fold mem'. cbn [fix_post s_rgs] in Hout. cbn [sm_zr M' fix_M] in Hw.
    assert (Hnow0 : ~ own_pt E M w) by exact (own_pt_keep _ E E M M' w Hwf (agree_refl _ _) eq_refl Hnow).
    pose proof (Hzrsh w Hw) as Hws.
    assert (Hw64 : 0 <= w < two64) by (unfold in_shadow, SH_LO, SH_HI in Hws; apply andb_prop in Hws as [H1 H2];
                                        apply Z.leb_le in H1; apply Z.ltb_lt in H2; unfold two64; lia).
    destruct (Z_lt_le_dec w u) as [Hlt|Hge]; [|destruct (Z_lt_le_dec w (u + n)) as [Hlt2|Hge2]].
    + unfold mem'. rewrite fresh_mem_out by (rewrite Hua, HnZw, fg64 by exact Hw64; lia). exact (Hzr w Hw Hout Hnow0 Hnb).
    + destruct na; [rewrite (Hnazr eq_refl w ltac:(lia)) in Hw; discriminate|].
      unfold mem'. apply fresh_mem_in. rewrite Hua, HnZw, fg64 by exact Hw64. lia.
    + unfold mem'. rewrite fresh_mem_out by (rewrite Hua, HnZw, fg64 by exact Hw64; lia). exact (Hzr w Hw Hout Hnow0 Hnb).
  - rewrite Forall_forall in Hrl |- *. intros R HR. unfold rl_ok, app_pt in *. rewrite Hvm'. exact (Hrl R HR).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct Hoth' as (Hp & Hf & Hi & Hs & Hl & Ht).
    unfold model'. rewrite Hf, Hi, Hs, Hl, Ht. repeat split; assumption.
  - rewrite Htd'. destruct Hoth' as (Hp & _). unfold model'. rewrite Hp. exact Hproc.
  - assert (Hgt : uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) by (rewrite Forall_forall in Hgtop; exact (Hgtop g Hgj)).
    assert (Hat : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (unfold alloc_top; rewrite Hvm'; reflexivity).
    assert (Hfz' := frz_keep mem0 E E L (fix_post L a) M M' ms
                (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na av (Z_to_bv 64 n)))) model model' Hwf (agree_refl _ _) eq_refl Hat
                ltac:(intros w _ Ho; exact Ho)
                ltac:(intros w Hw Ho; rewrite fresh_full_mem; fold mem'; unfold mem'; rewrite fresh_mem_out; [reflexivity|];
                      rewrite Hua, HnZw, fg64 by (unfold two64; lia); lia) Hfrz).
    intros q Hq w Hw. destruct (Hfz' q Hq w Hw) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. rewrite Q3.
    symmetry. apply Hm0o. rewrite fg64 by (unfold two64; lia). rewrite Hat in Q1. lia.
  - rom_tac.
  - intros q Hq w Hw. cbn [sm_own M' fix_M] in Hq.
    assert (Hop : own_pt E M w) by (exists q; split; [exact Hq | exact Hw]).
    destruct (Hown q Hq w Hw) as [Hv Hm]. split.
    + destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) u) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) (u + n)) as [Hlt2|Hge2]].
      * apply HH'; [exact Hv | intros Hr _; lia].
      * destruct (mmap_noreserve_b flags) eqn:Hnr; [exact (HH'r (Z_to_bv 64 w) ltac:(lia) ltac:(first [exact Hnr | reflexivity]))|]. apply HH'; [exact Hv | intros _ Hf; discriminate].
      * apply HH'; [exact Hv | intros Hr _; lia].
    + intros Ho. cbn [fix_post s_rgs] in Ho. rewrite fresh_full_mem. fold mem'. unfold mem'.
      destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) u) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 w)) (u + n)) as [Hlt2|Hge2]].
      * rewrite fresh_mem_out by (rewrite Hua, HnZw; lia). rewrite (Hm Ho). symmetry. apply Hm0o. lia.
      * symmetry. exact (Hm0i w Hop ltac:(lia)).
      * rewrite fresh_mem_out by (rewrite Hua, HnZw; lia). rewrite (Hm Ho). symmetry. apply Hm0o. lia.
  - exact Hblob'.
Qed.
End FixKeep.

(* [comment removed for export] *)
Definition rgs_sep (fs : list fact) (a : lin) (n : Z) (R : region) : bool :=
  match lin_off (rg_base R) a with
  | Some d => ((Z.leb n d && Z.ltb d 1152921504606846976) ||
               match lin_off a (rg_base R) with
               | Some d' => Z.leb (snd (irange fs (rg_size R))) d' && Z.ltb d' 1152921504606846976
               | None => false
               end)%bool
  | None =>
      match lin_off a (rg_base R) with
      | Some d => (Z.leb (snd (irange fs (rg_size R))) d && Z.ltb d 1152921504606846976)%bool
      | None => (Z.leb (snd (irange fs a) + n) (fst (irange fs (rg_base R))) ||
                 Z.leb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) (fst (irange fs a)))%bool
      end
  end.
(* [comment removed for export] *)
Definition rgs_sepA (fs : list fact) (a : lin) (ar : Z * Z) (n : Z) (R : region) : bool :=
  match lin_off (rg_base R) a with
  | Some d => if (Z.leb n d && Z.ltb d 1152921504606846976)%bool then true
              else match lin_off a (rg_base R) with
                   | Some d' => (Z.leb (snd (irange fs (rg_size R))) d' && Z.ltb d' 1152921504606846976)%bool
                   | None => false
                   end
  | None =>
      match lin_off a (rg_base R) with
      | Some d => (Z.leb (snd (irange fs (rg_size R))) d && Z.ltb d 1152921504606846976)%bool
      | None => let br := irange fs (rg_base R) in
                if Z.leb (snd ar + n) (fst br) then true else Z.leb (snd br + snd (irange fs (rg_size R))) (fst ar)
      end
  end.
Lemma rgs_sepA_eq : forall fs a n R, rgs_sepA fs a (irange fs a) n R = rgs_sep fs a n R.
Proof.
  intros fs a n R. unfold rgs_sepA, rgs_sep. destruct (lin_off (rg_base R) a) as [d|].
  - destruct (Z.leb n d && Z.ltb d 1152921504606846976)%bool; reflexivity.
  - destruct (lin_off a (rg_base R)) as [d|]; [reflexivity|]. cbv zeta.
    destruct (Z.leb (snd (irange fs a) + n) (fst (irange fs (rg_base R)))); reflexivity.
Qed.
Definition zero_ov (fs : list fact) (a : lin) (n : Z) (R : region) : bool :=
  match rg_kind R with
  | RZ => let '(lo, hi) := irange fs (lsub a (rg_base R)) in
          (* [comment removed for export] *)
          Z.leb 0 lo &&& Z.leb (hi + n) (size_lo fs R) &&& range_zero (rg_cont R) lo (hi + n)
  | _ => false
  end.
Definition allow_cov (fs : list fact) (a : lin) (n : Z) (al : list (lin * Z)) : bool :=
  (* [comment removed for export] *)
  existsb_lz (fun p => contained_b fs a n (fst p) (snd p) &&& Z.leb (snd (irange fs (fst p)) + snd p) two64 &&& Z.ltb 0 n) al.
Definition zr_sep (fs : list fact) (a : lin) (n : Z) (zr : list (Z * Z)) : bool :=
  forallb (fun p => (Z.leb (snd (irange fs a) + n) (fst p) || Z.leb (snd p) (fst (irange fs a)))%bool) zr.

Lemma lin_off_u : forall E a b d, lin_off a b = Some d -> bv_unsigned (lden E b) + d < two64 ->
  bv_unsigned (lden E a) = bv_unsigned (lden E b) + d.
Proof.
  intros E a b d H Hw. destruct (lin_off_sound E a b d H) as [Hv Hd]. rewrite lden_lsub in Hv.
  assert (Ha : lden E a = bv_add (lden E b) (Z_to_bv 64 d)).
  { rewrite <- Hv. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite Z.add_mod_idemp_r by (unfold two64; lia).
    replace (bv_unsigned (lden E b) + (bv_unsigned (lden E a) - bv_unsigned (lden E b))) with (bv_unsigned (lden E a)) by lia.
    symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
  rewrite Ha, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia). apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E b)).
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *. lia.
Qed.

Lemma rgs_sep_sound : forall E fs a n R, Forall (fact_ok E) fs -> 0 <= n -> uE E a + n <= 0x800000000000 ->
  uE E (rg_base R) + rsz E R <= two64 -> rgs_sep fs a n R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n).
Proof.
  intros E fs a n R HF Hn Ha HR H w Hw Hin. unfold rgs_sep in H. pose proof (u_lt (lden E a)) as Ra. pose proof (u_lt (lden E (rg_base R))) as Rb.
  destruct (lin_off (rg_base R) a) as [d|] eqn:Hd.
  - apply orb_prop in H as [H|H].
    + apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      pose proof (lin_off_sound E _ _ _ Hd) as [_ Hdr].
      unfold uE in *. rewrite (lin_off_u E _ _ d Hd ltac:(unfold two64 in *; lia)) in Hw. lia.
    + destruct (lin_off a (rg_base R)) as [d'|] eqn:Hd'; [|discriminate].
      apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. pose proof (lin_off_sound E _ _ _ Hd') as [_ Hdr].
      pose proof (irange_sound E fs (rg_size R) HF). unfold rsz in *.
      unfold uE in *. rewrite (lin_off_u E _ _ d' Hd' ltac:(unfold two64 in *; lia)) in Hin. lia.
  - destruct (lin_off a (rg_base R)) as [d|] eqn:Hd'.
    + apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. pose proof (lin_off_sound E _ _ _ Hd') as [_ Hdr].
      pose proof (irange_sound E fs (rg_size R) HF). unfold rsz in *.
      unfold uE in *. rewrite (lin_off_u E _ _ d Hd' ltac:(unfold two64 in *; lia)) in Hin. lia.
    + pose proof (irange_sound E fs a HF). pose proof (irange_sound E fs (rg_base R) HF). pose proof (irange_sound E fs (rg_size R) HF).
      unfold rsz, uE in *. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma rgs_sepA_sound : forall E fs a n R, Forall (fact_ok E) fs -> 0 <= n -> uE E a + n <= 0x800000000000 ->
  uE E (rg_base R) + rsz E R <= two64 -> rgs_sepA fs a (irange fs a) n R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n).
Proof. intros E fs a n R HF Hn Ha HR H. rewrite rgs_sepA_eq in H. exact (rgs_sep_sound E fs a n R HF Hn Ha HR H). Qed.


Lemma zero_ov_sound : forall E fs a n R, Forall (fact_ok E) fs -> zero_ov fs a n R = true -> 0 <= n ->
  uE E (rg_base R) + rsz E R <= two64 ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> uE E a <= w < uE E a + n ->
  rg_kind R = RZ /\ (tget (okey (w - uE E (rg_base R))) (rg_cont R) = None \/ tget (okey (w - uE E (rg_base R))) (rg_cont R) = Some (BK 0)).
Proof.
  intros E fs a n R HF H Hn HRw w Hw Hin. unfold zero_ov in H. destruct (rg_kind R) eqn:Hk; try discriminate. split; [reflexivity|].
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Hr. destruct (irange fs (lsub a (rg_base R))) as [lo hi] eqn:Hir.
  cbn [fst snd] in Hr. apply andb_prop in H as [H Hz]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (size_lo_sound E fs R HF) as Hsz.
  assert (Hoff : bv_unsigned (lden E (lsub a (rg_base R))) = uE E a - uE E (rg_base R)).
  { rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. unfold uE in *.
    destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned (lden E a))) as [Hle|Hgt].
    - apply Z.mod_small. pose proof (u_lt (lden E a)). pose proof (u_lt (lden E (rg_base R))). lia.
    - exfalso. rewrite lden_lsub, bv_sub_unsigned in Hr. unfold bv_wrap, bv_modulus in Hr. change (2 ^ Z.of_N 64) with two64 in Hr.
      replace (bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R))) with ((bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R)) + two64) + (-1) * two64) in Hr by ring.
      rewrite Z_mod_plus_full, Z.mod_small in Hr by (pose proof (u_lt (lden E a)); pose proof (u_lt (lden E (rg_base R))); lia).
      pose proof (u_lt (lden E (rg_base R))). pose proof (u_lt (lden E a)). unfold rsz in *. lia. }
  destruct (tget (okey (w - uE E (rg_base R))) (rg_cont R)) as [v|] eqn:Ht; [right|left; reflexivity].
  rewrite (range_zero_spec _ lo (hi + n) _ v Hz Ht ltac:(rewrite okey_pos by lia; rewrite Hoff in Hr; lia)). reflexivity.
Qed.

Lemma allow_cov_sound : forall E fs a n al, Forall (fact_ok E) fs -> allow_cov fs a n al = true ->
  forall w, uE E a <= w < uE E a + n -> 0 <= w < two64 -> page_allowedb (List.map (allow1 E) al) (page_base (Z_to_bv 64 w)) = true.
Proof.
  intros E fs a n al HF H w Hw Hw64. unfold allow_cov in H. rewrite existsb_lz_eq in H. apply existsb_exists in H as (p & Hp & Hc).
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  pose proof (irange_sound E fs (fst p) HF) as Ir.
  destruct (contained_sound E fs a n (fst p) (snd p) HF H1 H3 ltac:(unfold uE; lia)) as [C1 C2].
  destruct (in_split _ _ Hp) as (l1 & l2 & ->). rewrite map_app. apply page_allowedb_app_r. cbn [List.map].
  change (allow1 E p :: List.map (allow1 E) l2) with ([allow1 E p] ++ List.map (allow1 E) l2). apply page_allowedb_app_l.
  apply allow1_covers; [exact Hw64|]. lia.
Qed.

Lemma zr_sep_sound : forall E fs a n zr, Forall (fact_ok E) fs -> zr_sep fs a n zr = true ->
  forall w, uE E a <= w < uE E a + n -> in_zr zr w = false.
Proof.
  intros E fs a n zr HF H w Hw. unfold zr_sep in H. pose proof (irange_sound E fs a HF) as Ir. unfold uE in Hw.
  unfold in_zr. apply not_true_iff_false. intros He. apply existsb_exists in He as (p & Hp & Hc).
  rewrite forallb_forall in H. specialize (H p Hp). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* [comment removed for export] *)
Fixpoint zr_in_grant (fs : list fact) (gs : list (lin * lin * gkind)) (j k : nat) (p : Z * Z) : bool :=
  match gs with
  | [] => false
  | g :: gs' => ((negb (Nat.eqb k j) && match is_const (fst (fst g)) with
                                         | Some b => (negb (Z.eqb b MARKB) && Z.leb b (fst p) && Z.leb (snd p) (b + gsz_lo fs g))%bool
                                         | None => false end)
                 || zr_in_grant fs gs' j (Datatypes.S k) p)%bool
  end.
Definition zr_sep_g (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (a : lin) (n : Z) (zr : list (Z * Z)) : bool :=
  forallb (fun p => (Z.leb (snd (irange fs a) + n) (fst p) || Z.leb (snd p) (fst (irange fs a)) || zr_in_grant fs gs j O p)%bool) zr.

Lemma zr_in_grant_spec : forall fs gs j k p, zr_in_grant fs gs j k p = true ->
  exists i g' b, nth_error gs i = Some g' /\ (k + i)%nat <> j /\ is_const (fst (fst g')) = Some b /\ b <= fst p /\ snd p <= b + gsz_lo fs g' /\ is_mark g' = false.
Proof.
  intros fs. induction gs as [|g gs IH]; intros j k p H; cbn [zr_in_grant] in H; [discriminate|].
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H1 H2]. apply negb_true_iff, Nat.eqb_neq in H1.
    destruct (is_const (fst (fst g))) as [b|] eqn:Hb; [|discriminate]. apply andb_prop in H2 as [H2 H3]. apply andb_prop in H2 as [H0 H2]. apply Z.leb_le in H2, H3.
    exists O, g, b. split; [reflexivity|]. split; [lia|]. split; [exact Hb|]. split; [assumption|]. split; [assumption|].
    unfold is_mark. rewrite Hb. apply negb_true_iff in H0. rewrite H0. reflexivity.
  - destruct (IH j (Datatypes.S k) p H) as (i & g' & b & Hi & Hk & Hb & H1 & H2 & H3). exists (Datatypes.S i), g', b.
    split; [exact Hi|]. split; [lia|]. split; [exact Hb|]. split; [assumption|]. split; assumption.
Qed.

Lemma zr_sep_g_sound : forall E BL fs gs j g a n zr, Forall (fact_ok E) fs ->
  pdisj (lden_maps E BL gs) -> Forall (gshape_ok E) gs -> nth_error gs j = Some g -> is_mark g = false ->
  (forall w, uE E a <= w < uE E a + n -> uE E (fst (fst g)) <= w < uE E (fst (fst g)) + gsz E g) ->
  zr_sep_g fs gs j a n zr = true -> forall w, uE E a <= w < uE E a + n -> in_zr zr w = false.
Proof.
  intros E BL fs gs j g a n zr HF Hpd Hgsh Hj Hjm Hin H w Hw. unfold zr_sep_g in H. pose proof (irange_sound E fs a HF) as Ir. unfold uE in Hw.
  unfold in_zr. apply not_true_iff_false. intros He. apply existsb_exists in He as (p & Hp & Hc).
  rewrite forallb_forall in H. specialize (H p Hp). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia|].
  destruct (zr_in_grant_spec fs gs j O p H) as (i & g' & b & Hi & Hij & Hb & H1 & H2 & Hm'). cbn [Nat.add] in Hij.
  pose proof (gsz_bounds E fs g' HF) as Gb.
  pose proof (pdisj_lden_nth E BL gs i j g' g Hpd Hi Hj Hij Hm' Hjm) as Hdj.
  rewrite Forall_forall in Hgsh. destruct (Hgsh g' (nth_error_In _ _ Hi)) as (S1 & _ & _ & S4 & _).
  destruct (Hgsh g (nth_error_In _ _ Hj)) as (T1 & _ & _ & T4 & _).
  destruct (is_const_sound E _ b Hb) as [Hbv Hbr].
  unfold iv_disj, B, S, gden in Hdj. cbn [fst snd] in Hdj. rewrite Hbv in Hdj.
  unfold uE in S4. rewrite Hbv in S4. rewrite (fg64' b Hbr) in Hdj, S4.
  specialize (Hin w Hw). unfold gsz, uE in Hin, Gb, Hdj. lia.
Qed.

Lemma region_free_of_pts : forall l (lo n : word), ivs_wf l -> Forall (fun p => 0 < bv_unsigned (snd p)) l ->
  (forall x, bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n -> covered l x = false) -> 0 < bv_unsigned n ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n Hwf Hpos H Hn; [reflexivity|]. apply ivs_wf_cons_inv in Hwf as [Hb Hl].
  inversion Hpos as [|? ? Hps Hpos']; subst. cbn [snd] in Hps.
  cbn [region_free]. apply andb_true_intro. split; [|apply IH; [exact Hl | exact Hpos' | | exact Hn]; intros x Hx; specialize (H x Hx);
    rewrite covered_cons in H; apply orb_false_iff in H as [_ H]; exact H].
  apply negb_true_iff. unfold iv_overlap. apply not_true_iff_false. intros He. apply andb_prop in He as [E1 E2].
  apply Z.ltb_lt in E1, E2.
  destruct (Z_le_gt_dec (bv_unsigned lo) (bv_unsigned b)) as [Hle|Hgt].
  - pose proof (H (bv_unsigned b) ltac:(lia)) as Hx. rewrite covered_cons in Hx. apply orb_false_iff in Hx as [Hx _].
    unfold in_iv, in_rng, B, S in Hx. cbn [fst snd] in Hx. apply andb_false_iff in Hx. destruct Hx as [Hx|Hx].
    + apply Z.leb_gt in Hx. lia.
    + apply Z.ltb_ge in Hx. lia.
  - pose proof (H (bv_unsigned lo) ltac:(lia)) as Hx. rewrite covered_cons in Hx. apply orb_false_iff in Hx as [Hx _].
    unfold in_iv, in_rng, B, S in Hx. cbn [fst snd] in Hx. apply andb_false_iff in Hx. destruct Hx as [Hx|Hx].
    + apply Z.leb_gt in Hx. lia.
    + apply Z.ltb_ge in Hx. lia.
Qed.

Lemma map_contains_intro : forall l (lo n : word) b s,
  In (b, s) l -> bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s ->
  map_contains l lo n = true.
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Definition lal_ok (a gb : lin) : bool :=
  (lal4096 a || match lin_off a gb with Some d => Z.eqb (d mod 4096) 0 | None => false end)%bool.

Lemma lal_ok_sound : forall E a gb, lal_ok a gb = true -> uE E gb mod 4096 = 0 -> uE E gb <= uE E a -> uE E a < two64 ->
  uE E a mod 4096 = 0.
Proof.
  intros E a gb H Hg Hle Hlt. unfold lal_ok in H. apply orb_prop in H as [H|H]; [exact (lal4096_sound E a H)|].
  destruct (lin_off a gb) as [d|] eqn:Hd; [|discriminate]. apply Z.eqb_eq in H.
  destruct (lin_off_sound E a gb d Hd) as [Hv Hr].
  assert (Hu : uE E (lsub a gb) = d) by (unfold uE; rewrite Hv; apply fg64'; exact Hr).
  destruct (small_diff E a gb d d ltac:(lia)) as [[Hl He]|[Hl He]]; [|lia].
  replace (uE E a) with (uE E gb + d) by lia. rewrite Z.add_mod, Hg, H by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zero_ov_inside : forall E fs a n R, Forall (fact_ok E) fs -> zero_ov fs a n R = true -> 0 < n ->
  uE E (rg_base R) + rsz E R <= two64 -> uE E (rg_base R) <= uE E a /\ uE E a + n <= uE E (rg_base R) + rsz E R.
Proof.
  intros E fs a n R HF H Hn HRw. unfold zero_ov in H. destruct (rg_kind R); try discriminate.
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Hr. destruct (irange fs (lsub a (rg_base R))) as [lo hi] eqn:Hir.
  cbn [fst snd] in Hr. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (size_lo_sound E fs R HF) as Hsz. fold (uE E (lsub a (rg_base R))) in Hr.
  destruct (small_diff E a (rg_base R) lo hi Hr) as [[Hl He]|[Hl He]]; [lia|].
  pose proof (uE_range E a). lia.
Qed.

(* [comment removed for export] *)
Definition a1r : reg := Z_to_bv 5 11.
Definition len_ok (fs : list fact) (ln : lin) (n : Z) : bool :=
  (Z.ltb 0 (fst (irange fs ln)) && Z.leb (page_round_up_Z (snd (irange fs ln))) n && Z.ltb (snd (irange fs ln)) 4611686018427387904)%bool.

Lemma pru_mono : forall x y, x <= y -> page_round_up_Z x <= page_round_up_Z y.
Proof. intros x y H. unfold page_round_up_Z, page_size. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.

Definition fixkeep_ok (LIMIT : Z) (res : list (word * word)) (L : sst) (M : smodel) (n : Z) (na : bool) (j : nat) (kd' : gkind) : bool :=
  let fs := s_facts L in let a := rget (s_regs L) (rkey a0r) in let ln := rget (s_regs L) (rkey a1r) in
  let ar := irange fs a in      (* [comment removed for export] *)
  match a7c L, arg L 2, arg L 3, arg L 5, nth_error (sm_maps M) j with
  | Some c7, Some prot, Some flags, Some off, Some g =>
      (Z.eqb c7 222 && mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) && len_ok fs ln n &&
       negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       negb (mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       (if na then mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else negb (mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
             && mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       contained_b fs a n (fst (fst g)) (gsz_lo fs g) && lal_ok a (fst (fst g)) &&
       (gkind_eqb kd' GE || (gkind_eqb kd' (snd g) && negb (gkind_eqb kd' GN) && (na || mmap_noreserve_b (Z_to_bv 64 flags)))) &&
       ((negb na &&& existsb_lz (zero_ov fs a n) (s_rgs L)) |||      (* [comment removed for export] *)
        forallb (fun R => rgs_sepA fs a ar n R ||| sep_app2_b fs (sm_maps M) j (sm_sp M) a n R ||| sep_res_b res R ||| sep_rb_b fs (sm_maps M) j (sm_sp M) a R |||
                          (negb na &&& (zero_ov fs a n R ||| zero_ov2 fs a n R))) (s_rgs L)) && Z.ltb n 4611686018427387904 &&
       (negb (mmap_noreserve_b (Z_to_bv 64 flags)) ||| allow_cov fs a n (sm_allow M)) &&      (* [comment removed for export] *)
       (negb na ||| zr_sep_g fs (sm_maps M) j a n (sm_zr M)) && lwf (s_next L) a &&
       Z.leb (eager_sum (s_facts L) (set_kind j kd' (sm_maps M)) + allow_bound (sm_allow M)) LIMIT &&
       Z.leb (eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M) + (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) LIMIT &&
       negb (is_mark g))%bool        (* [comment removed for export] *)
  | _, _, _, _, _ => false
  end.

Lemma gpr_lin : forall segs E L (msr ms : machine_state), sden segs E L msr -> ms_regs msr = ms_regs ms ->
  ms_gpr (svc_set ms) 0 = lden E (rget (s_regs L) (rkey a0r)).
Proof.
  intros segs E L msr ms Hd Hr. destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _).
  specialize (HR a0r). unfold ms_gpr. cbn [svc_set ms_regs]. rewrite <- Hr. unfold getr in HR.
  assert (Hne : bv_eqb a0r 0 = false) by reflexivity. rewrite Hne in HR. exact HR.
Qed.
Lemma gpr_lin1 : forall segs E L (msr ms : machine_state), sden segs E L msr -> ms_regs msr = ms_regs ms ->
  ms_gpr (svc_set ms) 1 = lden E (rget (s_regs L) (rkey a1r)).
Proof.
  intros segs E L msr ms Hd Hr. destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _).
  specialize (HR a1r). unfold ms_gpr. cbn [svc_set ms_regs]. rewrite <- Hr. unfold getr in HR.
  assert (Hne : bv_eqb a1r 0 = false) by reflexivity. rewrite Hne in HR. exact HR.
Qed.

Lemma length_map_ok : forall {A B} (f : A -> B) (l : list A), length (List.map f l) = length l.
Proof. intros. apply length_map. Qed.

Section FixNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved segs).
Hypothesis Hreswf : ivs_wf (segments_reserved segs).

#[using="Hsegb Hoff Hrespos Hreswf"] Theorem den_fixkeep : forall E L M ms model T n na j kd',
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_own M = [] ->
  fixkeep_ok LIMIT (segments_reserved segs) L M n na j kd' = true ->
  (forall ms' model', DEN segs LIMIT model0 mem0 E (fix_post L (rget (s_regs L) (rkey a0r))) (fix_M M j kd') ms' model' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T n na j kd' Hd Hon Hok Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  unfold fixkeep_ok in Hok. set (a := rget (s_regs L) (rkey a0r)) in *. set (ln := rget (s_regs L) (rkey a1r)) in *.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate].
  destruct (arg L 2) as [prot|] eqn:H2; [|discriminate]. destruct (arg L 3) as [flags|] eqn:H3; [|discriminate].
  destruct (arg L 5) as [off|] eqn:H5; [|discriminate]. destruct (nth_error (sm_maps M) j) as [g|] eqn:Hj; [|discriminate].
  apply andb_prop in Hok as [Hok Hgm]. apply negb_true_iff in Hgm.
  apply andb_prop in Hok as [Hok Hbc]. apply Z.leb_le in Hbc. apply andb_prop in Hok as [Hok Hbud]. apply Z.leb_le in Hbud.
  apply andb_prop in Hok as [Hok Hwa]. apply andb_prop in Hok as [Hok Hzrc]. apply andb_prop in Hok as [Hok Halc].
  apply andb_prop in Hok as [Hok Hnbig]. apply Z.ltb_lt in Hnbig.
  apply andb_prop in Hok as [Hok Hrgc]. apply andb_prop in Hok as [Hok Hkdc]. apply andb_prop in Hok as [Hok Hdal].
  apply andb_prop in Hok as [Hok Hdc]. apply andb_prop in Hok as [Hok Hsel].
  apply andb_prop in Hok as [Hok Hnac]. apply andb_prop in Hok as [Hok Hmod]. apply andb_prop in Hok as [Hok Hlok].
  apply andb_prop in Hok as [Hok Hanon]. apply andb_prop in Hok as [Hc7 Hoffa]. apply Z.eqb_eq in Hc7. subst c7.
  apply negb_true_iff in Hmod, Hnac.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg0 : ms_gpr ms1 0 = lden E a) by exact (gpr_lin segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg1 : ms_gpr ms1 1 = lden E ln) by exact (gpr_lin1 segs E L (restrict H ms) ms Hsd eq_refl).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & HFl & _).
  unfold len_ok in Hlok. apply andb_prop in Hlok as [Hlok Hl3]. apply andb_prop in Hlok as [Hl1 Hl2].
  apply Z.ltb_lt in Hl1, Hl3. apply Z.leb_le in Hl2. pose proof (irange_sound E _ ln HFl) as Rln.
  set (len := lden E ln) in *.
  assert (Hnz0 : w_is0 len = false) by (unfold w_is0, bv_eqb; apply Z.eqb_neq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
  set (n0 := page_round_up_Z (bv_unsigned len)).
  assert (HnZ : page_round_up_Z (bv_unsigned len) = n0) by reflexivity.
  assert (HnZpos : 0 < n0) by (rewrite <- HnZ; exact (len_nZ_pos _ Hnz0)).
  assert (HnZal : n0 mod 4096 = 0) by (rewrite <- HnZ; exact (page_round_up_Z_aligned' _)).
  assert (Hn0n : n0 <= n) by (pose proof (pru_mono _ _ (proj2 Rln)); unfold n0; lia).
  assert (Hnpos : 0 < n) by lia.
  assert (Hgj : In g (sm_maps M)) by exact (nth_error_In _ _ Hj).
  pose proof Hgsh as Hgsh0. rewrite Forall_forall in Hgsh0. destruct (Hgsh0 g Hgj) as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5).
  pose proof Hgtop as Hgtop0. rewrite Forall_forall in Hgtop0. pose proof (Hgtop0 g Hgj) as Gt.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & _ & _ & _ & HG0 & HD0 & HF0 & _).
  pose proof (gsz_bounds E (s_facts L) g HF0) as Gb. pose proof (gsz_lo_nonneg (s_facts L) g) as Gb0.
  destruct (contained_sound E (s_facts L) a n (fst (fst g)) (gsz_lo (s_facts L) g) HF0 Hdc Hnpos ltac:(unfold uE, two64 in *; lia)) as [Hlo Hhi0].
  assert (Hhi : uE E a + n <= uE E (fst (fst g)) + gsz E g) by lia.
  assert (Hal : uE E a mod 4096 = 0) by (apply (lal_ok_sound E a (fst (fst g)) Hdal Gs3 Hlo); unfold uE, two64 in *; lia).
  assert (Hov : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> uE E a <= w < uE E a + n ->
      na = false /\ rg_kind R = RZ /\
      (tget (okey (w - uE E (rg_base R))) (rg_cont R) = None \/ tget (okey (w - uE E (rg_base R))) (rg_cont R) = Some (BK 0))).
  { intros R HR w Hw Hin. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (_ & HRw & _).
    apply orb_prop in Hrgc as [Hrgc|Hrgc].
    - (* [comment removed for export] *)
      apply andb_prop in Hrgc as [Hn0 Hex]. apply negb_true_iff in Hn0. rewrite existsb_lz_eq in Hex. apply existsb_exists in Hex as (R0 & HR0 & Hz0).
      destruct (HG0 R0 HR0) as (_ & HR0w & _).
      destruct (zero_ov_inside E (s_facts L) a n R0 HF0 Hz0 Hnpos HR0w) as [I1 I2].
      destruct (In_nth_error _ _ HR) as [i Hi]. destruct (In_nth_error _ _ HR0) as [i0 Hi0].
      destruct (Nat.eq_dec i i0) as [->|Hne].
      + rewrite Hi in Hi0. injection Hi0 as ->. split; [exact Hn0|].
        exact (zero_ov_sound E (s_facts L) a n R0 HF0 Hz0 ltac:(lia) HR0w w Hw Hin).
      + exfalso. pose proof (rgs_disj_nth E (s_rgs L) i i0 R R0 HD0 Hne Hi Hi0) as Hdj. unfold rg_disj in Hdj. unfold uE in *. lia.
    - rewrite forallb_forall in Hrgc. pose proof (Hrgc R HR) as Hc.
      apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|]; [apply orb_prop in Hc as [Hc|Hc]| |];
        [apply orb_prop in Hc as [Hc|Hc]| | |].
      + exfalso. apply (rgs_sepA_sound E (s_facts L) a n R HF0 ltac:(lia) ltac:(unfold uE in *; lia) HRw Hc w Hw Hin).
      + exfalso. destruct (HG0 R HR) as (HRs & _ & _).
        exact (sep_app2_sound E (s_facts L) (sm_maps M) model (sm_sp M) _ HF0 Hmaps Hpd Hgsh Hgtop Hsp (proj2 Hspok)
                 j g a n R Hj Hgm Hlo Hhi ltac:(unfold two64; lia) HRs HRw Hc w Hw Hin).
      + exfalso. rewrite <- Hres in Hc.
        exact (sep_res_sound E (sm_maps M) model _ Hmaps Hgsh Hmres j g a n R Hj Hgm Hlo Hhi Hc w Hw Hin).
      + exfalso. destruct (HG0 R HR) as (HRs & _ & _).
        exact (sep_rb_sound E (s_facts L) (sm_maps M) model (sm_sp M) HF0 Hgsh Hgtop Hsp (proj2 Hspok) j a n R HRs HRw Hc w Hw Hin).
      + apply andb_prop in Hc as [Hn0 Hz]. apply negb_true_iff in Hn0. split; [exact Hn0|].
        apply orb_prop in Hz as [Hz|Hz].
        * exact (zero_ov_sound E (s_facts L) a n R HF0 Hz ltac:(lia) HRw w Hw Hin).
        * exact (zero_ov2_sound E (s_facts L) a n R HF0 Hz ltac:(lia) HRw w Hw Hin). }
  assert (Hallow : mmap_noreserve_b (Z_to_bv 64 flags) = true -> forall w, uE E a <= w < uE E a + n ->
                     page_allowedb (allowA E M) (page_base (Z_to_bv 64 w)) = true).
  { intros Hnr w Hw. rewrite Hnr in Halc. cbn in Halc. apply (allow_cov_sound E (s_facts L) a n _ HF0 Halc w Hw).
    pose proof (u_lt (lden E a)). unfold uE, two64 in *. lia. }
  assert (Hnazr : na = true -> forall w, uE E a <= w < uE E a + n -> in_zr (sm_zr M) w = false).
  { intros Hna w Hw. rewrite Hna in Hzrc. cbn in Hzrc. rewrite Hmaps in Hpd.
    exact (zr_sep_g_sound E _ (s_facts L) (sm_maps M) j g a n _ HF0 Hpd Hgsh Hj Hgm (fun w' Hw' => ltac:(lia)) Hzrc w Hw). }
  assert (Hkd : kd' = GE \/ (kd' = snd g /\ (na = true \/ mmap_noreserve_b (Z_to_bv 64 flags) = true))).
  { apply orb_prop in Hkdc as [Hkdc|Hkdc]; [left; destruct kd'; try discriminate; reflexivity|]. right.
    apply andb_prop in Hkdc as [Hk1 Hk2]. apply andb_prop in Hk1 as [Hk1 _]. split; [destruct kd', (snd g); try discriminate; reflexivity|].
    apply orb_prop in Hk2 as [Hk2|Hk2]; [left; exact Hk2 | right; exact Hk2]. }
  assert (Hkdn : kd' <> GN).
  { intros ->. apply orb_prop in Hkdc as [Hkdc|Hkdc]; [discriminate|]. apply andb_prop in Hkdc as [Hk1 _]. apply andb_prop in Hk1 as [_ Hk1].
    discriminate. }
  pose proof (fix_keep_den segs LIMIT model0 mem0 Hsegb E L M ms model a n0 na (Z_to_bv 64 flags) j g kd' mem0 Hd Hwa Hj Hgm
                ltac:(lia) ltac:(lia) HnZpos HnZal Hal Hkd Hkdn
                (fun R HR w Hw Hin => Hov R HR w Hw ltac:(lia))
                (fun Hnr w Hw => Hallow Hnr w ltac:(lia))
                (fun Hna w Hw => Hnazr Hna w ltac:(lia)) Hbud
                (fun w _ => eq_refl) (fun w Hop _ => False_ind _ (own_pt_nil E M w Hon Hop))) as HD'.
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  (* [comment removed for export] *)
  assert (HuA : bv_unsigned (lden E a) = uE E a) by reflexivity.
  assert (Htop : uE E a + n0 <= alloc_top (m_vmmaps model)) by lia.
  assert (Hgate : fixed_gate model (lden E a) len).
  { unfold fixed_gate, page_size. rewrite HuA, HnZ. repeat split; lia. }
  assert (HnZw : bv_unsigned (Z_to_bv 64 n0) = n0) by (apply fg64; pose proof (u_lt (lden E a)); unfold uE, two64 in *; lia).
  assert (Hcm : forall x, uE E a <= x < uE E a + n0 -> covered (vm_maps (m_vmmaps model)) x = true).
  { intros x Hx. rewrite Hmaps. apply (covered_In _ (gden E g)); [exact (lden_maps_in E _ _ g Hgj Hgm)|]. unfold gden. rewrite in_iv_word.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold gsz, uE in *; lia. }
  assert (Hctn : (region_free (vm_reserved (m_vmmaps model)) (lden E a) (Z_to_bv 64 n0)
                  && map_contains (vm_maps (m_vmmaps model)) (lden E a) (Z_to_bv 64 n0))%bool = true).
  { apply andb_true_intro. split.
    - rewrite Hres. apply region_free_of_pts; [exact Hreswf | exact Hrespos | | rewrite HnZw; exact HnZpos].
      intros x Hx. rewrite HnZw, HuA in Hx. rewrite <- Hres. exact (Hmres x (Hcm x Hx)).
    - rewrite Hmaps. apply (map_contains_intro _ _ _ (fst (gden E g)) (snd (gden E g))); [rewrite <- surjective_pairing; exact (lden_maps_in E _ _ g Hgj Hgm) | |].
      + unfold gden. cbn [fst]. unfold uE in *. lia.
      + unfold gden. cbn [fst snd]. rewrite HnZw, HuA. unfold gsz, uE in *. lia. }
  rewrite <- HnZ in Hctn.
  destruct na.
  - assert (Hbr := branch_fixed_na_contained segs ms1 (ms_reg ms 17) model Hno).
    rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr, Hctn.
    specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hsel Hgate Hctn).
    eapply rzc_silent1; [|exact (Hk _ _ HD')].
    exact (node_mmap_fixed_na_contained segs cfg Hoff ms1 model (ms_reg ms 17) (lden E a) (Z_to_bv 64 n0) (Z_to_bv 64 flags) Hh Hsvc Hno
             ltac:(rewrite HuA; lia) Hbr).
  - apply andb_prop in Hsel as [Hsel1 Hsel2]. apply negb_true_iff in Hsel1.
    assert (Hbr := branch_fixed_rw_contained segs ms1 (ms_reg ms 17) model Hno).
    rewrite ?Hg0, ?Hg1, ?Hg2, ?Hg3, ?Hg5 in Hbr. rewrite HnZ in Hbr, Hctn.
    specialize (Hbr Hoffa Hanon Hnz0 Hmod Hnac Hsel1 Hsel2 Hgate Hctn).
    eapply rzc_silent1; [|exact (Hk _ _ HD')].
    apply (node_mmap_fixed_rw_contained segs cfg Hoff ms1 model (ms_reg ms 17) (lden E a) (Z_to_bv 64 n0) (Z_to_bv 64 flags) Hh Hsvc Hno
             ltac:(rewrite HuA; lia) Hbr).
    (* [comment removed for export] *)
    assert (Hmw : model_ivs_wf model).
    { split; [rewrite Hmaps; exact (ivs_wf_lden E model _ _ Hgsh (proj1 Hblob))|]. split; [exact (proj1 Hivwf)|]. split; [exact (proj2 Hivwf) | exact (proj1 Hspok)]. }
    assert (Hvb : vm_backing_used model <= eager_sum (s_facts L) (sm_maps M) + allow_bound (sm_allow M))
      by exact (den_backing_le segs LIMIT model0 mem0 E L M ms model (s_facts L) Hd HF0).
    pose proof (mark_len_nonneg (s_facts L) (sm_maps M)) as Hmn0.
    assert (Hprod : 0 <= (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (mmap_noreserve_b (Z_to_bv 64 flags)) eqn:Hnr.
    + pose proof (u_lt (lden E a)) as Ra.
      apply mmap_fixed_rw_budget_ok_recommit_intro; [exact Hnr | exact Hmw | | | | |]; unfold page_size; rewrite ?HuA, ?HnZw.
      * exact Hal.
      * exact HnZal.
      * exact HnZpos.
      * unfold uE, two64 in *. change (2 ^ 64) with 18446744073709551616. lia.
      * rewrite Hlim. lia.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [exact Hnr | exact Hmw|]. rewrite Hlim.
      assert (Hov' : overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned (lden E a)) (bv_unsigned (lden E a) + bv_unsigned (Z_to_bv 64 n0))
                     <= Z.of_nat (length (vm_maps (m_vmmaps model))) * n0).
      { rewrite HnZw. clear -HnZpos. induction (vm_maps (m_vmmaps model)) as [|g0 r IH]; [unfold overlap_sum; cbn; lia|].
        cbn [length]. rewrite overlap_sum_cons. pose proof (iv_count_in_rng_le g0 (bv_unsigned (lden E a)) (bv_unsigned (lden E a) + n0) ltac:(lia)).
        lia. }
      destruct (ledger_lden_bounds E model (s_facts L) _ _ HF0 Hgsh (proj1 Hblob) (proj2 (proj2 Hblob))) as [_ Hln]. rewrite <- Hmaps in Hln.
      pose proof (mark_len_nonneg (s_facts L) (sm_maps M)) as Hmn.
      assert (Z.of_nat (length (vm_maps (m_vmmaps model))) * n0 <= (Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * n) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
Qed.
End FixNode.
