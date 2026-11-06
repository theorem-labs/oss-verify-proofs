(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv AllocTop VmKit MmNodes GapGrid KLink.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RelSpec RefNodes HeapCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).
Ltac kb_open K :=
  pose proof (kb_minv _ _ _ K) as Kminv; pose proof (kb_halt _ _ _ K) as Khalt; pose proof (kb_wf _ _ _ K) as Kwf; pose proof (kb_nawf _ _ _ K) as Knwf;
  pose proof (kb_resv _ _ _ K) as Kresv; pose proof (kb_top _ _ _ K) as Ktop; pose proof (kb_hceil _ _ _ K) as Khc; pose proof (kb_resv_top _ _ _ K) as Krtop; pose proof (kb_resv_wf _ _ _ K) as Krwf; pose proof (kb_resv_n _ _ _ K) as Krn;
  pose proof (kb_start _ _ _ K) as Kstart;
  pose proof (kb_groups _ _ _ K) as Kgrp; pose proof (kb_metas _ _ _ K) as Kmet; pose proof (kb_distinct _ _ _ K) as Kdis;
  pose proof (kb_brkreg _ _ _ K) as Kbreg; pose proof (kb_phase _ _ _ K) as Kph;
  pose proof (kb_live _ _ _ K) as Klive; pose proof (kb_count _ _ _ K) as Kcnt; pose proof (kb_limit _ _ _ K) as Klim.

Section HC.
Context {HC : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_above : forall maps aw nw, (forall e, In e maps -> ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma iv_subtract_ehi : forall a sz lo hi e,
  bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= lo -> hi <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> ehi e <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi e Hwf Hlo Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_ehi : forall maps lo hi e,
  (forall e0, In e0 maps -> ehi e0 <= 2^64) -> 0 <= lo -> hi <= 2^64 ->
  In e (maps_subtract maps lo hi) -> ehi e <= 2^64.
Proof.
  intros maps lo hi e Hwf Hlo Hhi Hin. destruct (maps_subtract_In _ _ _ _ Hin) as ([a sz] & H0 & H1).
  pose proof (Hwf _ H0) as W. unfold ehi in W. cbn in W.
  pose proof (iv_subtract_ehi a sz lo hi e W Hlo Hhi H1). lia.
Qed.

Lemma ev_mmap_fixed_ok : forall L G s0 cur cb ck, frame_ok G -> ld_brk L = BPGuard cur -> 0 <= cb -> 0 <= ck ->
  let a := round_up_pg cur in
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (ev_step (EMmap a PGSZ PROT_NONE MAPFX))
        (ev_step_post L (EMmap a PGSZ PROT_NONE MAPFX) G s0 cb ck).
Proof.
  intros L G s0 cur cb ck HG Hph Hcb Hck a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KLB L' (ps_brk s0) mo /\ x = FxDone /\ BUD L' mo cb ck)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (aw := MmNodes.wz a). set (nw := MmNodes.wz PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hrf : region_free (vm_reserved (m_vmmaps mo)) aw nw = true).
    { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kb_resv_top _ _ _ HK). exact He. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (SF : mmsafe (NMmap a PGSZ PROT_NONE MAPFX) mo).
    { cbn. right. change (pgup PGSZ) with PGSZ. fold aw nw. splits; auto;
        first [rewrite Ha, Ecur; exact S2 | unfold PGSZ in *; lia]. }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_mmap_fixed_iff mo) in Hst; [| exact MI| exact SF]. destruct Hst as (_ & -> & ->).
    change (pgup PGSZ) with PGSZ. fold aw nw.
    exists FxDone. split.
    { unfold dec_mmap_fixed. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. change (mmap_len PGSZ) with PGSZ. fold aw nw.
      subst aw nw. unfold MmNodes.wz. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (HK' : KLB L' (ps_brk s0) (mmap_fx_model mo a PGSZ)).
    { subst L'. unfold mmap_fx_model. fold aw nw.
      kb_open HK. constructor; rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - intros e [<-|He]; [rewrite ehi_pair, Ua, Un; lia|]. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: lia.
      - intros b0 l0 Hin. pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgrp b0 l0 Hin). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. exists e0. split; [exact He0|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
      - unfold vm_live_bytes in *. cbn [vm_maps]. rewrite Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]. rewrite Hph. reflexivity.
      - rewrite Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]. rewrite Hph. unfold PGSZ. reflexivity. }
    splits; auto.
    destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD. unfold mmap_fx_model. rewrite with_vmmaps_vmmaps. cbn [vm_limit].
    assert (E1 : ltotal L' = ltotal L) by (subst L'; unfold ltotal, lbrk_bytes; cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]; rewrite Hph; reflexivity).
    assert (E2 : lcount L' = lcount L) by (subst L'; unfold lcount, lbrk_cnt; cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]; rewrite Hph; unfold PGSZ; reflexivity).
    rewrite E1, E2. splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & -> & HB). unfold ev_step_post, ans_cont, ev_costb, ev_costk, ev_fixed.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb]. cbv iota. fold L'.
  rewrite !Z.sub_0_r. splits; auto. unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma phase_quiet : forall L L' pbrk mo mo',
  KLB L pbrk mo -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  phase_inv (ld_brk L') L' pbrk mo'.
Proof.
  intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kb_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

Lemma ev_munmap_ok : forall L G s0 a l0 len cb ck, frame_ok G -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) -> 0 <= cb -> 0 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (ev_step (EMunmap a len))
        (ev_step_post L (EMunmap a len) G s0 cb ck).
Proof.
  intros L G s0 a l0 len cb ck HG Hq Hin Hlen Hcb Hck. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite <- mmap_len_round_up in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KLB L' (ps_brk s0) mo /\ x = RgDone true /\ BUD L' mo cb ck)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l0) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Hhas : map_has (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, KInv.wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    assert (SF : mmsafe (NMunmap a len) mo).
    { cbn. change (pgup len) with (mmap_len len). rewrite Hlen2, TASK_SIZE_val. unfold MmNodes.wz. fold aw nw. splits; auto; try lia; unfold PGSZ in A3; exact A3. }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_munmap_iff mo) in Hst; [| exact MI| exact SF]. destruct Hst as (_ & -> & ->).
    change (pgup len) with (mmap_len len). rewrite Hlen2. unfold MmNodes.wz. fold aw nw.
    exists (RgDone true). split.
    { unfold dec_munmap. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite Hlen2. fold aw nw.
      rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. rewrite !bv_eqb_refl. reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (kb_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kb_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + n) by lia.
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. unfold KInv.wz in E. rewrite unsigned_lit, Ua in E by lia. exact E. }
    assert (HK' : KLB L' (ps_brk s0) (munmap_model mo a n)).
    { unfold munmap_model. unfold MmNodes.wz. fold aw.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) (munmap_model mo a n)) by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]).
      unfold munmap_model in Hph'. unfold MmNodes.wz in Hph'. fold aw in Hph'.
      subst L'. kb_open HK. constructor; try exact Hph'; rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - apply vmwf_remove. exact Kwf.
      - intros e He. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: lia.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgrp b0 l1 Hin1). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        unfold map_remove. apply filter_In. split; [exact G5|]. destruct (bv_eqb _ aw) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
        apply (Kfst b0 l1 Hne ltac:(pose proof (mmap_len_ge l1 G0); lia)). exact E.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kmet b0 l1 k Hin0). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + unfold map_remove. apply filter_In. split; [exact G7|]. destruct (bv_eqb _ aw) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
          apply (Kfst b0 l1 Hne ltac:(pose proof (mmap_len_ge l1 G0); lia)). exact E.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kbreg b0 l1 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr].
        unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:Efst; [|reflexivity]. exfalso. apply bv_eqb_eq in Efst.
        unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold KInv.wz in D. fold aw nw in D. rewrite Un in D. lia.
      - unfold vm_live_bytes in *. destruct (live_bytes_remove (vm_maps (m_vmmaps mo)) aw nw Kwf A5) as [-> _]. rewrite Klive, Un.
        unfold ltotal. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !sum_glen_app, sum_glen_cons. fold n.
        unfold lbrk_bytes. cbn [ld_brk ld_brkreg set_groups]. lia.
      - destruct (live_bytes_remove (vm_maps (m_vmmaps mo)) aw nw Kwf A5) as [_ ->].
        assert (LP : (1 <= length (vm_maps (m_vmmaps mo)))%nat) by (destruct (vm_maps (m_vmmaps mo)); [destruct A5| cbn; lia]).
        rewrite Nat2Z.inj_sub, Kcnt by exact LP. unfold lcount. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !app_length. cbn [length].
        unfold lbrk_cnt. cbn [ld_brk ld_brkreg set_groups]. lia. }
    splits; auto.
    destruct HB as (Q0 & Q1 & Q2 & Q3 & Q4). unfold BUD. unfold munmap_model. rewrite with_vmmaps_vmmaps. cbn [vm_limit].
    assert (E1 : ltotal L' <= ltotal L).
    { subst L'. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg ld_groups ld_metas set_groups]. rewrite Ezz.
      replace (sum_glen (ld_groups L)) with (sum_glen (g1 ++ (a, l0) :: g2)) by (rewrite <- Eg; reflexivity).
      rewrite !sum_glen_app, sum_glen_cons. pose proof (mmap_len_ge l0 ltac:(lia)). lia. }
    assert (E2 : lcount L' <= lcount L).
    { subst L'. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg ld_groups ld_metas set_groups]. rewrite Ezz.
      replace (length (ld_groups L)) with (length (g1 ++ (a, l0) :: g2)) by (rewrite <- Eg; reflexivity).
      rewrite !app_length. cbn [length]. lia. }
    splits; auto; lia. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & -> & HB). unfold ev_step_post, ans_cont, ev_costb, ev_costk.
  cbn [answer_ok event_post]. fold L'. rewrite !Z.sub_0_r.
  splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

Lemma ev_mprotect_ok : forall L G s0 b l k cb ck, frame_ok G -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l -> 0 <= cb -> 0 <= ck ->
  let a := b + (1 + k) * PGSZ in
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (ev_step (EMprotect a PGSZ PROT_RW))
        (ev_step_post L (EMprotect a PGSZ PROT_RW) G s0 cb ck).
Proof.
  intros L G s0 b l k cb ck HG Hq Hin Hk2 Hcb Hck a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite <- mmap_len_round_up in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KLB L' (ps_brk s0) mo /\ x = RgDone true /\ BUD L' mo cb ck)).
    intros s mo (-> & HK & HGs & HB). pose proof HB as (Q0 & Q1 & Q2 & Q3 & Q4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    pose proof (kb_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (SF : mmsafe (NMprotect a PGSZ PROT_RW) mo).
    { cbn. change (pgup PGSZ) with PGSZ. unfold MmNodes.wz. fold aw nw. splits; auto; try (unfold PGSZ in *; lia). }
    split; [exact SF|].
    assert (BOK : mprotect_budget_ok mo aw nw = true).
    { apply mprotect_budget_ok_intro; [exact (proj1 MI)| exact (proj2 MI)|]. rewrite (kb_live _ _ _ HK). unfold BUDCAP in *. lia. }
    intros rsp mo' evs Hst.
    apply (nstep_mprotect_iff mo) in Hst; [| exact SF]. change (pgup PGSZ) with PGSZ in Hst. unfold MmNodes.wz in Hst. fold aw nw in Hst.
    destruct Hst as (_ & [(He & _ & _)|(_ & -> & ->)]).
    { exfalso. rewrite BOK in He. discriminate He. }
    exists (RgDone true). split.
    { unfold dec_mprotect_rw, dec_mprotect. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. change (mmap_len PGSZ) with PGSZ. fold aw nw.
      rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. rewrite !bv_eqb_refl. reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (kb_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kb_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (HK' : KLB L' (ps_brk s0) (MmNodes.mprotect_model mo a PGSZ)).
    { unfold MmNodes.mprotect_model.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) (MmNodes.mprotect_model mo a PGSZ)) by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]).
      unfold MmNodes.mprotect_model in Hph'.
      subst L'. kb_open HK. constructor; try exact Hph'; rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - intros e He. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: unfold PGSZ in *; lia.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kmet b1 l1 k0 Hin1). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q * PGSZ) (b + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(right; subst a; clear -Hq1; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          assert (D : b0 + mmap_len l0 <= b \/ b + nb <= b0).
          { destruct (Z.eq_dec b0 b) as [->|Hne].
            { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
            exact (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne). }
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hab Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      - rewrite map_base_bump. exact Kdis.
      - unfold vm_live_bytes in *. rewrite Klive. unfold ltotal. cbn [ld_groups ld_metas set_metas]. rewrite sum_mlen_bump. unfold lbrk_bytes. cbn [ld_brk ld_brkreg set_metas]. reflexivity.
      - rewrite Kcnt. unfold lcount. cbn [ld_groups ld_metas set_metas]. rewrite length_bump. unfold lbrk_cnt. cbn [ld_brk ld_brkreg set_metas]. reflexivity. }
    splits; auto.
    unfold BUD. unfold MmNodes.mprotect_model. rewrite with_vmmaps_vmmaps. cbn [vm_limit].
    assert (E1 : ltotal L' = ltotal L) by (subst L'; unfold ltotal, lbrk_bytes; cbn [ld_brk ld_brkreg ld_groups ld_metas set_metas]; rewrite sum_mlen_bump; reflexivity).
    assert (E2 : lcount L' = lcount L) by (subst L'; unfold lcount, lbrk_cnt; cbn [ld_brk ld_brkreg ld_groups ld_metas set_metas]; rewrite length_bump; reflexivity).
    rewrite E1, E2. splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & -> & HB). unfold ev_step_post, ans_cont, ev_costb, ev_costk.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok. cbn [Z.eqb orb]. rewrite !Z.sub_0_r. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_step_spec : forall L e (G : PState -> Model -> Prop) s0 cb ck,
  frame_ok G -> event_pre L e -> ev_costb e <= cb -> ev_costk e <= ck -> 0 <= cb -> 0 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck) (ev_step e) (ev_step_post L e G s0 cb ck).
Proof.
  intros L e G s0 cb ck HG Hpre Hcb Hck Hcb0 Hck0.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - cbn [ev_costb ev_costk] in Hcb, Hck.
    destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
    + unfold ev_step. cbn [Z.eqb]. apply ev_brk0_ok; assumption.
    + destruct (Z.eqb_spec (round_up_pg cur + 2 * PGSZ) 0) as [E|NE].
      * intros s mo (-> & HK & _). exfalso. pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & _).
        pose proof (kb_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow1_ok; try assumption; revert Hcb Hck; cbn; rewrite ?(proj2 (Z.eqb_neq _ _) NE); intros; assumption.
    + destruct (Z.eqb_spec (b + l + PGSZ) 0) as [E|NE].
      * intros s mo (-> & HK & _). exfalso. pose proof (kb_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow2_ok; try assumption; revert Hcb Hck; cbn; rewrite ?(proj2 (Z.eqb_neq _ _) NE); intros; assumption.
  - cbn [ev_costb ev_costk] in Hcb, Hck.
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + change (ev_fixed MAPF) with false in Hcb, Hck. cbv iota in Hcb, Hck. apply ev_mmap_ok; assumption.
    + apply ev_mmap_fixed_ok; assumption.
  - destruct Hpre as (Hq & l0 & Hin & Hlen). apply (ev_munmap_ok L G s0 addr l0 len); assumption.
  - destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). apply (ev_mprotect_ok L G s0 b l k); assumption.
Qed.

(* [comment removed for export] *)
Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop) (G : PState -> Model -> Prop) L s0 cb ck,
  frame_ok G -> ctree_ok L t Post -> tbound t cb ck P -> 0 <= cb -> 0 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ P r /\ KLB L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0 /\ BUD L' mo 0 0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post P G L s0 cb ck HG Hok TB Hcb Hck.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs & HB). exists L.
    split; [constructor|]. cbn in Hok, TB. splits; auto. eapply BUD_mono; [exact HB| lia| lia].
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk]. cbn in TB. destruct TB as (TB1 & TB2 & TBk).
    eapply mspec_bind; [apply (ev_step_spec L e G s0 cb ck HG Hpre TB1 TB2 Hcb Hck)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & Hcont & HK1 & HG1 & Hm & Hfa & Hso & HB1).
    pose proof HB1 as (B0 & B1 & _).
    eapply mspec_conseq; [apply (IH z Post P G (event_post L e z) s1 _ _ HG (Hk z Hans) (TBk z Hcont) B0 B1)| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HPr & HK & HG' & Hm' & Hfa' & Hso' & HB'). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.
End HC.
