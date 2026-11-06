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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_live MallocInv_repw MallocInv_getmeta MallocInv_env MallocIface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gextent (mt : meta_rec) : Z := 16 + mt_cnt mt * mt_stride mt.
Definition glvl (mt : meta_rec) : Z := Z.log2 (gextent mt / 48).
(* [comment removed for export] *)
Definition nfuel (mt : meta_rec) : nat := if 0 <? mt_maplen mt then 1%nat else Z.to_nat (7 - glvl mt).

Section Depth.
  Variable A : astate.
  Hypothesis HW : WF A.

  Lemma nested_extent : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    mt_maplen mt = 0 -> 48 <= gextent mt <= 2048.
  Proof.
    intros ma mt aib slots Hma Hr Hml.
    destruct (wf_nested_small A HW ma mt aib slots Hma Hr Hml) as [Hl Hs].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32 & _ & Hsc & _).
    pose proof (stride_ge16 mt ltac:(llia) Hsc). unfold gextent, mt_cnt in *. lnia.
  Qed.

  Lemma glvl_range : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    mt_maplen mt = 0 -> 0 <= glvl mt <= 5.
  Proof.
    intros ma mt aib slots Hma Hr Hml. pose proof (nested_extent ma mt aib slots Hma Hr Hml) as He.
    unfold glvl. split; [apply Z.log2_nonneg|].
    assert (gextent mt / 48 <= 43) by (apply Z.div_le_upper_bound; llia).
    assert (1 <= gextent mt / 48) by (apply Z.div_le_lower_bound; llia).
    apply Z.le_trans with (Z.log2 43); [apply Z.log2_le_mono; llia | cbn; llia].
  Qed.

  (* [comment removed for export] *)
  Lemma parent_lvl : forall ma mt aib slots pa pm paib psl j,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> mt_maplen mt = 0 ->
    a_meta A pa = Some pm -> mt_role pm = RGroup paib psl -> 0 <= j ->
    nth_error psl (Z.to_nat j) = Some (SNested ma) ->
    mt_maplen pm = 0 -> glvl mt + 1 <= glvl pm.
  Proof.
    intros ma mt aib slots pa pm paib psl j Hma Hr Hml Hpa Hpr Hj0 Hj Hpml.
    destruct (wf_nested A HW pa pm paib psl j ma Hpa Hpr Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & _ & _ & Hfit).
    rewrite Hma in Hmc. injection Hmc as <-.
    pose proof (nested_extent ma mt aib slots Hma Hr Hml) as He.
    destruct (wf_nested_small A HW pa pm paib psl Hpa Hpr Hpml) as [Hl Hs].
    destruct (wf_grp A HW pa pm paib psl Hpa Hpr) as (Hw32 & _ & Hsc & _).
    pose proof (stride_ge16 pm ltac:(llia) Hsc).
    assert (Hd : 2 * gextent mt + 8 <= gextent pm) by (unfold gextent, mt_cnt in *; lnia).
    unfold glvl.
    assert (H2 : 2 * (gextent mt / 48) <= gextent pm / 48).
    { apply Z.div_le_lower_bound; [llia|]. pose proof (Z.mul_div_le (gextent mt) 48 ltac:(llia)). llia. }
    assert (H1 : 1 <= gextent mt / 48) by (apply Z.div_le_lower_bound; llia).
    replace (Z.log2 (gextent mt / 48) + 1) with (Z.log2 (2 * (gextent mt / 48))) by (rewrite Z.log2_double by llia; llia).
    apply Z.log2_le_mono. llia.
  Qed.

  Lemma nfuel_parent : forall ma mt aib slots pa pm paib psl j,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> mt_maplen mt = 0 ->
    a_meta A pa = Some pm -> mt_role pm = RGroup paib psl -> 0 <= j ->
    nth_error psl (Z.to_nat j) = Some (SNested ma) ->
    (nfuel pm < nfuel mt)%nat.
  Proof.
    intros ma mt aib slots pa pm paib psl j Hma Hr Hml Hpa Hpr Hj0 Hj.
    pose proof (glvl_range ma mt aib slots Hma Hr Hml) as Hl.
    unfold nfuel. rewrite (proj2 (Z.ltb_ge 0 (mt_maplen mt))) by llia.
    destruct (0 <? mt_maplen pm) eqn:E; [llia|]. apply Z.ltb_ge in E.
    pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (Hw32 & _). 
    assert (Hpml : mt_maplen pm = 0) by (unfold mt_maplen, w_maplen in *; pose proof (Z.div_pos (mt_w32 pm) 4096); llia).
    pose proof (parent_lvl ma mt aib slots pa pm paib psl j Hma Hr Hml Hpa Hpr Hj0 Hj Hpml).
    pose proof (glvl_range pa pm paib psl Hpa Hpr Hpml). llia.
  Qed.

  Lemma nfuel_le : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
    (nfuel mt <= 7)%nat.
  Proof.
    intros ma mt aib slots Hma Hr. unfold nfuel. destruct (0 <? mt_maplen mt) eqn:E; [llia|].
    apply Z.ltb_ge in E. pose proof (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32 & _).
    assert (Hml : mt_maplen mt = 0) by (unfold mt_maplen, w_maplen in *; pose proof (Z.div_pos (mt_w32 mt) 4096); llia).
    pose proof (glvl_range ma mt aib slots Hma Hr Hml). llia.
  Qed.
End Depth.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Chain.
  Variable A : astate.
  Hypothesis HW : WF A.

  Lemma nested_in_root_slot_n : forall n ma mt aib slots,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> mt_maplen mt = 0 -> 5 - Z.of_nat n <= glvl mt ->
    exists mr mtr aibr slr j ch, a_meta A mr = Some mtr /\ mt_role mtr = RGroup aibr slr /\ 0 < mt_maplen mtr /\
      0 <= j /\ nth_error slr (Z.to_nat j) = Some (SNested ch) /\
      slot_start mtr j <= gext_lo mt /\ gext_hi mt <= slot_end mtr j.
  Proof.
    induction n as [|n IH]; intros ma mt aib slots Hma Hr Hml Hl.
    - (* [comment removed for export] *)
      destruct (wf_nested_parent A HW ma mt aib slots Hma Hr Hml) as (pa & pm & paib & psl & j & Hpa & Hpr & Hj0 & Hj).
      destruct (wf_nested A HW pa pm paib psl j ma Hpa Hpr Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & _ & Hmem & Hfit).
      rewrite Hma in Hmc. injection Hmc as <-.
      destruct (Z.lt_ge_cases 0 (mt_maplen pm)) as [Hroot | Hnz].
      + exists pa, pm, paib, psl, j, ma. repeat split; auto.
        * unfold gext_lo, slot_start in *. llia.
        * unfold gext_hi, slot_end, slot_start, slot_end_g, slot_start_g in *. rewrite Hmem. unfold slot_start_g. llia.
      + exfalso. pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (Hw32 & _).
        assert (Hpml : mt_maplen pm = 0) by (unfold mt_maplen, w_maplen in *; pose proof (Z.div_pos (mt_w32 pm) 4096); llia).
        pose proof (parent_lvl A HW ma mt aib slots pa pm paib psl j Hma Hr Hml Hpa Hpr Hj0 Hj Hpml).
        pose proof (glvl_range A HW pa pm paib psl Hpa Hpr Hpml). cbn in Hl. llia.
    - destruct (wf_nested_parent A HW ma mt aib slots Hma Hr Hml) as (pa & pm & paib & psl & j & Hpa & Hpr & Hj0 & Hj).
      destruct (wf_nested A HW pa pm paib psl j ma Hpa Hpr Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & _ & Hmem & Hfit).
      rewrite Hma in Hmc. injection Hmc as <-.
      destruct (Z.lt_ge_cases 0 (mt_maplen pm)) as [Hroot | Hnz].
      + exists pa, pm, paib, psl, j, ma. repeat split; auto.
        * unfold gext_lo, slot_start in *. llia.
        * unfold gext_hi, slot_end, slot_start, slot_end_g, slot_start_g in *. rewrite Hmem. unfold slot_start_g. llia.
      + pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (Hw32 & _ & Hsc & _).
        assert (Hpml : mt_maplen pm = 0) by (unfold mt_maplen, w_maplen in *; pose proof (Z.div_pos (mt_w32 pm) 4096); llia).
        pose proof (parent_lvl A HW ma mt aib slots pa pm paib psl j Hma Hr Hml Hpa Hpr Hj0 Hj Hpml) as Hpl.
        destruct (IH pa pm paib psl Hpa Hpr Hpml ltac:(rewrite Nat2Z.inj_succ in Hl; llia)) as
          (mr & mtr & aibr & slr & jr & chr & Hmr & Hrr & Hmlr & Hjr0 & Hjr & Hlo & Hhi).
        exists mr, mtr, aibr, slr, jr, chr. repeat split; auto.
        * pose proof (stride_ge16 pm ltac:(llia) Hsc).
          unfold gext_lo, gext_hi, slot_start, slot_start_g in *. rewrite Hmem. lnia.
        * pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (_ & _ & _ & Hlen & _).
          assert (Hjlt : (Z.to_nat j < length psl)%nat) by (apply (proj1 (nth_error_Some psl (Z.to_nat j))); rewrite Hj; discriminate).
          assert (Hjc : j + 1 <= mt_cnt pm) by llia.
          pose proof (stride_ge16 pm ltac:(llia) Hsc) as HS.
          assert (HjS : j * mt_stride pm + mt_stride pm <= mt_cnt pm * mt_stride pm) by lnia.
          unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g in *. rewrite Hmem in *. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma nested_in_root_slot : forall ma mt aib slots,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> mt_maplen mt = 0 ->
    exists mr mtr aibr slr j ch, a_meta A mr = Some mtr /\ mt_role mtr = RGroup aibr slr /\ 0 < mt_maplen mtr /\
      0 <= j /\ nth_error slr (Z.to_nat j) = Some (SNested ch) /\
      slot_start mtr j <= gext_lo mt /\ gext_hi mt <= slot_end mtr j.
  Proof.
    intros ma mt aib slots Hma Hr Hml. apply (nested_in_root_slot_n 5 ma mt aib slots Hma Hr Hml).
    pose proof (glvl_range A HW ma mt aib slots Hma Hr Hml). cbn. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma root_no_nested_clear : forall ma mt aib slots x mtx aibx slx,
    a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
    (forall j ch, nth_error slots j <> Some (SNested ch)) ->
    a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> x <> ma ->
    gext_hi mtx <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= gext_lo mtx.
  Proof.
    intros ma mt aib slots x mtx aibx slx Hma Hr Hml Hnn Hx Hrx Hne.
    pose proof (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw32x & _ & Hscx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfitx & _).
    pose proof (stride_ge16 mtx ltac:(llia) Hscx) as HSx.
    destruct (Z.lt_ge_cases 0 (mt_maplen mtx)) as [Hrootx | Hnz].
    - pose proof (wf_disj_grp_grp A HW ma mt aib slots x mtx aibx slx Hma Hr Hml Hx Hrx Hrootx ltac:(intros E; apply Hne; symmetry; exact E)) as D.
      rewrite (proj2 (Z.eqb_neq (mt_maplen mtx) 0)) in Hfitx by llia.
      unfold gext_lo, gext_hi. unfold mt_cnt in *. destruct D; [right; llia | left; lnia].
    - assert (Hmlx : mt_maplen mtx = 0) by (unfold mt_maplen, w_maplen in *; pose proof (Z.div_pos (mt_w32 mtx) 4096); llia).
      destruct (nested_in_root_slot x mtx aibx slx Hx Hrx Hmlx) as (mr & mtr & aibr & slr & j & ch & Hmr & Hrr & Hmlr & Hj0 & Hj & Hlo & Hhi).
      destruct (Z.eq_dec mr ma) as [-> | Hne2].
      + exfalso. rewrite Hma in Hmr. injection Hmr as <-. rewrite Hr in Hrr. injection Hrr as <- <-. exact (Hnn _ _ Hj).
      + pose proof (wf_disj_grp_grp A HW ma mt aib slots mr mtr aibr slr Hma Hr Hml Hmr Hrr Hmlr ltac:(intros E; apply Hne2; symmetry; exact E)) as D.
        pose proof (wf_grp A HW mr mtr aibr slr Hmr Hrr) as (Hw32r & _ & Hscr & Hlenr & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfitr & _).
        pose proof (stride_ge16 mtr ltac:(llia) Hscr) as HSr.
        rewrite (proj2 (Z.eqb_neq (mt_maplen mtr) 0)) in Hfitr by llia.
        assert (Hjlt : (Z.to_nat j < length slr)%nat) by (apply (proj1 (nth_error_Some slr (Z.to_nat j))); rewrite Hj; discriminate).
        assert (Hjc : j < mt_cnt mtr) by llia.
        assert (HjS : 0 <= j * mt_stride mtr /\ j * mt_stride mtr + mt_stride mtr <= mt_cnt mtr * mt_stride mtr) by lnia.
        unfold slot_start, slot_end, slot_start_g, slot_end_g, gext_lo, gext_hi in *. unfold mt_cnt in *.
        destruct D; [right | left]; lnia.
  Qed.
End Chain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ntpre (A : astate) (s : mstate) (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z) : Prop := {
  np_wf : WF A;
  np_rep : Rep A (ms_mem s);
  np_win : WIN s;
  np_ro : rodata_clear (ms_mem s);
  np_st : statics_ok (ms_mem s);
  np_vm : VMok A (ms_vm s);
  np_ma : a_meta A ma = Some mt;
  np_role : mt_role mt = RGroup aib slots;
  np_slot : nth_error slots (Z.to_nat i) = Some STaken;
  np_i : 0 <= i
}.

(* [comment removed for export] *)
Definition never_bounces (sc : Z) : Prop := sc < 7 \/ 38 < sc.

(* [comment removed for export] *)
Definition nt_ctx_kept (k : cslot) : Prop :=
  match k with KActive _ | KFmh | KUsage _ | KSeq | KUseq _ => False | _ => True end.

(* [comment removed for export] *)
Definition nt_groups (A A' : astate) (ma : Z) (slots : list slot_st) (i : Z) : Prop :=
  forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    exists mt0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\
      mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx /\
      ((x = ma /\ slx = list_set slots (Z.to_nat i) SIdle) \/
       (x <> ma /\ (slx = sl0 \/ exists j ch, nth_error sl0 j = Some (SNested ch) /\ slx = list_set sl0 j SIdle))).

Definition nt_dead_kept (A A' : astate) : Prop :=
  forall x mtx, a_meta A x = Some mtx -> mt_role mtx = RDead ->
    exists mtx', a_meta A' x = Some mtx' /\ mt_role mtx' = RDead.

(* [comment removed for export] *)
Definition nt_result (A A' : astate) (h : VmMaps) (r : word * word) : Prop :=
  (r = (w0, w0) /\ VMok A' h /\ (forall x, dom A' x <-> dom A x))
  \/ (exists B L, r = (Z_to_bv 64 B, Z_to_bv 64 L) /\ 0 < L /\ page_aligned B /\ L mod 4096 = 0 /\
        heap_range B (B + L) /\
        In (Z_to_bv 64 B, Z_to_bv 64 L) (vm_maps h) /\
        region_free (vm_noaccess h) (Z_to_bv 64 B) (Z_to_bv 64 L) = true /\
        VMok A' (vm_munmap (Z_to_bv 64 B) (Z_to_bv 64 L) h) /\
        (forall x, B <= x < B + L -> ~ dom A' x) /\
        (forall f, has A' f -> f_a f + f_n f <= B \/ B + L <= f_a f) /\
        (forall x, dom A x <-> dom A' x \/ B <= x < B + L)).

Definition ntfree_post (A : astate) (s : mstate) (ma : Z) (mt : meta_rec) (slots : list slot_st) (i : Z)
    (r : word * word) (s' : mstate) : Prop :=
  exists A', WF A' /\ Rep A' (ms_mem s') /\ statics_ok (ms_mem s') /\ rodata_clear (ms_mem s') /\
    s' = upd s (ms_mem s') (ms_vm s) /\
    a_live A' = a_live A /\ a_areas A' = a_areas A /\
    (forall k, nt_ctx_kept k -> a_ctx A' k = a_ctx A k) /\
    (forall a : word, ~ mowned A a -> ms_mem s' a = ms_mem s a) /\
    (forall a : word, ms_mem s a <> None -> ms_mem s' a <> None) /\
    nt_dead_kept A A' /\
    nt_groups A A' ma slots i /\
    (Z.lor (mt_avail mt) (mt_freed mt) + 2 ^ i = 2 ^ (mt_cnt mt) - 1 -> never_bounces (mt_sc mt) ->
       forall mtx aibx slx, a_meta A' ma = Some mtx -> mt_role mtx <> RGroup aibx slx) /\
    nt_result A A' (ms_vm s) r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ntJ1 (A : astate) (s : mstate) (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st)
    (A1 : astate) (s1 : mstate) : Prop := {
  j1_wf : WF A1;
  j1_rep : Rep A1 (ms_mem s1);
  j1_st : statics_ok (ms_mem s1);
  j1_ro : rodata_clear (ms_mem s1);
  j1_vm : VMok A1 (ms_vm s);
  j1_s : s1 = upd s (ms_mem s1) (ms_vm s);
  j1_ma : exists mt1, a_meta A1 ma = Some mt1 /\ mt_role mt1 = RGroup aib slots /\
            mt_w32 mt1 = mt_w32 mt /\ mt_mem mt1 = mt_mem mt /\
            mt_avail mt1 = mt_avail mt /\ mt_freed mt1 = mt_freed mt;
  j1_unlinked : forall sc, ~ In ma (a_active A1 sc);
  j1_live : a_live A1 = a_live A;
  j1_areas : a_areas A1 = a_areas A;
  j1_ctx : forall k, (forall sc, k <> KActive sc) -> a_ctx A1 k = a_ctx A k;
  j1_fl : a_freelist A1 = a_freelist A;
  j1_frame : forall a : word, ~ mowned A a -> ms_mem s1 a = ms_mem s a;
  j1_mapped : forall a : word, ms_mem s a <> None -> ms_mem s1 a <> None;
  j1_dead : nt_dead_kept A A1;
  j1_groups : forall x mtx aibx slx, a_meta A1 x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     exists mt0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx slx /\ mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  j1_groups_back : forall x mt0 aibx slx, a_meta A x = Some mt0 -> mt_role mt0 = RGroup aibx slx ->
     exists mtx, a_meta A1 x = Some mtx /\ mt_role mtx = RGroup aibx slx /\ mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  j1_dom : forall x, dom A1 x <-> dom A x
}.

End WithLayout.
