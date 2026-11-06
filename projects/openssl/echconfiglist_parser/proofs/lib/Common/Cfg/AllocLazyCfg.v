(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  lo <= hi ->
  Forall (fun r => 0 < e_sz r /\ (e_hi r <= lo \/ hi <= e_lo r)) (m_vm_lazy m) ->
  Forall (fun p => page_outside_range lo hi p = true) (m_vm_materialized m) ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hle Hlz Hmat. unfold vm_forget_range.
  rewrite (maps_subtract_id _ lo hi Hle Hlz).
  rewrite (filter_all_true _ _ (proj1 (Forall_forall _ _) Hmat)).
  apply with_vm_backing_self.
Qed.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Lemma sstep_cfg_det_iff_lz : forall ms m x8 eff0 m0 e0,
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) m o <-> o = Ok eff0 m0 e0) ->
  m_halted m0 = None -> syscall_effect_accesses eff0 = [] ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = e0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms m x8 eff0 m0 e0 Hh Hsvc Hspec Hh0 Hl0 e st.
  rewrite (sstep_cfg_svc_iff_noacc cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & _ & ->). apply Hspec in Hs. inversion Hs; subst. split; reflexivity.
    + intros (-> & ->). exists eff0, m0. split; [apply Hspec; reflexivity |]. split; [| reflexivity].
      intros (_ & Hr & (eff' & m' & evs' & Hs' & Hnr)).
      apply Hspec in Hs'. inversion Hs'; subst. rewrite Hr in Hnr. discriminate Hnr.
  - intros Hun. apply Hspec in Hun. discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs. inversion Hs; subst. split; assumption.
Qed.

Lemma sstep_cfg_filter_det_iff_lz : forall ms m x8 eff0 m0 e0,
  injected_family_off cfg (sys_input segs ms x8) = true ->
  m_halted m = None -> ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) m (Ok eff0 m0 e0) ->
  refusal_b (sys_input segs ms x8) m (eff_ret eff0) = false ->
  m_halted m0 = None -> syscall_effect_accesses eff0 = [] ->
  (forall o, syscall_spec (sys_input segs ms x8) m o ->
     o = Ok eff0 m0 e0
     \/ exists eff m' evs, o = Ok eff m' evs
          /\ refusal_b (sys_input segs ms x8) m (eff_ret eff) = true
          /\ m_halted m' = None /\ syscall_effect_accesses eff = []) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = e0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms m x8 eff0 m0 e0 Hoff Hh Hsvc Hs0 Hnr0 Hh0 Hl0 Hall e st.
  rewrite (sstep_cfg_svc_iff_noacc cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->).
      destruct (Hall _ Hs) as [Heq | (eff1 & m1 & evs1 & Heq & Hr & _)]; inversion Heq; subst.
      * split; reflexivity.
      * exfalso. apply Hns. split; [exact Hoff |]. split; [exact Hr |].
        exists eff0, m0, e0. split; assumption.
    + intros (-> & ->). exists eff0, m0. split; [exact Hs0 |]. split; [| reflexivity].
      apply spurious_refusal_not_refusal. exact Hnr0.
  - intros Hun. destruct (Hall _ Hun) as [Heq | (? & ? & ? & Heq & _)]; discriminate Heq.
  - intros eff m' evs Hs.
    destruct (Hall _ Hs) as [Heq | (eff1 & m1 & evs1 & Heq & _ & Hn & Hl)]; inversion Heq; subst;
      split; assumption.
Qed.

Theorem mmap_anon_step_iff_lz : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_b m a nZ = true) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists a, mmap_grant_b m a nZ = true /\ e = [] /\
      st = SNext (mkCfg (sysret ms a (apply_zeros (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
                        (mmap_grant_model a nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hsvc Hno Hargs nZ (a0 & Ha0) e st.
  pose proof (mmap_anon_spec_iff segs ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec. fold nZ in Hspec.
  assert (Hoff : injected_family_off cfg (sys_input segs ms x8) = true)
    by (apply alloc_family_off; [exact Hc | right; right; left; exact Hno]).
  rewrite (sstep_cfg_svc_iff_noacc cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->). apply Hspec in Hs as [Hs | (a & Ha & Hs)].
      * exfalso. inversion Hs; subst. apply Hns. split; [exact Hoff |]. split.
        { cbn [eff_ret]. apply mmap_refusal_enomem. exact Hno. }
        exists (mkEffect a0 [] [(a0, Z_to_bv 64 nZ)]), (mmap_grant_model a0 nZ m), [].
        split; [apply Hspec; right; exists a0; split; [exact Ha0 | reflexivity] |].
        cbn [eff_ret]. apply mmap_refusal_grant; [exact Hno |].
        apply mmap_grant_b_iff in Ha0. tauto.
      * inversion Hs; subst. exists a. split; [exact Ha |]. split; reflexivity.
    + intros (a & Ha & -> & ->).
      exists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), (mmap_grant_model a nZ m).
      split; [apply Hspec; right; exists a; split; [exact Ha | reflexivity] |].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. cbn [eff_ret].
      apply mmap_refusal_grant; [exact Hno |]. apply mmap_grant_b_iff in Ha. tauto.
  - intros Hun. apply Hspec in Hun as [Hun | (a & _ & Hun)]; discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs as [Hs | (a & _ & Hs)]; inversion Hs; subst.
    + split; [exact Hh | reflexivity].
    + split; [exact Hh | reflexivity].
Qed.

Theorem mmap_na_step_iff_lz : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_na_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true /\ e = [] /\
      st = SNext (mkCfg (sysret ms a (apply_unmaps (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
                        (mmap_na_model a nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hsvc Hno Hargs nZ (a0 & Ha0) e st.
  pose proof (mmap_na_spec_iff segs ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec. fold nZ in Hspec.
  assert (Hoff : injected_family_off cfg (sys_input segs ms x8) = true)
    by (apply alloc_family_off; [exact Hc | right; right; left; exact Hno]).
  rewrite (sstep_cfg_svc_iff_noacc cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->). apply Hspec in Hs as [Hs | (a & Ha & Hs)].
      * exfalso. inversion Hs; subst. apply Hns. split; [exact Hoff |]. split.
        { cbn [eff_ret]. apply mmap_refusal_enomem. exact Hno. }
        exists (mkEffectU a0 [] [] [(a0, Z_to_bv 64 nZ)] [] []), (mmap_na_model a0 nZ m), [].
        split; [apply Hspec; right; exists a0; split; [exact Ha0 | reflexivity] |].
        cbn [eff_ret]. apply mmap_refusal_grant; [exact Hno |].
        apply mmap_grant_na_b_iff in Ha0. tauto.
      * inversion Hs; subst. exists a. split; [exact Ha |]. split; reflexivity.
    + intros (a & Ha & -> & ->).
      exists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []), (mmap_na_model a nZ m).
      split; [apply Hspec; right; exists a; split; [exact Ha | reflexivity] |].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. cbn [eff_ret].
      apply mmap_refusal_grant; [exact Hno |]. apply mmap_grant_na_b_iff in Ha. tauto.
  - intros Hun. apply Hspec in Hun as [Hun | (a & _ & Hun)]; discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs as [Hs | (a & _ & Hs)]; inversion Hs; subst.
    + split; [exact Hh | reflexivity].
    + split; [exact Hh | reflexivity].
Qed.

Theorem brk_query_step_iff_lz : forall ms x8 m,
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  (bv_unsigned (ms_gpr ms 0) = 0
   \/ bv_unsigned (ms_gpr ms 0) < bv_unsigned (vm_start_brk (m_vmmaps m))) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m Hh Hsvc Hno Hq e st.
  rewrite (sstep_cfg_det_iff_lz ms m x8 _ _ _ Hh Hsvc (brk_query_spec_iff segs ms x8 m Hno Hq) Hh eq_refl).
  reflexivity.
Qed.

Theorem brk_grow_step_iff_lz : forall ms x8 m,
  sc_alloc cfg = false ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = true ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (ms_gpr ms 0)
                         (apply_zeros (ms_mem ms) (brk_grow_zeros (ms_gpr ms 0) m)))
                      (brk_grow_model (ms_gpr ms 0) m)).
Proof.
  intros ms x8 m Hc Hh Hsvc Hno Hargs Hg e st.
  pose proof (brk_grow_spec_iff segs ms x8 m Hno Hargs) as Hspec.
  rewrite (sstep_cfg_filter_det_iff_lz ms m x8
             (mkEffect (ms_gpr ms 0) [] (brk_grow_zeros (ms_gpr ms 0) m))
             (brk_grow_model (ms_gpr ms 0) m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | left; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. split; [exact Hg | reflexivity].
  - cbn [eff_ret]. apply brk_refusal_new; assumption.
  - exact Hh.
  - reflexivity.
  - intros o Ho. apply Hspec in Ho as [-> | (_ & ->)]; [right | left; reflexivity].
    eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
    split; [apply brk_refusal_old; assumption | split; [exact Hh | reflexivity]].
Qed.

Theorem brk_grow_step_iff_blocked_lz : forall ms x8 m,
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214 ->
  brk_grow_args ms m ->
  brk_grow_b m (ms_gpr ms 0) = false ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\ st = SNext (mkCfg (sysret ms (vm_brk (m_vmmaps m)) (ms_mem ms)) m).
Proof.
  intros ms x8 m Hh Hsvc Hno Hargs Hg e st.
  pose proof (brk_grow_spec_iff segs ms x8 m Hno Hargs) as Hspec.
  assert (Honly : forall o, syscall_spec (sys_input segs ms x8) m o <->
                            o = Ok (mkEffect (vm_brk (m_vmmaps m)) [] []) m []).
  { intros o. rewrite Hspec. split; [| intros ->; left; reflexivity].
    intros [-> | (Hg' & _)]; [reflexivity | rewrite Hg in Hg'; discriminate Hg']. }
  rewrite (sstep_cfg_det_iff_lz ms m x8 _ _ _ Hh Hsvc Honly Hh eq_refl). reflexivity.
Qed.

Theorem mprotect_rw_step_iff_lz : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226 ->
  mprotect_rw_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  mprotect_budget_ok m addr (Z_to_bv 64 nZ) = true ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (Z_to_bv 64 0) (apply_zeros (ms_mem ms) [(addr, Z_to_bv 64 nZ)]))
                      (mprotect_rw_model addr nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hsvc Hno Hargs addr nZ Hb e st.
  pose proof (mprotect_rw_spec_iff segs ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec.
  fold addr nZ in Hspec.
  rewrite (sstep_cfg_filter_det_iff_lz ms m x8
             (mkEffect (Z_to_bv 64 0) [] [(addr, Z_to_bv 64 nZ)])
             (mprotect_rw_model addr nZ m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | right; right; right; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. split; [exact Hb | reflexivity].
  - cbn [eff_ret]. apply mprotect_refusal_zero. exact Hno.
  - exact Hh.
  - reflexivity.
  - intros o Ho. apply Hspec in Ho as [-> | (_ & ->)]; [right | left; reflexivity].
    eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
    split; [apply mprotect_refusal_enomem; exact Hno | split; [exact Hh | reflexivity]].
Qed.

(* [comment removed for export] *)
Theorem munmap_entry_step_iff_lz : forall ms x8 m len n,
  m_halted m = None ->
  (forall h, vm_forget_range (bv_unsigned (ms_gpr ms 0)) (bv_unsigned (ms_gpr ms 0) + bv_unsigned n)
               (with_vmmaps h m) = with_vmmaps h m) ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_entry_args ms m len n ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (Z_to_bv 64 0) (apply_unmaps (ms_mem ms) [(ms_gpr ms 0, n)]))
                      (with_vmmaps (ledger_unmap (ms_gpr ms 0) n (m_vmmaps m)) m)).
Proof.
  intros ms x8 m len n Hh Hfr Hsvc Hno Hargs e st.
  pose proof (munmap_entry_spec_iff segs ms x8 m len n Hno Hargs) as Hspec.
  unfold munmap_model in Hspec. rewrite Hfr in Hspec.
  rewrite (sstep_cfg_det_iff_lz ms m x8 _ _ _ Hh Hsvc Hspec); [reflexivity | exact Hh | reflexivity].
Qed.

(* [comment removed for export] *)
Theorem munmap_entry_step_iff_gen_lz : forall ms x8 m len n,
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_entry_args ms m len n ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms (Z_to_bv 64 0) (apply_unmaps (ms_mem ms) [(ms_gpr ms 0, n)]))
                      (munmap_model (ms_gpr ms 0) n m)).
Proof.
  intros ms x8 m len n Hh Hsvc Hno Hargs e st.
  pose proof (munmap_entry_spec_iff segs ms x8 m len n Hno Hargs) as Hspec.
  rewrite (sstep_cfg_det_iff_lz ms m x8 _ _ _ Hh Hsvc Hspec); [reflexivity | exact Hh | reflexivity].
Qed.

Lemma mmap_guard_spec_iff_lz : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  (forall h, vm_forget_range (bv_unsigned (ms_gpr ms 0)) (bv_unsigned (ms_gpr ms 0) + page_round_up_Z len)
               (with_vmmaps h m) = with_vmmaps h m) ->
  mmap_guard_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ o = Ok (mkEffectU addr [] [] [(addr, Z_to_bv 64 nZ)] [] []) (mmap_guard_model addr nZ m) []
    \/ o = Ok (mkEffectU (errno_ret ENOMEM) [] [] [(addr, Z_to_bv 64 nZ)] [] [])
              (mmap_guard_destroyed_model addr nZ m) [].
Proof.
  intros ms x8 m len Hno Hfr (Hlen & Hpos & Hprot & Hflags & Hoff & Hal & Ha0 & Htop & HfR & Hcont)
    addr nZ o.
  rewrite (syscall_spec_mmap segs ms x8 m o Hno).
  fold addr in Hal, Ha0, Htop, HfR, Hcont. fold nZ in Htop, HfR, Hcont.
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = false)
    by (unfold mmap_modeled_b; rewrite Hprot; reflexivity).
  assert (G5 : mmap_noaccess_b prot flags off = false)
    by (unfold mmap_noaccess_b, mmap_flags_core; rewrite Hprot, Hflags; reflexivity).
  assert (G6 : mmap_fixed_noaccess_b prot flags off = true).
  { unfold mmap_fixed_noaccess_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G7 : mmap_noreserve_b flags = false)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat.
  assert (G8 : (two_pow_64 <=? bv_unsigned addr + nZ) = false) by (apply Z.leb_gt; lia).
  assert (G9 : (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)) = true) by (apply Z.leb_le; exact Htop).
  assert (G10 : (bv_unsigned addr mod page_size =? 0) = true) by (apply Z.eqb_eq; exact Hal).
  assert (G11 : (0 <? bv_unsigned addr) = true) by (apply Z.ltb_lt; exact Ha0).
  assert (Hrepl : with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                    (with_vmmaps (ledger_guard addr (Z_to_bv 64 nZ) (m_vmmaps m)) m)
                  = mmap_guard_model addr nZ m).
  { unfold with_mmap_replacement, with_mmap_backing. rewrite G7.
    assert (Eu : bv_unsigned (Z_to_bv 64 nZ) = nZ).
    { apply u64_lit. pose proof (alloc_top_lt (m_vmmaps m)) as Hat0. unfold two_pow_64 in Hat0.
      pose proof (u64_range addr). assert (0 <= nZ) by (unfold nZ; pose proof (page_round_up_Z_ge len); lia). lia. }
    rewrite Eu. apply Hfr. }
  unfold mmap_spec. rewrite G1, G2, G3, G4, G5, G6. cbn [negb]. rewrite Hlen. fold nZ. fold addr.
  rewrite G8.
  rewrite bind_get_model. rewrite G9, G10, G11. cbn [negb]. rewrite HfR, Hcont. cbn [andb].
  fold (ledger_guard addr (Z_to_bv 64 nZ) (m_vmmaps m)). rewrite Hrepl.
  fold (mmap_guard_destroyed_model addr nZ m).
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | [H | H]]; sys_destruct.
      * left. match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end. reflexivity.
      * right. left. reflexivity.
      * right. right.
        match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end. reflexivity.
    + intros [H | [H | H]]; sys_destruct.
  - intros [-> | [-> | ->]].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. left. eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
    + right. right. exists ENOMEM, m, [], [].
      split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |]. split; [| reflexivity].
      eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Theorem mmap_guard_step_iff_lz : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None ->
  (forall h, vm_forget_range (bv_unsigned (ms_gpr ms 0)) (bv_unsigned (ms_gpr ms 0) + page_round_up_Z len)
               (with_vmmaps h m) = with_vmmaps h m) ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_guard_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms addr (apply_unmaps (ms_mem ms) [(addr, Z_to_bv 64 nZ)]))
                      (mmap_guard_model addr nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hfr Hsvc Hno Hargs addr nZ e st.
  pose proof (mmap_guard_spec_iff_lz ms x8 m len Hno Hfr Hargs) as Hspec. cbv zeta in Hspec.
  fold addr nZ in Hspec.
  destruct Hargs as (_ & _ & _ & _ & _ & Hal & _). fold addr in Hal.
  rewrite (sstep_cfg_filter_det_iff_lz ms m x8
             (mkEffectU addr [] [] [(addr, Z_to_bv 64 nZ)] [] [])
             (mmap_guard_model addr nZ m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | right; right; left; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. left. reflexivity.
  - cbn [eff_ret]. apply mmap_refusal_grant; assumption.
  - exact Hh.
  - reflexivity.
  - intros o Ho. apply Hspec in Ho as [-> | [-> | ->]]; [right | left; reflexivity | right].
    + eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
      split; [apply mmap_refusal_enomem; exact Hno | split; [exact Hh | reflexivity]].
    + eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
      split; [apply mmap_refusal_enomem; exact Hno |].
      destruct (mmap_guard_destroyed_facts addr nZ m) as [H1 H2].
      split; [rewrite H1; exact Hh | reflexivity].
Qed.

(* [comment removed for export] *)

Definition mmap_anon_nr_args (ms : machine_state) (len : Z) : Prop :=
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned (ms_gpr ms 2) = 3          (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 3) = 16418      (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 5) = 0.

Definition mmap_grant_nr_model (a : word) (nZ : Z) (m : Model) : Model :=
  vm_add_lazy a (Z_to_bv 64 nZ) (mmap_grant_model a nZ m).

Lemma mmap_anon_nr_spec_iff : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  mmap_anon_nr_args ms len ->
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true
                 /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 nZ)]) (mmap_grant_nr_model a nZ m) [].
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hflags & Hoff) nZ o.
  rewrite (syscall_spec_mmap segs ms x8 m o Hno).
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = true).
  { unfold mmap_modeled_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G5 : mmap_noreserve_b flags = true)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  unfold mmap_spec. rewrite G1, G2, G3, G4. cbn [negb].
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite G5, Hlen. fold nZ.
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | H]; sys_destruct.
      * left. match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end.
        reflexivity.
      * right. eexists. split; [apply mmap_grant_na_b_iff; repeat split; eassumption |].
        reflexivity.
    + intros [H | H]; sys_destruct.
  - intros [-> | (a & Ha & ->)].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. apply mmap_grant_na_b_iff in Ha as (A1 & A2 & A3 & A4).
      exists m, m, [], []. split; [reflexivity |]. split; [| reflexivity].
      exists a, m, [], []. split.
      { exists a. split; [| reflexivity]. repeat split; assumption. }
      split; [| reflexivity].
      exists tt, (mmap_grant_nr_model a nZ m), [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Theorem mmap_anon_nr_step_iff_lz : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_anon_nr_args ms len ->
  let nZ := page_round_up_Z len in
  (exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true /\ e = [] /\
      st = SNext (mkCfg (sysret ms a (apply_zeros (ms_mem ms) [(a, Z_to_bv 64 nZ)]))
                        (mmap_grant_nr_model a nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hsvc Hno Hargs nZ (a0 & Ha0) e st.
  pose proof (mmap_anon_nr_spec_iff ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec. fold nZ in Hspec.
  assert (Hoff : injected_family_off cfg (sys_input segs ms x8) = true)
    by (apply alloc_family_off; [exact Hc | right; right; left; exact Hno]).
  rewrite (sstep_cfg_svc_iff_noacc cfg segs ms m x8 Hh Hsvc).
  - split.
    + intros (eff & m' & Hs & Hns & ->). apply Hspec in Hs as [Hs | (a & Ha & Hs)].
      * exfalso. inversion Hs; subst. apply Hns. split; [exact Hoff |]. split.
        { cbn [eff_ret]. apply mmap_refusal_enomem. exact Hno. }
        exists (mkEffect a0 [] [(a0, Z_to_bv 64 nZ)]), (mmap_grant_nr_model a0 nZ m), [].
        split; [apply Hspec; right; exists a0; split; [exact Ha0 | reflexivity] |].
        cbn [eff_ret]. apply mmap_refusal_grant; [exact Hno |].
        apply mmap_grant_na_b_iff in Ha0. tauto.
      * inversion Hs; subst. exists a. split; [exact Ha |]. split; reflexivity.
    + intros (a & Ha & -> & ->).
      exists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), (mmap_grant_nr_model a nZ m).
      split; [apply Hspec; right; exists a; split; [exact Ha | reflexivity] |].
      split; [| reflexivity].
      apply spurious_refusal_not_refusal. cbn [eff_ret].
      apply mmap_refusal_grant; [exact Hno |]. apply mmap_grant_na_b_iff in Ha. tauto.
  - intros Hun. apply Hspec in Hun as [Hun | (a & _ & Hun)]; discriminate Hun.
  - intros eff m' evs Hs. apply Hspec in Hs as [Hs | (a & _ & Hs)]; inversion Hs; subst.
    + split; [exact Hh | reflexivity].
    + split; [exact Hh | reflexivity].
Qed.

(* [comment removed for export] *)

Definition mmap_commit_args (ms : machine_state) (m : Model) (len : Z) : Prop :=
  let h := m_vmmaps m in
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  bv_unsigned (ms_gpr ms 1) = len /\ 0 < len
  /\ bv_unsigned (ms_gpr ms 2) = 3          (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 3) = 50         (* [comment removed for export] *)
  /\ bv_unsigned (ms_gpr ms 5) = 0
  /\ bv_unsigned addr mod page_size = 0 /\ 0 < bv_unsigned addr
  /\ bv_unsigned addr + nZ <= alloc_top h
  /\ region_free (vm_reserved h) addr (Z_to_bv 64 nZ) = true
  /\ map_contains (vm_maps h) addr (Z_to_bv 64 nZ) = true.

Definition mmap_commit_model (addr : word) (nZ : Z) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + nZ)
    (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr (Z_to_bv 64 nZ)) m).

Lemma mmap_commit_args_of_inv : forall R L c S ms m len p,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned (ms_gpr ms 1) = len -> 0 < len ->
  bv_unsigned (ms_gpr ms 2) = 3 -> bv_unsigned (ms_gpr ms 3) = 50 ->
  bv_unsigned (ms_gpr ms 5) = 0 ->
  bv_unsigned (ms_gpr ms 0) mod page_size = 0 ->
  In p (vm_maps (m_vmmaps m)) ->
  e_lo p <= bv_unsigned (ms_gpr ms 0) ->
  bv_unsigned (ms_gpr ms 0) + page_round_up_Z len <= e_hi p ->
  mmap_commit_args ms m len.
Proof.
  intros R L c S ms m len p Hinv Hlen Hpos Hprot Hflags Hoff Hal Hp Hlo Hhi.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat. unfold two_pow_64 in Hat.
  pose proof (page_round_up_Z_pos len Hpos) as Hnpos.
  pose proof (li_top _ _ _ _ _ Hinv) as Htp. pose proof (li_disj_R _ _ _ _ _ Hinv) as HdR.
  pose proof (li_reserved _ _ _ _ _ Hinv) as HR.
  rewrite Forall_forall in Htp, HdR.
  destruct (Htp p Hp) as [Hp0 Hptop].
  assert (Hu : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len)
    by (apply u64_lit; clear - Hnpos Hhi Hptop Hat Hlo Hp0; lia).
  assert (Hin : e_inside (ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z len)) p).
  { unfold e_inside, e_hi at 1, e_lo at 2, e_lo at 2, e_sz. cbn [fst snd]. rewrite Hu.
    split; assumption. }
  unfold mmap_commit_args. cbv zeta. repeat split; try assumption.
  - clear - Hp0 Hlo. lia.
  - clear - Hhi Hptop. lia.
  - rewrite HR. apply region_free_iff. apply Forall_forall. intros r Hr.
    specialize (HdR p Hp). rewrite Forall_forall in HdR.
    apply e_disj_sym. eapply e_disj_inside; [apply e_disj_sym; apply HdR; exact Hr | exact Hin].
  - eapply map_contains_intro; [exact Hp | exact Hin].
Qed.

Lemma mmap_commit_spec_iff_lz : forall ms x8 m len,
  bv_unsigned x8 = 222 ->
  mmap_commit_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  forall o,
    syscall_spec (sys_input segs ms x8) m o <->
    o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
    \/ (vm_backing_within_limit (mmap_commit_model addr nZ m) = true
        /\ o = Ok (mkEffect addr [] [(addr, Z_to_bv 64 nZ)]) (mmap_commit_model addr nZ m) [])
    \/ o = Ok (mkEffectU (errno_ret ENOMEM) [] [] [(addr, Z_to_bv 64 nZ)] [] [])
              (mmap_guard_destroyed_model addr nZ m) [].
Proof.
  intros ms x8 m len Hno (Hlen & Hpos & Hprot & Hflags & Hoff & Hal & Ha0 & Htop & HfR & Hcont)
    addr nZ o.
  rewrite (syscall_spec_mmap segs ms x8 m o Hno).
  fold addr in Hal, Ha0, Htop, HfR, Hcont. fold nZ in Htop, HfR, Hcont.
  set (flags := ms_gpr ms 3) in *. set (off := ms_gpr ms 5) in *. set (prot := ms_gpr ms 2) in *.
  assert (G1 : mmap_off_aligned_b off = true)
    by (unfold mmap_off_aligned_b; rewrite Hoff; reflexivity).
  assert (G2 : mmap_anon_b flags = true) by (unfold mmap_anon_b; rewrite Hflags; reflexivity).
  assert (G3 : w_is0 (ms_gpr ms 1) = false) by (apply w_is0_pos; lia).
  assert (G4 : mmap_modeled_b prot flags off = false)
    by (unfold mmap_modeled_b, mmap_flags_core; rewrite Hprot, Hflags; reflexivity).
  assert (G5 : mmap_noaccess_b prot flags off = false)
    by (unfold mmap_noaccess_b, mmap_flags_core; rewrite Hprot, Hflags; reflexivity).
  assert (G6 : mmap_fixed_noaccess_b prot flags off = false)
    by (unfold mmap_fixed_noaccess_b, mmap_flags_core; rewrite Hprot, Hflags; reflexivity).
  assert (G6' : mmap_fixed_rw_b prot flags off = true).
  { unfold mmap_fixed_rw_b, mmap_flags_core.
    rewrite Hprot, Hflags, (proj2 (w_is0_iff off) Hoff). reflexivity. }
  assert (G7 : mmap_noreserve_b flags = false)
    by (unfold mmap_noreserve_b; rewrite Hflags; reflexivity).
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat.
  assert (G8 : (two_pow_64 <=? bv_unsigned addr + nZ) = false) by (apply Z.leb_gt; lia).
  assert (G9 : (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)) = true) by (apply Z.leb_le; exact Htop).
  assert (G10 : (bv_unsigned addr mod page_size =? 0) = true) by (apply Z.eqb_eq; exact Hal).
  assert (G11 : (0 <? bv_unsigned addr) = true) by (apply Z.ltb_lt; exact Ha0).
  assert (Eu : bv_unsigned (Z_to_bv 64 nZ) = nZ).
  { apply u64_lit. unfold two_pow_64 in Hat.
    pose proof (u64_range addr). assert (0 <= nZ) by (unfold nZ; pose proof (page_round_up_Z_ge len); lia). lia. }
  assert (Hrepl : with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                    (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr (Z_to_bv 64 nZ)) m)
                  = mmap_commit_model addr nZ m).
  { unfold with_mmap_replacement, with_mmap_backing, mmap_commit_model. rewrite G7, Eu. reflexivity. }
  unfold mmap_spec. rewrite G1, G2, G3, G4, G5, G6, G6'. cbn [negb]. rewrite Hlen. fold nZ. fold addr.
  rewrite G8.
  rewrite bind_get_model. rewrite G9, G10, G11. cbn [negb]. rewrite HfR, Hcont. cbn [andb].
  unfold mmap_fixed_rw_budget_ok. rewrite Hrepl.
  fold (mmap_guard_destroyed_model addr nZ m).
  unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, modify.
  split.
  - destruct o as [eff m' evs |].
    + intros [H | [H | H]]; sys_destruct.
      * left. match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end. reflexivity.
      * right. left. split; [assumption | reflexivity].
      * right. right.
        match goal with Hi : In _ mmap_errnos |- _ => destruct Hi as [<- | []] end. reflexivity.
    + intros [H | [H | H]]; sys_destruct.
  - intros [-> | [[Hb ->] | ->]].
    + left. exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |].
      split; reflexivity.
    + right. left. exists tt, m, [], []. split; [exists tt; split; [exact Hb | reflexivity] |].
      split; [| reflexivity].
      exists tt, (mmap_commit_model addr nZ m), [], []. split; [reflexivity |]. split; reflexivity.
    + right. right. exists ENOMEM, m, [], [].
      split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |]. split; [| reflexivity].
      eexists tt, _, [], []. split; [reflexivity |]. split; reflexivity.
Qed.

Theorem mmap_commit_step_iff_lz : forall ms x8 m len,
  sc_alloc cfg = false ->
  m_halted m = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 ->
  mmap_commit_args ms m len ->
  let addr := ms_gpr ms 0 in
  let nZ := page_round_up_Z len in
  vm_backing_within_limit (mmap_commit_model addr nZ m) = true ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    e = [] /\
    st = SNext (mkCfg (sysret ms addr (apply_zeros (ms_mem ms) [(addr, Z_to_bv 64 nZ)]))
                      (mmap_commit_model addr nZ m)).
Proof.
  intros ms x8 m len Hc Hh Hsvc Hno Hargs addr nZ Hbud e st.
  pose proof (mmap_commit_spec_iff_lz ms x8 m len Hno Hargs) as Hspec. cbv zeta in Hspec.
  fold addr nZ in Hspec.
  destruct Hargs as (_ & _ & _ & _ & _ & Hal & _). fold addr in Hal.
  rewrite (sstep_cfg_filter_det_iff_lz ms m x8
             (mkEffect addr [] [(addr, Z_to_bv 64 nZ)])
             (mmap_commit_model addr nZ m) []).
  - reflexivity.
  - apply alloc_family_off; [exact Hc | right; right; left; exact Hno].
  - exact Hh.
  - exact Hsvc.
  - apply Hspec. right. left. split; [exact Hbud | reflexivity].
  - cbn [eff_ret]. apply mmap_refusal_grant; assumption.
  - exact Hh.
  - reflexivity.
  - intros o Ho. apply Hspec in Ho as [-> | [[_ ->] | ->]]; [right | left; reflexivity | right].
    + eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
      split; [apply mmap_refusal_enomem; exact Hno | split; [exact Hh | reflexivity]].
    + eexists _, _, _. split; [reflexivity |]. cbn [eff_ret].
      split; [apply mmap_refusal_enomem; exact Hno |].
      destruct (mmap_guard_destroyed_facts addr nZ m) as [H1 H2].
      split; [rewrite H1; exact Hh | reflexivity].
Qed.

End WithCfg.

(* [comment removed for export] *)
Lemma lazy_interior_aligned_lz : forall (a n : word),
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  lazy_interior a n = [(a, n)].
Proof.
  intros a n Ha Hn Hpos Hwf. unfold lazy_interior, page_size in *.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as Da.
  pose proof (Z.div_mod (bv_unsigned n) 4096 ltac:(lia)) as Dn.
  rewrite Ha in Da. rewrite Hn in Dn.
  set (qa := bv_unsigned a / 4096) in *. set (qn := bv_unsigned n / 4096) in *.
  assert (E1 : (bv_unsigned a + 4096 - 1) / 4096 * 4096 = bv_unsigned a).
  { rewrite Da. replace (4096 * qa + 0 + 4096 - 1) with (qa * 4096 + 4095) by lia.
    rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. }
  assert (E2 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 = bv_unsigned a + bv_unsigned n).
  { rewrite Da, Dn. replace (4096 * qa + 0 + (4096 * qn + 0)) with ((qa + qn) * 4096) by lia.
    rewrite Z.div_mul by lia. lia. }
  cbv zeta. rewrite E1, E2.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  f_equal. f_equal.
  - apply bv_eq. rewrite u64_lit by lia. reflexivity.
  - apply bv_eq. rewrite u64_lit by lia. lia.
Qed.

Lemma mmap_grant_nr_model_facts : forall a nZ m,
  m_halted (mmap_grant_nr_model a nZ m) = m_halted m
  /\ m_vm_lazy (mmap_grant_nr_model a nZ m) = lazy_interior a (Z_to_bv 64 nZ) ++ m_vm_lazy m
  /\ m_vm_materialized (mmap_grant_nr_model a nZ m) = m_vm_materialized m
  /\ m_vmmaps (mmap_grant_nr_model a nZ m) = ledger_grant a (Z_to_bv 64 nZ) (m_vmmaps m).
Proof. intros a nZ [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
