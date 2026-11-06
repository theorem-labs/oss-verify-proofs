(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  SimInv ExitSim PropExec CatSim MmapSim AllocSim ShapeAlg DivergeSim SpinAlg SpinAlgX AgentLib RefNodes VmLimitFrame.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma budget_refused_at_alloc : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_budget_refused_b (sys_input segs ms x8) model = true ->
  budget_refused_at segs (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hb. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. left. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma mmap_mark : forall ms model x8,
  bv_unsigned x8 = 222 -> mmap_args_ok ms ->
  alloc_budget_refused_b (sys_input segs ms x8) model
  = negb (vm_backing_used model + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? vm_limit (m_vmmaps model)).
Proof.
  intros ms model x8 Hno Ha.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  destruct (alloc_mark_sysnos_dispatched (sys_input segs ms x8) model) as (_ & _ & H222 & _).
  rewrite H222 by (rewrite in_sysno_sys_input; exact Hno).
  change (in_arg (sys_input segs ms x8) 0) with (ms_gpr ms 0). change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1).
  change (in_arg (sys_input segs ms x8) 2) with (ms_gpr ms 2). change (in_arg (sys_input segs ms x8) 3) with (ms_gpr ms 3).
  change (in_arg (sys_input segs ms x8) 4) with (ms_gpr ms 4). change (in_arg (sys_input segs ms x8) 5) with (ms_gpr ms 5).
  unfold mmap_budget_refused_b. rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  unfold mmap_noreserve_backed_ok. rewrite Hflags.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_nbr : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222 ->
  mmap_args_ok ms ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  (* [comment removed for export] *)
  (nbr_limit <= vm_limit (m_vmmaps model) -> vm_backing_used model + n <= vm_limit (m_vmmaps model)) ->
  B [] ->                                                             (* [comment removed for export] *)
  (forall a, grant_ok_na (ms_gpr ms 0) model a n = true ->
     vm_backing_used model + n <= vm_limit (m_vmmaps model) ->       (* [comment removed for export] *)
     srealizes segs scfg
       (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
              (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok_na (ms_gpr ms 0) model a n = true) ->
  srealizes segs scfg (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs Halloc n Hacc HB0 HB [a0 Ha0].
  destruct (vm_backing_used model + n <=? vm_limit (m_vmmaps model)) eqn:Ebud.
  - (* [comment removed for export] *)
    apply (srz_mmap segs scfg ms model x8 B Hh Hlazy Hsvc Hno Hargs Halloc).
    + intros a Ha. apply HB; [apply grant_ok_grant_ok_na; exact Ha| apply Z.leb_le; exact Ebud].
    + exists a0. fold n. unfold grant_ok. unfold grant_ok_na in Ha0. rewrite Ha0, Ebud. reflexivity.
  - destruct (Z_lt_le_dec (vm_limit (m_vmmaps model)) nbr_limit) as [Hsmall | Hbig].
    + (* [comment removed for export] *)
      apply srz_refused.
      * apply (budget_refused_at_alloc ms model x8 Hh Hsvc).
        rewrite (mmap_mark ms model x8 Hno Hargs). fold n. rewrite Ebud. reflexivity.
      * exact Hsmall.
      * exact HB0.
    + (* [comment removed for export] *)
      exfalso. apply Z.leb_gt in Ebud. specialize (Hacc Hbig). lia.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_refused_huge : forall ms model x8 B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222 ->
  mmap_args_ok ms ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  vm_limit (m_vmmaps model) < n ->
  vm_limit (m_vmmaps model) < nbr_limit ->
  B [] ->
  srealizes segs scfg (mkCfg ms model) B.
Proof.
  intros ms model x8 B Hh Hsvc Hno Hargs n Hbig Hsmall HB.
  assert (Hused : 0 <= vm_backing_used model).
  { unfold vm_backing_used. pose proof (live_bytes_nonneg (maps_subtract_all (vm_backed_maps (m_vmmaps model)) (m_vm_lazy model))). unfold page_size. lia. }
  apply srz_refused.
  - apply (budget_refused_at_alloc ms model x8 Hh Hsvc).
    rewrite (mmap_mark ms model x8 Hno Hargs). fold n. apply Bool.negb_true_iff. apply Z.leb_gt. lia.
  - exact Hsmall.
  - exact HB.
Qed.

(* [comment removed for export] *)
Lemma mprotect_mark : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226 ->
  ms_gpr ms 0 = addr -> bv_unsigned addr mod page_size = 0 ->
  ms_gpr ms 1 = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned addr + page_round_up_Z len < two_pow_64 ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  alloc_budget_refused_b (sys_input segs ms x8) model = negb (mprotect_budget_ok model addr n).
Proof.
  intros ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  assert (Hlen' : len < two_pow_64).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  destruct (alloc_mark_sysnos_dispatched (sys_input segs ms x8) model) as (_ & _ & _ & H226).
  rewrite H226 by (rewrite in_sysno_sys_input; exact Hno).
  change (in_arg (sys_input segs ms x8) 0) with (ms_gpr ms 0). change (in_arg (sys_input segs ms x8) 1) with (ms_gpr ms 1).
  change (in_arg (sys_input segs ms x8) 2) with (ms_gpr ms 2).
  unfold mprotect_budget_refused_b. rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hna, Hma. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mprotect_at_nbr : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226 ->
  sc_alloc scfg = false ->
  ms_gpr ms 0 = addr -> bv_unsigned addr mod page_size = 0 ->
  ms_gpr ms 1 = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned addr + page_round_up_Z len < two_pow_64 ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (nbr_limit <= vm_limit (m_vmmaps model) -> mprotect_budget_ok model addr n = true) ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                             (mprotect_model addr n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno Halloc H0 Hal H1 Hlen Hnw H2 n Hna Hma Hacc HK.
  destruct (mprotect_budget_ok model addr n) eqn:Ebud.
  - exact (srz_mprotect_at segs scfg ms model x8 addr len K Hh Hlazy Hsvc Hno Halloc H0 Hal H1 Hlen Hnw H2 Hna Hma Ebud HK).
  - destruct (Z_lt_le_dec (vm_limit (m_vmmaps model)) nbr_limit) as [Hsmall | Hbig].
    + apply srz_refused.
      * apply (budget_refused_at_alloc ms model x8 Hh Hsvc).
        rewrite (mprotect_mark ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma). fold n. rewrite Ebud. reflexivity.
      * exact Hsmall.
      * exact (srealizes_nonempty segs scfg _ _ HK).
    + specialize (Hacc Hbig). discriminate Hacc.
Qed.

End WithSegs.
