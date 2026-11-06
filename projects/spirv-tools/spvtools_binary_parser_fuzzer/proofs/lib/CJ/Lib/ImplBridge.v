(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec AgentLib CatSim ShapeAlg SRealizes MmapSim AllocSim RefNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Nodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section Bridge.
Variable segs : list Segment.

Lemma msteps_cj_fw : forall ms ms', Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hst] _ IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact Hst | exact IH].
Qed.

Lemma srz_evt : forall (P : machine_state -> Prop) ms mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  evt segs P ms ->
  (forall ms', P ms' -> srealizes segs (mkCfg ms' mo) T) ->
  srealizes segs (mkCfg ms mo) T.
Proof.
  intros P ms mo T Hh Hl (ms' & Hrun & HP) HK.
  eapply srz_msteps; [exact Hh | exact Hl | apply msteps_cj_fw; exact Hrun | apply HK; exact HP].
Qed.

Lemma kgrant_ok_spec : forall hint m a n, alloc_top (m_vmmaps m) = alloc_ceiling ->
  kgrant_ok hint m a n = MmapSim.grant_ok hint m a n.
Proof. intros hint m a n E. unfold kgrant_ok, MmapSim.grant_ok. rewrite E. reflexivity. Qed.
Lemma kgrant_ok_na_spec : forall hint m a n, alloc_top (m_vmmaps m) = alloc_ceiling ->
  kgrant_ok_na hint m a n = RefNodes.grant_ok_na hint m a n.
Proof. intros hint m a n E. unfold kgrant_ok_na, RefNodes.grant_ok_na. rewrite E. reflexivity. Qed.

Definition node_char (n : node) (ms : machine_state) (mo : Model) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
             exists eff mo', nstep n mo eff mo' [] /\ o = LinuxProcessSem.Monad.Ok eff mo' []) /\
  (exists eff mo', nstep n mo eff mo' []).

Definition mstd' (mo : Model) : Prop :=
  m_halted mo = None /\ m_vm_lazy mo = [] /\ m_vm_materialized mo = []
  /\ alloc_top (m_vmmaps mo) = alloc_ceiling.

Lemma mstd'_with_vmmaps : forall h mo, vm_init_sp h = vm_init_sp (m_vmmaps mo) -> mstd' mo -> mstd' (with_vmmaps h mo).
Proof.
  intros h mo Hsp (A & B & C & D). unfold mstd' in *. refine (conj A (conj B (conj C _))).
  unfold alloc_top in *. change (m_vmmaps (with_vmmaps h mo)) with h. rewrite Hsp. exact D.
Qed.

Lemma mstd'_forget : forall lo hi mo, mstd' mo -> mstd' (vm_forget_range lo hi mo).
Proof.
  intros lo hi mo (A & B & C & D). unfold vm_forget_range, with_vm_backing, mstd', m_halted, m_vm_lazy, m_vm_materialized in *.
  cbn. rewrite B, C. cbn. auto.
Qed.

Lemma nstep_mstd' : forall n mo eff mo', mstd' mo -> nstep n mo eff mo' [] -> mstd' mo'.
Proof.
  intros n mo eff mo' Hs Hn. destruct n; cbn in Hn; try (destruct Hn as [_ Hn]; contradiction).
  -   destruct Hn as [_ Hn]. destruct (req =? 0).
    + destruct Hn as [_ ->]. exact Hs.
    + destruct Hn as [[_ ->] | (_ & _ & ->)]; [exact Hs | apply mstd'_with_vmmaps; [reflexivity | exact Hs]].
  -   destruct Hn as [_ Hn].
    destruct ((flags =? MAP_ANON_PRIV) && (prot =? PROT_RW_Z)).
    { destruct Hn as [(e & _ & _ & ->) | (a & _ & _ & ->)]; [exact Hs | apply mstd'_with_vmmaps; [reflexivity | exact Hs]]. }
    destruct ((flags =? MAP_ANON_PRIV) && (prot =? 0)).
    { destruct Hn as [(e & _ & _ & ->) | (a & _ & _ & ->)]; [exact Hs | apply mstd'_with_vmmaps; [reflexivity | exact Hs]]. }
    destruct ((flags =? MAP_ANON_PRIV_FIXED) && (prot =? 0)); [|contradiction].
    destruct Hn as [(e & _ & _ & ->) | [(_ & ->) | (e & _ & _ & ->)]];
      [exact Hs | apply mstd'_forget; apply mstd'_with_vmmaps; [reflexivity | exact Hs] | apply mstd'_forget; apply mstd'_with_vmmaps; [reflexivity | exact Hs]].
  -   destruct Hn as [_ [_ ->]]. unfold kmunmap_model, with_mmap_destroyed. apply mstd'_forget; apply mstd'_with_vmmaps; [reflexivity | exact Hs].
  -   destruct Hn as [_ [(e & _ & _ & ->) | (_ & _ & ->)]]; [exact Hs | apply mstd'_with_vmmaps; [reflexivity | exact Hs]].
Qed.

Lemma areg_gpr0 : forall ms, ms_gpr ms 0 = areg ms 10. Proof. reflexivity. Qed.
Lemma areg_gpr1 : forall ms, ms_gpr ms 1 = areg ms 11. Proof. reflexivity. Qed.
Lemma areg_gpr2 : forall ms, ms_gpr ms 2 = areg ms 12. Proof. reflexivity. Qed.
Lemma areg_gpr3 : forall ms, ms_gpr ms 3 = areg ms 13. Proof. reflexivity. Qed.
Lemma areg_gpr4 : forall ms, ms_gpr ms 4 = areg ms 14. Proof. reflexivity. Qed.
Lemma areg_gpr5 : forall ms, ms_gpr ms 5 = areg ms 15. Proof. reflexivity. Qed.

Lemma nstep_brk0_unfold : forall mo eff mo',
  nstep (NBrk 0) mo eff mo' [] <-> (eff = eff0 (vm_brk (m_vmmaps mo)) /\ mo' = mo).
Proof. intros. unfold nstep. cbn [Z.eqb]. split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]]. Qed.

Lemma nstep_brk_grow_unfold : forall req mo eff mo', req <> 0 ->
  nstep (NBrk req) mo eff mo' [] <->
  ((eff = eff0 (vm_brk (m_vmmaps mo)) /\ mo' = mo)
   \/ (kbrk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true
       /\ eff = mkEffect (Z_to_bv 64 req) [] [(vm_brk (m_vmmaps mo), Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo))))]
       /\ mo' = kbrk_grow_model (req - bv_unsigned (vm_brk (m_vmmaps mo))) mo)).
Proof.
  intros req mo eff mo' Hr. unfold nstep. rewrite (proj2 (Z.eqb_neq _ _) Hr).
  split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]].
Qed.

Lemma node_char_brk : forall req ms mo,
  at_node segs (NBrk req) ms -> nsafe (NBrk req) mo -> mstd' mo -> node_char (NBrk req) ms mo.
Proof.
  intros req ms mo [Hsvc Ha0] Hsafe (Hh & Hl & Hm & Hc).
  exists (Z_to_bv 64 214). split; [exact Hsvc|].
  assert (Hno : bv_unsigned (Z_to_bv 64 214) = 214) by reflexivity.
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 req) by (rewrite areg_gpr0; exact Ha0).
  destruct (Z.eq_dec req 0) as [-> | Hnz].
  -
    assert (Hcases : forall r, brk_resolution_ok mo (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps mo)).
    { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
      unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
    split.
    + intros o. rewrite (brk_outcome_si segs ms _ mo o Hno). split.
      * intros (r & Hr & ->). apply Hcases in Hr. subst r. exists (eff0 (vm_brk (m_vmmaps mo))), mo.
        split; [apply nstep_brk0_unfold; auto|].
        rewrite H0, brk_zeros_query, brk_unmaps_keep, (brk_model_query _ mo eq_refl), vmmaps_eta, with_vmmaps_eta. reflexivity.
      * intros (eff & mo' & Hn & ->). apply nstep_brk0_unfold in Hn as [-> ->].
        exists (vm_brk (m_vmmaps mo)). split; [apply Hcases; reflexivity|].
        rewrite H0, brk_zeros_query, brk_unmaps_keep, (brk_model_query _ mo eq_refl), vmmaps_eta, with_vmmaps_eta. reflexivity.
    + exists (eff0 (vm_brk (m_vmmaps mo))), mo. apply nstep_brk0_unfold. auto.
  -
    destruct Hsafe as [-> | Hsafe]; [exfalso; apply Hnz; reflexivity|].
    cbv zeta in Hsafe. destruct Hsafe as (Hbal & Hral & Hb0 & Hbr & Hs).
    set (d := req - bv_unsigned (vm_brk (m_vmmaps mo))).
    set (reqw := Z_to_bv 64 req) in *.
    assert (Hureq : bv_unsigned reqw = req) by (unfold reqw; apply u64_lit; lia).
    pose proof (kbrk_grow_ok_spec mo reqw reqw Hc) as Ek.
    assert (Ereq : req = bv_unsigned (vm_brk (m_vmmaps mo)) + d) by (unfold d; lia).
    assert (Hcases : forall r, brk_resolution_ok mo (ms_gpr ms 0) r <->
                     (r = vm_brk (m_vmmaps mo) \/ (r = reqw /\ Mmap.brk_grow_ok mo reqw reqw = true))).
    { intros r. rewrite H0. apply brk_r_ok_grow_cases; rewrite ?Hureq; lia. }
    assert (Hneq : reqw <> vm_brk (m_vmmaps mo)).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. lia. }
    assert (Hreq0 : reqw <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
    assert (Hlt : bv_unsigned (vm_brk (m_vmmaps mo)) < bv_unsigned reqw) by (rewrite Hureq; lia).
    assert (Hdal : d mod page_size = 0).
    { unfold d. unfold page_size in *. rewrite Zminus_mod, Hral, Hbal. reflexivity. }
    assert (Hd : 0 < d) by (unfold d; lia).
    assert (Hnw : bv_unsigned (vm_brk (m_vmmaps mo)) + d < 2 ^ 64) by (unfold d; lia).

    assert (Egrant : Mmap.brk_grow_ok mo reqw reqw = true ->
              LinuxProcessSem.Monad.Ok (mkEffectU reqw [] (brk_zeros (ms_gpr ms 0) reqw (vm_brk (m_vmmaps mo))) (brk_unmaps reqw (vm_brk (m_vmmaps mo))) [] [])
                 (brk_model (ms_gpr ms 0) reqw mo) []
              = LinuxProcessSem.Monad.Ok (mkEffect reqw [] [(vm_brk (m_vmmaps mo), Z_to_bv 64 d)]) (kbrk_grow_model d mo) []).
    { intros Hg. rewrite H0.
      rewrite (brk_zeros_grow reqw reqw (vm_brk (m_vmmaps mo)) Hreq0 Hb0 Hlt), (brk_unmaps_grow reqw (vm_brk (m_vmmaps mo))) by lia.
      unfold brk_page_range.
      rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk (m_vmmaps mo)))) by (first [lia | exact Hbal]).
      rewrite (page_round_up_Z_aligned (bv_unsigned reqw)) by (rewrite Hureq; first [lia | exact Hral]).
      rewrite (proj2 (Z.ltb_lt _ _) Hlt).
      replace (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps mo)))) with (vm_brk (m_vmmaps mo)) by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
      rewrite Hureq. fold d.
      unfold reqw. rewrite Ereq. rewrite (brk_model_grow_eq mo d Hd Hb0 Hnw Hbal Hdal). reflexivity. }
    assert (Ekeep : LinuxProcessSem.Monad.Ok (mkEffectU (vm_brk (m_vmmaps mo)) [] (brk_zeros (ms_gpr ms 0) (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))) (brk_unmaps (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))) [] [])
                       (brk_model (ms_gpr ms 0) (vm_brk (m_vmmaps mo)) mo) []
                    = LinuxProcessSem.Monad.Ok (eff0 (vm_brk (m_vmmaps mo))) mo []).
    { rewrite brk_zeros_keep, brk_unmaps_keep, brk_model_keep. reflexivity. }
    split.
    + intros o. rewrite (brk_outcome_si segs ms _ mo o Hno). split.
      * intros (r & Hr & ->). destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
        -- exists (eff0 (vm_brk (m_vmmaps mo))), mo. split; [apply (nstep_brk_grow_unfold req mo _ _ Hnz); left; auto|]. exact Ekeep.
        -- exists (mkEffect reqw [] [(vm_brk (m_vmmaps mo), Z_to_bv 64 d)]), (kbrk_grow_model d mo).
           split; [apply (nstep_brk_grow_unfold req mo _ _ Hnz); right; split; [change (kbrk_grow_ok mo reqw reqw = true); rewrite Ek; exact Hg | auto]|]. exact (Egrant Hg).
      * intros (eff & mo' & Hn & ->). apply (nstep_brk_grow_unfold req mo _ _ Hnz) in Hn. fold d in Hn.
        destruct Hn as [[-> ->] | (Hg & -> & ->)].
        -- exists (vm_brk (m_vmmaps mo)). split; [apply Hcases; left; reflexivity|]. symmetry. exact Ekeep.
        -- change (kbrk_grow_ok mo reqw reqw = true) in Hg. rewrite Ek in Hg. exists reqw. split; [apply Hcases; right; auto|]. symmetry. exact (Egrant Hg).
    + exists (eff0 (vm_brk (m_vmmaps mo))), mo. apply nstep_brk_grow_unfold; [exact Hnz|]. left. auto.
Qed.

Lemma node_char_munmap : forall addr len ms mo,
  at_node segs (NMunmap addr len) ms -> nsafe (NMunmap addr len) mo -> mstd' mo -> node_char (NMunmap addr len) ms mo.
Proof.
  intros addr len ms mo (Hsvc & Ha0 & Ha1) Hsafe (Hh & Hl & Hm).
  cbv zeta in Hsafe. unfold nsafe in Hsafe. destruct Hsafe as (Hal & Hlen & Ha0' & Hnw & Hhas).
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  assert (HTS : TASK_SIZE = 0x800000000000) by reflexivity.
  exists (Z_to_bv 64 215). split; [exact Hsvc|].
  assert (Hno : bv_unsigned (Z_to_bv 64 215) = 215) by reflexivity.
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 addr) by (rewrite areg_gpr0; exact Ha0).
  assert (H1 : ms_gpr ms 1 = Z_to_bv 64 len) by (rewrite areg_gpr1; exact Ha1).
  assert (Hu0 : bv_unsigned (ms_gpr ms 0) = addr) by (rewrite H0; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (Hpru : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)) by (unfold page_round_up; rewrite Hu1; reflexivity).
  assert (Hargs : munmap_args_ok ms mo).
  { unfold munmap_args_ok. rewrite Hu0, Hu1, Hpru, H0. repeat split; try assumption.
    intros E. apply (f_equal bv_unsigned) in E. rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
  assert (En : forall eff mo', nstep (NMunmap addr len) mo eff mo' [] <->
            (eff = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] []
             /\ mo' = kmunmap_model (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) mo)).
  { intros eff mo'. unfold nstep. cbv zeta. split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]]. }
  split.
  - intros o. rewrite (munmap_outcome_si segs ms _ mo o Hno Hargs). unfold munmap_eff. rewrite Hpru, H0. split.
    + intros ->. eexists _, _. split; [apply En; split; reflexivity | reflexivity].
    + intros (eff & mo' & Hn & ->). apply En in Hn as [-> ->]. reflexivity.
  - eexists _, _. apply En. split; reflexivity.
Qed.

Lemma node_char_mprotect : forall addr len prot ms mo,
  at_node segs (NMprotect addr len prot) ms -> nsafe (NMprotect addr len prot) mo -> mstd' mo ->
  node_char (NMprotect addr len prot) ms mo.
Proof.
  intros addr len prot ms mo (Hsvc & Ha0 & Ha1 & Ha2) Hsafe (Hh & Hl & Hm).
  unfold nsafe in Hsafe. cbv zeta in Hsafe. destruct Hsafe as (-> & Hal & Hlen & Ha0' & Hnw & Hna & Hma).
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  exists (Z_to_bv 64 226). split; [exact Hsvc|].
  assert (Hno : bv_unsigned (Z_to_bv 64 226) = 226) by reflexivity.
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 addr) by (rewrite areg_gpr0; exact Ha0).
  assert (H1 : ms_gpr ms 1 = Z_to_bv 64 len) by (rewrite areg_gpr1; exact Ha1).
  assert (H2 : ms_gpr ms 2 = Z_to_bv 64 3) by (rewrite areg_gpr2; exact Ha2).
  assert (Hua : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; lia).
  pose proof (mprotect_outcome_si segs ms _ mo (Z_to_bv 64 addr) len Hno H0 ltac:(rewrite Hua; exact Hal) H1 Hlen
                ltac:(rewrite Hua; exact Hnw) H2 Hna Hma) as Hchk.
  cbv zeta in Hchk.
  assert (En : forall eff mo', nstep (NMprotect addr len PROT_RW_Z) mo eff mo' [] <->
            ((exists e, In e mprotect_errnos /\ eff = efferr e /\ mo' = mo)
             \/ (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
                 /\ eff = mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]
                 /\ mo' = kmprotect_model (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) mo))).
  { intros eff mo'. unfold nstep. cbv zeta. split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]]. }
  split.
  - intros o. rewrite (Hchk o). split.
    + intros [(e & He & ->) | (Hbud & ->)].
      * exists (efferr e), mo. split; [apply En; left; exists e; auto | reflexivity].
      * eexists _, _. split; [apply En; right; split; [exact Hbud | split; reflexivity] | reflexivity].
    + intros (eff & mo' & Hn & ->). apply En in Hn as [(e & He & -> & ->) | (Hbud & -> & ->)].
      * left. exists e. auto.
      * right. auto.
  - exists (efferr ENOMEM), mo. apply En. left. exists ENOMEM. split; [apply ENOMEM_in_mprotect_errnos | auto].
Qed.

Lemma node_char_mmap : forall addr len prot flags ms mo,
  at_node segs (NMmap addr len prot flags) ms -> nsafe (NMmap addr len prot flags) mo -> mstd' mo ->
  node_char (NMmap addr len prot flags) ms mo.
Proof.
  intros addr len prot flags ms mo (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) Hsafe (Hh & Hl & Hm & Hc).
  unfold nsafe in Hsafe. cbv zeta in Hsafe. destruct Hsafe as [Hlen Hcase].
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  exists (Z_to_bv 64 222). split; [exact Hsvc|].
  assert (Hno : bv_unsigned (Z_to_bv 64 222) = 222) by reflexivity.
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 addr) by (rewrite areg_gpr0; exact Ha0).
  assert (H1 : ms_gpr ms 1 = Z_to_bv 64 len) by (rewrite areg_gpr1; exact Ha1).
  assert (H2 : ms_gpr ms 2 = Z_to_bv 64 prot) by (rewrite areg_gpr2; exact Ha2).
  assert (H3 : ms_gpr ms 3 = Z_to_bv 64 flags) by (rewrite areg_gpr3; exact Ha3).
  assert (H4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by (rewrite areg_gpr4; exact Ha4).
  assert (H5 : ms_gpr ms 5 = Z_to_bv 64 0) by (rewrite areg_gpr5; exact Ha5).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (Hl0 : ms_gpr ms 1 <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
  assert (Hpru : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)) by (unfold page_round_up; rewrite Hu1; reflexivity).
  destruct Hcase as [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & Hal & Hpos & Hce & Hrf & Hmc)]].
  -
    assert (Hargs : mmap_args_ok ms) by (unfold mmap_args_ok; rewrite H2, H3, H4, H5; repeat split; try reflexivity; exact Hl0).
    assert (En : forall eff mo', nstep (NMmap 0 len PROT_RW_Z MAP_ANON_PRIV) mo eff mo' [] <->
            ((exists e, In e mmap_errnos /\ eff = efferr e /\ mo' = mo)
             \/ (exists a, kgrant_ok (Z_to_bv 64 0) mo a (page_round_up_Z len) = true
                   /\ eff = mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]
                   /\ mo' = kmmap_model a (Z_to_bv 64 (page_round_up_Z len)) mo))).
    { intros eff mo'. unfold nstep. cbv zeta. cbn [Z.eqb MAP_ANON_PRIV PROT_RW_Z Pos.eqb andb].
      split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]]. }
    split.
    + intros o. rewrite (mmap_outcome_si segs ms _ mo o Hno Hargs). rewrite Hu1, Hpru, H0.
      setoid_rewrite <- (kgrant_ok_spec _ mo _ _ Hc). split.
      * intros [(e & He & ->) | (a & Hg & ->)].
        -- exists (efferr e), mo. split; [apply En; left; exists e; auto | reflexivity].
        -- eexists _, _. split; [apply En; right; exists a; split; [exact Hg | split; reflexivity] | reflexivity].
      * intros (eff & mo' & Hn & ->). apply En in Hn as [(e & He & -> & ->) | (a & Hg & -> & ->)].
        -- left. exists e. auto.
        -- right. exists a. auto.
    + exists (efferr ENOMEM), mo. apply En. left. exists ENOMEM. split; [apply ENOMEM_in_mmap_errnos | auto].
  -
    assert (Hargs : mmap_noaccess_args_ok ms) by (unfold mmap_noaccess_args_ok; rewrite H2, H3, H4, H5; repeat split; try reflexivity; exact Hl0).
    pose proof (mmap_noaccess_outcome_si segs ms _ mo Hno Hargs) as Hchk. cbv zeta in Hchk. rewrite Hu1, H0 in Hchk.
    setoid_rewrite <- (kgrant_ok_na_spec _ mo _ _ Hc) in Hchk.
    assert (En : forall eff mo', nstep (NMmap 0 len 0 MAP_ANON_PRIV) mo eff mo' [] <->
            ((exists e, In e mmap_errnos /\ eff = efferr e /\ mo' = mo)
             \/ (exists a, kgrant_ok_na (Z_to_bv 64 0) mo a (page_round_up_Z len) = true
                   /\ eff = mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] []
                   /\ mo' = knoaccess_model a (Z_to_bv 64 (page_round_up_Z len)) mo))).
    { intros eff mo'. unfold nstep. cbv zeta. cbn [Z.eqb MAP_ANON_PRIV PROT_RW_Z Pos.eqb andb].
      split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]]. }
    split.
    + intros o. rewrite (Hchk o). split.
      * intros [(e & He & ->) | (a & Hg & ->)].
        -- exists (efferr e), mo. split; [apply En; left; exists e; auto | reflexivity].
        -- eexists _, _. split; [apply En; right; exists a; split; [exact Hg | split; reflexivity] | reflexivity].
      * intros (eff & mo' & Hn & ->). apply En in Hn as [(e & He & -> & ->) | (a & Hg & -> & ->)].
        -- left. exists e. auto.
        -- right. exists a. auto.
    + exists (efferr ENOMEM), mo. apply En. left. exists ENOMEM. split; [apply ENOMEM_in_mmap_errnos | auto].
  -
    assert (Hargs : mmap_fixed_args_ok ms) by (unfold mmap_fixed_args_ok; rewrite H2, H3, H4, H5; repeat split; try reflexivity; exact Hl0).
    assert (Hua : bv_unsigned (Z_to_bv 64 addr) = addr).
    { apply u64_lit. pose proof (RelSpec.alloc_top_lt_2_64 (m_vmmaps mo)) as HT. unfold two_pow_64 in HT.
      pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
    pose proof (mmap_fixed_outcome_si segs ms _ mo (Z_to_bv 64 addr) len Hno Hargs H0 ltac:(rewrite Hua; exact Hal)
                  ltac:(rewrite Hua; exact Hpos) H1 (proj1 Hlen) ltac:(rewrite Hua, Hc; exact Hce) Hrf Hmc) as Hchk.
    cbv zeta in Hchk.
    assert (En : forall eff mo', nstep (NMmap addr len 0 MAP_ANON_PRIV_FIXED) mo eff mo' [] <->
            ((exists e, In e mmap_errnos /\ eff = efferr e /\ mo' = mo)
             \/ (eff = mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] []
                 /\ mo' = kfixna_model (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) mo)
             \/ (exists e, In e mmap_errnos
                   /\ eff = mkEffectU (errno_ret e) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] []
                   /\ mo' = kfixlost_model (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) mo))).
    { intros eff mo'. unfold nstep. cbv zeta. cbn [Z.eqb MAP_ANON_PRIV MAP_ANON_PRIV_FIXED PROT_RW_Z Pos.eqb andb].
      split; [intros [_ H]; exact H | intros H; split; [reflexivity | exact H]]. }
    split.
    + intros o. rewrite (Hchk o). split.
      * intros [(e & He & ->) | [-> | (e & He & ->)]].
        -- exists (efferr e), mo. split; [apply En; left; exists e; auto | reflexivity].
        -- eexists _, _. split; [apply En; right; left; split; reflexivity | reflexivity].
        -- eexists _, _. split; [apply En; right; right; exists e; split; [exact He | split; reflexivity] | reflexivity].
      * intros (eff & mo' & Hn & ->). apply En in Hn as [(e & He & -> & ->) | [[-> ->] | (e & He & -> & ->)]].
        -- left. exists e. auto.
        -- right; left. reflexivity.
        -- right; right. exists e. auto.
    + exists (efferr ENOMEM), mo. apply En. left. exists ENOMEM. split; [apply ENOMEM_in_mmap_errnos | auto].
Qed.

Lemma node_char_of : forall n ms mo,
  at_node segs n ms -> nsafe n mo -> mstd' mo -> node_char n ms mo.
Proof.
  intros n ms mo Hat Hsafe Hstd. destruct n; try (exfalso; exact Hsafe).
  - apply node_char_brk; assumption.
  - apply node_char_mmap; assumption.
  - apply node_char_munmap; assumption.
  - apply node_char_mprotect; assumption.
Qed.

Lemma nrefusal_refusal_b : forall n ms x8 mo eff mo',
  at_node segs n ms -> ms_svc_pending ms = Some x8 -> nstep n mo eff mo' [] ->
  forall e, refusal_b (sys_input segs ms x8) mo (eff_ret e) = nrefusal n mo e.
Proof.
  intros n ms x8 mo eff mo' Hat Hsvc Hn e.
  destruct n; try (destruct Hn as [_ Hn]; contradiction); cbn [at_node] in Hat.
  - destruct Hat as (Hs & H10). rewrite Hs in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [nrefusal].
    change (bv_unsigned (Z_to_bv 64 214) =? 214)%Z with true. cbv iota.
    rewrite in_a0_si. rewrite H10. reflexivity.
  - destruct Hat as (Hs & _). rewrite Hs in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [nrefusal]. vm_compute (bv_unsigned (Z_to_bv 64 222)).
    cbn. rewrite Bool.orb_false_r. reflexivity.
  - destruct Hat as (Hs & _). rewrite Hs in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [nrefusal]. reflexivity.
  - destruct Hat as (Hs & _). rewrite Hs in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [nrefusal]. reflexivity.
Qed.

Lemma nfamily_off : forall n ms x8 mo eff mo',
  at_node segs n ms -> ms_svc_pending ms = Some x8 -> nstep n mo eff mo' [] ->
  injected_family_off CFG (sys_input segs ms x8) = false ->
  forall e, nrefusal n mo e = false.
Proof.
  intros n ms x8 mo eff mo' Hat Hsvc Hn Hoff e.
  destruct n; try (destruct Hn as [_ Hn]; contradiction); cbn [at_node] in Hat; destruct Hat as (Hs & _);
    rewrite Hs in Hsvc; injection Hsvc as <-; rewrite injected_family_off_CFG, in_sysno_si in Hoff;
    try (vm_compute in Hoff; discriminate Hoff).
  reflexivity.
Qed.

Lemma nspurious_iff : forall n ms mo x8 eff mo',
  at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
             exists eff mo', nstep n mo eff mo' [] /\ o = LinuxProcessSem.Monad.Ok eff mo' []) ->
  nstep n mo eff mo' [] ->
  (~ spurious_refusal_cfg CFG (sys_input segs ms x8) mo eff <-> nstep_cfg n mo eff mo' []).
Proof.
  intros n ms mo x8 eff mo' Hat Hsvc Hchar Hn.
  pose proof (nrefusal_refusal_b n ms x8 mo eff mo' Hat Hsvc Hn) as HR.
  split.
  - intros Hns. split; [exact Hn |]. intros Hr eff' mo'' evs' Hn'.
    destruct (nrefusal n mo eff') eqn:E; [reflexivity |]. exfalso. apply Hns.
    destruct (injected_family_off CFG (sys_input segs ms x8)) eqn:Hoff.
    + split; [exact Hoff |]. split; [rewrite HR; exact Hr |].
      pose proof (proj1 Hn') as ->.
      exists eff', mo'', []. split; [apply Hchar; exists eff', mo''; auto |]. rewrite HR. exact E.
    + rewrite (nfamily_off n ms x8 mo eff mo' Hat Hsvc Hn Hoff eff) in Hr. discriminate Hr.
  - intros [_ Hcfg] (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)).
    rewrite HR in Hr, Hnr. apply Hchar in Hs. destruct Hs as (e2 & mo2 & Hn2 & E2).
    injection E2 as -> -> ->.
    rewrite (Hcfg Hr e2 mo2 [] Hn2) in Hnr. discriminate Hnr.
Qed.

Lemma srz_svc_fam : forall n ms mo x8 (T : resp -> Model -> TSet),
  at_node segs n ms ->
  m_halted mo = None -> m_vm_lazy mo = [] -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
             exists eff mo', nstep n mo eff mo' [] /\ o = LinuxProcessSem.Monad.Ok eff mo' []) ->
  (exists eff mo', nstep n mo eff mo' []) ->
  (forall eff mo', nstep n mo eff mo' [] -> m_halted mo' = None /\ m_vm_lazy mo' = []) ->
  (forall eff mo', nstep_cfg n mo eff mo' [] -> srealizes segs (mkCfg (nret ms eff) mo') (T eff mo')) ->
  srealizes segs (mkCfg ms mo)
    (fun tr => tr = [] \/ exists eff mo', nstep_cfg n mo eff mo' [] /\ T eff mo' tr).
Proof.
  intros n ms mo x8 T Hat Hh Hl Hsvc Hchar (eff0_ & mo0 & H0) Hpost HK.
  set (I := { p : resp * Model | nstep n mo (fst p) (snd p) [] }).
  set (R := fun o => exists eff mo', nstep n mo eff mo' [] /\ o = LinuxProcessSem.Monad.Ok eff mo' []).
  assert (Hin : forall i : I, R (LinuxProcessSem.Monad.Ok (fst (proj1_sig i)) (snd (proj1_sig i)) [])).
  { intros [[eff mo'] Ho]. cbn. exists eff, mo'. split; [exact Ho | reflexivity]. }
  assert (Hout : forall o, R o -> exists i : I, o = LinuxProcessSem.Monad.Ok (fst (proj1_sig i)) (snd (proj1_sig i)) []).
  { intros o (eff & mo' & Ho & ->). exists (exist _ (eff, mo') Ho). reflexivity. }
  assert (HN := Nodes.node_family_cfg segs ms mo x8 I (fun i => fst (proj1_sig i)) (fun i => snd (proj1_sig i))
                  (fun _ => []) R Hh Hsvc Hchar Hin Hout
                  ltac:(intros [[eff mo'] Ho]; exact (proj1 (Hpost eff mo' Ho)))
                  ltac:(intros [[eff mo'] Ho]; exact (proj2 (Hpost eff mo' Ho)))).
  pose (j0 := Nodes.family_cfg_nonempty segs ms mo x8 I (fun i => fst (proj1_sig i)) (fun i => snd (proj1_sig i))
                (fun _ => []) R Hchar Hout (exist _ (eff0_, mo0) H0)).
  eapply srz_conseq.
  - eapply (srz_node segs (mkCfg ms mo) _ (fun _ => []) _
             (fun j => T (fst (proj1_sig (proj1_sig j))) (snd (proj1_sig (proj1_sig j)))) j0 HN).
    intros [[[eff mo'] Ho] Hns]. cbn. apply HK.
    exact (proj1 (nspurious_iff n ms mo x8 eff mo' Hat Hsvc Hchar Ho) Hns).
  - intros tr. unfold t_alt, t_emit. split.
    + intros [[[[eff mo'] Ho] Hns] [Hp | (tr' & -> & Ht)]]; cbn in *.
      * left. destruct tr; [reflexivity | destruct Hp].
      * right. exists eff, mo'. split; [| exact Ht].
        exact (proj1 (nspurious_iff n ms mo x8 eff mo' Hat Hsvc Hchar Ho) Hns).
    + intros [-> | (eff & mo' & Hc & Ht)].
      * exists j0. left. constructor.
      * exists (exist _ (exist _ (eff, mo') (nstep_cfg_sub _ _ _ _ _ Hc))
                  (proj2 (nspurious_iff n ms mo x8 eff mo' Hat Hsvc Hchar (nstep_cfg_sub _ _ _ _ _ Hc)) Hc)).
        right. exists tr. auto.
Qed.

Fixpoint tset {R : Type} (t : itree node R) (mo : Model) (KL : R -> Model -> TSet) : TSet :=
  match t with
  | Ret r => KL r mo
  | Vis n k => fun tr => tr = [] \/ exists eff mo', nstep_cfg n mo eff mo' [] /\ tset (k eff) mo' KL tr
  end.

Lemma nstep_evs_nil : forall n mo eff mo' evs, nstep n mo eff mo' evs -> evs = [].
Proof. intros n mo eff mo' evs [H _]. exact H. Qed.

Theorem srz_impl : forall {R : Type} (t : itree node R) Q P ms mo (KL : R -> Model -> TSet),
  impl segs (at_node segs) t Q ms -> twf t mo P -> mstd' mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> mstd' mo' -> srealizes segs (mkCfg ms' mo') (KL r mo')) ->
  srealizes segs (mkCfg ms mo) (tset t mo KL).
Proof.
  intros R t. induction t as [r | n k IH]; intros Q P ms mo KL Himpl Htwf Hstd HL.
  - cbn in Himpl, Htwf |- *. pose proof Hstd as (Hh & Hl & Hm).
    eapply srz_evt; [exact Hh | exact Hl | exact Himpl |].
    intros ms' HQ. apply (HL r ms' mo HQ Htwf). exact Hstd.
  - cbn in Himpl, Htwf. cbn [tset]. destruct Htwf as [Hsafe Hk]. pose proof Hstd as (Hh & Hl & Hm).
    eapply srz_evt; [exact Hh | exact Hl | exact Himpl |].
    intros ms1 [Hat Himpl1].
    destruct (node_char_of n ms1 mo Hat Hsafe Hstd) as (x8 & Hsvc & Hchar & Hex).
    apply (srz_svc_fam n ms1 mo x8 (fun eff mo' => tset (k eff) mo' KL) Hat Hh Hl Hsvc Hchar Hex).
    + intros eff mo' Hn. pose proof (nstep_mstd' n mo eff mo' Hstd Hn) as (A & B & C & D). auto.
    + intros eff mo' Hn. apply nstep_cfg_sub in Hn.
      apply (IH eff Q P); [apply Himpl1 | apply (Hk eff mo' []); exact Hn | exact (nstep_mstd' n mo eff mo' Hstd Hn) | exact HL].
Qed.

Lemma tpath_cfg_sub : forall {R : Type} (t : itree node R) mo tr r mo',
  tpath nstep_cfg t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros R t. induction t as [r0 | n k IH]; intros mo tr r mo' Hp; cbn in *; [exact Hp |].
  destruct Hp as (rsp & mo1 & evs & tr' & Hn & Hp & E). exists rsp, mo1, evs, tr'.
  split; [exact (nstep_cfg_sub _ _ _ _ _ Hn) |]. split; [exact (IH rsp mo1 tr' r mo' Hp) | exact E].
Qed.

Lemma tpath_mstd' : forall {R : Type} (t : itree node R) mo tr r mo',
  mstd' mo -> tpath nstep t mo tr r mo' -> mstd' mo'.
Proof.
  intros R t. induction t as [r0 | n k IH]; intros mo tr r mo' Hs Hp; cbn in *.
  - destruct Hp as (_ & -> & _). exact Hs.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hn & Hp & _). pose proof (nstep_evs_nil _ _ _ _ _ Hn) as ->.
    exact (IH rsp mo1 tr' r mo' (nstep_mstd' n mo rsp mo1 Hs Hn) Hp).
Qed.

Fixpoint twf_cfg {R : Type} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep_cfg n mo rsp mo' evs -> twf_cfg (k rsp) mo' P
  end.

Lemma twf_twf_cfg : forall {R : Type} (t : itree node R) mo P, twf t mo P -> twf_cfg t mo P.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H |].
  destruct H as [Hs Hk]. split; [exact Hs |]. intros rsp mo' evs Hn.
  apply IH. apply (Hk rsp mo' evs). exact (nstep_cfg_sub _ _ _ _ _ Hn).
Qed.

Lemma twf_cfg_with_path : forall {R : Type} (t : itree node R) mo (P Q : R -> Model -> Prop),
  twf_cfg t mo P -> (forall r mo', tpath nstep_cfg t mo [] r mo' -> Q r mo') ->
  twf_cfg t mo (fun r mo' => P r mo' /\ Q r mo').
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P Q H HQ; cbn in *.
  - split; [exact H |]. apply HQ. auto.
  - destruct H as [Hs Hk]. split; [exact Hs |]. intros rsp mo' evs Hn.
    pose proof (nstep_evs_nil _ _ _ _ _ (nstep_cfg_sub _ _ _ _ _ Hn)) as ->.
    apply IH; [exact (Hk _ _ _ Hn) |]. intros r mo2 Hp. apply HQ. exists rsp, mo', [], []. auto.
Qed.

Lemma twf_cfg_leaf_exists : forall {R : Type} (t : itree node R) mo P,
  twf_cfg t mo P -> (forall n mo1, nsafe n mo1 -> exists eff mo', nstep n mo1 eff mo' []) ->
  exists r mo', tpath nstep_cfg t mo [] r mo' /\ P r mo'.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P H HEX; cbn in *.
  - exists r, mo. auto.
  - destruct H as [Hs Hk]. destruct (HEX n mo Hs) as (eff & mo1 & Hn).
    destruct (nstep_cfg_exists n mo eff mo1 [] Hn) as (eff1 & mo2 & evs1 & Hn1).
    pose proof (nstep_evs_nil _ _ _ _ _ (nstep_cfg_sub _ _ _ _ _ Hn1)) as ->.
    destruct (IH eff1 mo2 P (Hk _ _ _ Hn1) HEX) as (r & mo' & Hp & HP).
    exists r, mo'. split; [| exact HP]. exists eff1, mo2, [], []. auto.
Qed.

Theorem srz_impl_cfg : forall {R : Type} (t : itree node R) Q P ms mo (KL : R -> Model -> TSet),
  impl segs (at_node segs) t Q ms -> twf_cfg t mo P -> mstd' mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> mstd' mo' -> srealizes segs (mkCfg ms' mo') (KL r mo')) ->
  srealizes segs (mkCfg ms mo) (tset t mo KL).
Proof.
  intros R t. induction t as [r | n k IH]; intros Q P ms mo KL Himpl Htwf Hstd HL.
  - cbn in Himpl, Htwf |- *. pose proof Hstd as (Hh & Hl & Hm).
    eapply srz_evt; [exact Hh | exact Hl | exact Himpl |].
    intros ms' HQ. apply (HL r ms' mo HQ Htwf). exact Hstd.
  - cbn in Himpl, Htwf. cbn [tset]. destruct Htwf as [Hsafe Hk]. pose proof Hstd as (Hh & Hl & Hm).
    eapply srz_evt; [exact Hh | exact Hl | exact Himpl |].
    intros ms1 [Hat Himpl1].
    destruct (node_char_of n ms1 mo Hat Hsafe Hstd) as (x8 & Hsvc & Hchar & Hex).
    apply (srz_svc_fam n ms1 mo x8 (fun eff mo' => tset (k eff) mo' KL) Hat Hh Hl Hsvc Hchar Hex).
    + intros eff mo' Hn. pose proof (nstep_mstd' n mo eff mo' Hstd Hn) as (A & B & C & D). auto.
    + intros eff mo' Hn.
      apply (IH eff Q P); [apply Himpl1 | apply (Hk eff mo' []); exact Hn
                          | exact (nstep_mstd' n mo eff mo' Hstd (nstep_cfg_sub _ _ _ _ _ Hn)) | exact HL].
Qed.

Lemma tset_elim : forall {R : Type} (t : itree node R) mo KL tr,
  tset t mo KL tr -> tr = [] \/ exists r mo', tpath nstep_cfg t mo [] r mo' /\ KL r mo' tr.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo KL tr H; cbn in H.
  - right. exists r, mo. split; [cbn; auto | exact H].
  - destruct H as [-> | (eff & mo' & Hn & Ht)]; [left; reflexivity|].
    destruct (IH eff mo' KL tr Ht) as [-> | (r & mo2 & Hp & HK)]; [left; reflexivity|].
    right. exists r, mo2. split; [|exact HK]. cbn. exists eff, mo', [], []. auto.
Qed.

Lemma tset_intro : forall {R : Type} (t : itree node R) mo KL tr r mo',
  tpath nstep_cfg t mo [] r mo' -> KL r mo' tr -> tset t mo KL tr.
Proof.
  intros R t; induction t as [r0 | n k IH]; intros mo KL tr r mo' Hp HK; cbn in Hp |- *.
  - destruct Hp as (-> & -> & _). exact HK.
  - destruct Hp as (eff & mo1 & evs & tr' & Hn & Hp & He).
    pose proof (nstep_evs_nil _ _ _ _ _ (nstep_cfg_sub _ _ _ _ _ Hn)) as ->. destruct tr'; [|discriminate He].
    right. exists eff, mo1. split; [exact Hn|]. eapply IH; [exact Hp | exact HK].
Qed.

Lemma tset_nil_reach : forall {R : Type} (t : itree node R) mo KL,
  (forall r mo', tpath nstep_cfg t mo [] r mo' -> KL r mo' []) -> tset t mo KL [].
Proof.
  intros R t mo KL H. destruct t as [r | n k]; cbn.
  - apply H. cbn. auto.
  - left. reflexivity.
Qed.

Lemma tset_eq_gen : forall {R : Type} (t : itree node R) mo KL (K : TSet),
  (forall r mo' tr, tpath nstep_cfg t mo [] r mo' -> KL r mo' tr -> K tr) ->
  (forall tr, K tr -> tr = [] \/ exists r mo', tpath nstep_cfg t mo [] r mo' /\ KL r mo' tr) ->
  K [] -> (forall r mo', tpath nstep_cfg t mo [] r mo' -> KL r mo' []) ->
  t_eq (tset t mo KL) K.
Proof.
  intros R t mo KL K Hsub Hcov Knil KLnil tr. split.
  - intros Ht. destruct (tset_elim t mo KL tr Ht) as [-> | (r & mo' & Hp & HK)]; [exact Knil|]. exact (Hsub r mo' tr Hp HK).
  - intros HK. destruct (Hcov tr HK) as [-> | (r & mo' & Hp & HKL)].
    + apply tset_nil_reach. exact KLnil.
    + eapply tset_intro; [exact Hp | exact HKL].
Qed.

Lemma tset_eq_const : forall {R : Type} (t : itree node R) mo KL (K : TSet),
  (forall r mo', tpath nstep_cfg t mo [] r mo' -> t_eq (KL r mo') K) ->
  (exists r mo', tpath nstep_cfg t mo [] r mo') ->
  K [] ->
  t_eq (tset t mo KL) K.
Proof.
  intros R t mo KL K HK (r0 & mo0 & Hp0) Knil.
  apply tset_eq_gen; [| | exact Knil |].
  - intros r mo' tr Hp H. apply (proj1 (HK r mo' Hp tr)). exact H.
  - intros tr H. right. exists r0, mo0. split; [exact Hp0|]. apply (proj2 (HK r0 mo0 Hp0 tr)). exact H.
  - intros r mo' Hp. apply (proj2 (HK r mo' Hp [])). exact Knil.
Qed.

End Bridge.

End AC_1.
