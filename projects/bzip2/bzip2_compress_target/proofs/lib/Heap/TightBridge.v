(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec MmapSim RefNodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep MmFacts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require KStepC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require KStepC MI_Inv MI_Kit MI_Ledger MI_Contracts MTight.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prelim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MSafe OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStep OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MmFacts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC.KLink OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KStepC OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ledger OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MTight.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require CfgStep AllocRefusal.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma twf_strengthen {R} : forall (t : itree node R) mo (P : R -> Model -> Prop) (Q : R -> Model -> Prop),
  twf t mo P -> (forall tr r mo', tpath nstep t mo tr r mo' -> Q r mo') -> twf t mo (fun r mo' => P r mo' /\ Q r mo').
Proof.
  intros t. induction t as [r|n k IH]; intros mo P Q HT HQ; cbn in *.
  - split; [exact HT|]. apply (HQ []). repeat split; reflexivity.
  - destruct HT as [HS HK]. split; [exact HS|]. intros rsp mo' evs Hst. apply IH; [apply (HK rsp mo' evs); exact Hst|].
    intros tr r mo'' Hp. apply (HQ (evs ++ tr)). exists rsp, mo', evs, tr. auto.
Qed.

Lemma mspec_strengthen {St A} (P : St -> Model -> Prop) (m : Monad.M St A) (Q : A -> St -> Model -> Prop) (R : St -> Model -> A -> St -> Model -> Prop) :
  mspec P m Q ->
  (forall s mo tr a s' mo', P s mo -> tpath nstep (m s) mo tr (Ok (a, s')) mo' -> R s mo a s' mo') ->
  forall s mo, P s mo -> mspec (fun s1 mo1 => s1 = s /\ mo1 = mo) m (fun a s' mo' => Q a s' mo' /\ R s mo a s' mo').
Proof.
  intros HM HR s mo HP s1 mo1 [-> ->]. unfold etwf.
  pose proof (twf_strengthen (m s) mo (fun r mo1 => match r with Unr => False | Ok p => Q (fst p) (snd p) mo1 end)
                (fun r mo' => match r with Ok p => R s mo (fst p) (snd p) mo' | Unr => True end) (HM s mo HP)) as W.
  eapply twf_mono.
  - apply W. intros tr [|[a s']] mo' Hp; [exact I|]. cbn. exact (HR s mo tr a s' mo' HP Hp).
  - intros [|[a s']] mo'; cbn; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation MAPF_Z := MAPF.

Lemma mmap_len_eq len : mmap_len len = page_round_up_Z len.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_grant_of_not_refusable : forall n mo,
  AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF_Z) mo n = false ->
  exists a, grant_ok (Z_to_bv 64 0) mo a n = true.
Proof.
  intros n mo Hnf. unfold AllocRefusal.mmap_grant_refusable in Hnf. apply orb_false_iff in Hnf as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  apply AllocRefusal.vm_gap_available_iff in Hg as (a & H1 & H2 & H3 & H4).
  exists a. unfold grant_ok.
  rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4. cbn [andb].
  unfold mmap_noreserve_backed_ok in Hb.
  replace (mmap_noreserve_b (Z_to_bv 64 MAPF_Z)) with false in Hb by (vm_compute; reflexivity).
  exact Hb.
Qed.

Lemma nstep_mmap_grant : forall len mo a, 0 < len < 2^62 ->
  grant_ok (Z_to_bv 64 0) mo a (mmap_len len) = true ->
  nstep (NMmap 0 len PROT_RW MAPF_Z) mo (mkEffect a [] [(a, Z_to_bv 64 (mmap_len len))])
        (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                                   (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))
                                   (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo) [].
Proof.
  intros len mo a Hlen HG.
  assert (Hne : errno_ret_in mmap_errnos a = false)
    by exact (grant_not_errno (Z_to_bv 64 0) mo a (mmap_len len) ltac:(pose proof (mmap_len_ge len ltac:(lia)); lia) HG).
  apply nstep_mmap_iff. split.
  2:{ apply spurious_refusal_not_refusal. cbn [eff_ret].
      rewrite CfgStep.refusal_b_mmap by reflexivity. exact Hne. }
  unfold check_mmap.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 MAPF_Z)) with true by (vm_compute; reflexivity). cbn [negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF_Z) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  cbv iota beta.
  rewrite unsigned_lit by lia. rewrite <- mmap_len_eq.
  rewrite Hne.
  unfold grant_ok in HG. apply andb_prop in HG as [HG H5]. apply andb_prop in HG as [HG H4].
  apply andb_prop in HG as [HG H3]. apply andb_prop in HG as [H1 H2].
  rewrite H1, H2, H3, H4. unfold mmap_noreserve_backed_ok.
  replace (mmap_noreserve_b (Z_to_bv 64 MAPF_Z)) with false by (vm_compute; reflexivity).
  rewrite H5. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb].
  unfold with_mmap_backing. replace (mmap_noreserve_b (Z_to_bv 64 MAPF_Z)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_err_forced : forall len mo rsp mo' evs e, 0 < len < 2^62 ->
  nstep (NMmap 0 len PROT_RW MAPF_Z) mo rsp mo' evs -> dec_mmap len [] rsp = Some (MmErr e) ->
  AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF_Z) mo (mmap_len len) = true.
Proof.
  intros len mo rsp mo' evs e Hlen H DX.
  destruct (AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF_Z) mo (mmap_len len)) eqn:Hrf; [reflexivity| exfalso].
  pose proof H as Hst.
  apply nstep_mmap_iff in H. destruct H as [H _]. unfold check_mmap in H.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 MAPF_Z)) with true in H by (vm_compute; reflexivity). cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF_Z) (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  cbv iota beta in H. rewrite unsigned_lit in H by lia. rewrite <- mmap_len_eq in H.
  destruct rsp as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr.
  - destruct (mmap_grant_of_not_refusable (mmap_len len) mo Hrf) as [a GA].
    pose proof (nstep_mmap_grant len mo a Hlen GA) as Hg. apply nstep_mmap_iff in Hg as [Hgc _].
    apply (nstep_mmap_refusal_absurd _ _ _ _ _ _ _ _ _ _ Hst Herr Hgc).
    exact (grant_not_errno (Z_to_bv 64 0) mo a (mmap_len len) ltac:(pose proof (mmap_len_ge len ltac:(lia)); lia) GA).
  - cbv iota zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E E7]. apply listNN_eqb_eq in E7. subst zs.
    revert DX. cbn -[mmap_addr_ok mmap_len bv_eqb bv_unsigned Z_to_bv page_round_up_Z]. rewrite !bv_eqb_refl. cbn [andb].
    destruct (mmap_addr_ok len [] (bv_unsigned r)); discriminate.
Qed.

(* [comment removed for export] *)
Lemma mmap_not_forced_of_grant : forall n mo a,
  grant_ok (Z_to_bv 64 0) mo a n = true -> AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF_Z) mo n = false.
Proof.
  intros n mo a GA. unfold grant_ok in GA.
  apply andb_prop in GA as [GA H5]. apply andb_prop in GA as [GA H4].
  apply andb_prop in GA as [GA H3]. apply andb_prop in GA as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  unfold AllocRefusal.mmap_grant_refusable.
  rewrite (proj2 (AllocRefusal.vm_gap_available_iff _ _) (ex_intro _ a (conj H1 (conj H2 (conj H3 H4))))).
  unfold mmap_noreserve_backed_ok.
  replace (mmap_noreserve_b (Z_to_bv 64 MAPF_Z)) with false by (vm_compute; reflexivity).
  rewrite H5. reflexivity.
Qed.

Lemma mmap_not_forced_big : forall len mo, 0 < len -> mmap_len len <= 2^35 ->
  atop_ok (m_vmmaps mo) ->
  Forall (fun p => bv_unsigned (snd p) <= 2^35) (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= 1000 ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF_Z) mo (mmap_len len) = false.
Proof.
  intros len mo Hlen Hml Hat SZ CNT BUD.
  pose proof (mmap_len_ge len Hlen) as ML.
  destruct (grant_exists_big (Z_to_bv 64 0) mo (mmap_len len) Hat ltac:(lia) SZ CNT BUD) as [a GA].
  exact (mmap_not_forced_of_grant _ _ _ GA).
Qed.


Lemma m_vm_materialized_with_vmmaps h m : m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. destruct m as [fd [maps lazy mat] io fs pr li ti]. reflexivity. Qed.

Lemma m_vm_materialized_forget lo hi m : m_vm_materialized m = [] -> m_vm_materialized (vm_forget_range lo hi m) = [].
Proof. destruct m as [fd [maps lazy mat] io fs pr li ti]. cbn. intros ->. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_ok_exact : forall len mo rsp mo' evs a, 0 < len < 2^62 ->
  nstep (NMmap 0 len PROT_RW MAPF_Z) mo rsp mo' evs -> dec_mmap len [] rsp = Some (MmOk a) ->
  mo' = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                                   (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))
                                   (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.
Proof.
  intros len mo rsp mo' evs a Hlen H DX. apply nstep_mmap_iff in H. destruct H as [H _]. unfold check_mmap in H.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 MAPF_Z)) with true in H by (vm_compute; reflexivity). cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  replace (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF_Z) (Z_to_bv 64 0)) with true in H by (vm_compute; reflexivity).
  cbv iota beta in H. destruct rsp as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  match type of H with context [errno_ret_in ?l r] => destruct (errno_ret_in l r) eqn:Herr end.
  - destruct zs; [|discriminate]. exfalso. apply errno_ret_in_true in Herr as (e & HIn & ->).
    cbn in HIn. destruct HIn as [<-|[]]. cbn -[errno_of errno_ret] in DX. rewrite errno_of_errno_ret in DX by (unfold ENOMEM; lia). discriminate.
  - cbv zeta in H. match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    injection H as <-. apply andb_prop in E as [E E7]. apply listNN_eqb_eq in E7. subst zs.
    cbn -[mmap_addr_ok mmap_len bv_eqb bv_unsigned Z_to_bv page_round_up_Z] in DX. rewrite bv_eqb_refl in DX. cbn [andb] in DX.
    rewrite unsigned_lit in DX by lia. fold (mmap_len len) in DX. rewrite bv_eqb_refl in DX. cbn [andb] in DX.
    destruct (mmap_addr_ok len [] (bv_unsigned r)); [|discriminate]. injection DX as <-. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit by lia. fold (mmap_len len).
    unfold with_mmap_backing. replace (mmap_noreserve_b (Z_to_bv 64 MAPF_Z)) with false by (vm_compute; reflexivity). reflexivity.
Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac tp_bind H :=
  let EU := fresh "EU" in
  apply -> tpath_ebind in H; destruct H as [[_ EU]|H]; [discriminate EU|].
Section ACeilS2. Context {ACEIL__ : ACeil}.


Lemma tpath_ret_inv {R} (r0 r : R) mo tr mo' : tpath nstep (Ret r0) mo tr r mo' -> r0 = r /\ mo' = mo /\ tr = [].
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma neg_errno_ENOMEM_facts : forall LR len,
  mmap_answer_ok LR len (neg_errno ENOMEM) = true /\ is_err (neg_errno ENOMEM) = true.
Proof. intros. split; [unfold mmap_answer_ok; apply orb_true_intro; left|]; vm_compute; reflexivity. Qed.

Section PATHS.
Variables (X : list bptr) (G : PState -> Model -> Prop) (s : PState) (MD : Model) (n : Z).
Variables (QF : Malloc.M (mstate * option cptr) -> Prop) (QS : Z -> Malloc.M (mstate * option cptr) -> Prop).
Variables (PF : mstate * option cptr -> Prop) (PS : Z -> mstate * option cptr -> Prop).
Hypothesis HO : OWNX X G s MD.
Hypothesis Hn : 0 <= n.
Hypothesis MM : MMAP1 (live_ranges (ps_m s)) (cmalloc (ps_m s) n) QF QS.
Hypothesis HF : forall t, QF t -> exists x, t = SRet x /\ PF x.
Hypothesis HS : forall z t, QS z t -> exists x, t = SRet x /\ PS z x.

(* [comment removed for export] *)
Lemma raw_malloc_paths04 : forall tr r s' MD',
  tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' ->
  exists len K z x,
    cmalloc (ps_m s) n = SVis (EMmap 0 len PROT_RW MAPF) K /\ 0 < len <= 2^30 /\ tr = []
    /\ s' = set_m (fst x) s
    /\ r = match snd x with Some c => Some (c, fresh_off (fst x) c n) | None => None end
    /\ ( (is_err z = true /\ PF x /\ MD' = MD /\ AllocRefusal.mmap_grant_refusable (Z_to_bv 64 MAPF) MD (mmap_len len) = true)
       \/ (is_err z = false /\ PS z x /\ vm_only MD MD' /\ m_vm_lazy MD' = [] /\ m_halted MD' = None
           /\ let h := m_vmmaps MD in
              m_vmmaps MD' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                          (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
           /\ mmap_addr_ok len [] z = true /\ m_vm_materialized MD' = m_vm_materialized MD
           /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true) ).
Proof.
  intros tr r s' MD' Hp.
  cps_destruct MM as (len & K & E & Hlen & KF & KS).
  destruct HO as [(L & SR & HK & Hincl) [Hnd HG]].
  (* [comment removed for export] *)
  pose proof (cmalloc_contract_sim (ps_m s) L n SR Hn) as CT. rewrite E in CT. cbn [ctree_ok] in CT. destruct CT as [PRE _].
  cbn [event_pre] in PRE.
  assert (QUIET : brk_quiet L /\ 0 < len < LEN_MAX).
  { destruct PRE as [(Q & _ & _ & _ & B)|(cur & _ & _ & _ & _ & AB)]; [auto|]. exfalso. unfold MAPF, MAPFX in AB. cbv in AB. lia. }
  destruct QUIET as [QUIET LENMAX].
  unfold raw_malloc, mbind, mget in Hp.
  tp_bind Hp. cps_destruct Hp as (tr1 & [s0 s0'] & mo1 & tr2 & H1 & H2 & ->).
  apply tpath_ret_inv in H1 as (E1 & -> & ->). injection E1 as <- <-. cbn [fst snd] in H2.
  tp_bind H2. cps_destruct H2 as (tr3 & [[st' p] s1] & mo2 & tr4 & H3 & H4 & ->).
  rewrite E in H3. cbn [membed] in H3. unfold mbind in H3.
  tp_bind H3. cps_destruct H3 as (tr5 & [z s2] & mo3 & tr6 & H5 & H6 & ->).
  unfold ev_step in H5. cbn -[msys mret mbind Z.to_nat neg_errno] in H5. unfold mbind in H5.
  tp_bind H5. cps_destruct H5 as (tr7 & [a s3] & mo4 & tr8 & H7 & H8 & ->).
  unfold msys in H7. apply tpath_enode in H7 as (rsp & NS & ER).
  cps_pose (nstep_dec_mmap len [] MD rsp mo4 tr7 (kl_atop _ _ _ HK) ltac:(lia) ltac:(pose proof (mmap_len_ge len ltac:(lia)); lia) ltac:(constructor) NS)
    as (-> & VO & LZ & x & DX & CX).
  rewrite DX in ER. injection ER as -> ->.
  apply tpath_ret_inv in H8 as (E8 & -> & ->). injection E8 as E8a E8b. subst z s2.
  cbn [fst snd] in H6, H4.
  assert (KLh : m_halted MD = None /\ m_vm_lazy MD = []) by (split; [exact (kl_halt _ _ _ HK)| exact (kl_lazy _ _ _ HK)]).
  destruct x as [e|a].
  - (* [comment removed for export] *)
    assert (LEN62 : 0 < len < 2^62) by lia.
    pose proof (nstep_mmap_err_forced len MD rsp mo4 _ e LEN62 NS DX) as FORCED. clear LEN62.
    destruct CX as [-> ->].
    destruct (neg_errno_ENOMEM_facts (live_ranges (ps_m s)) len) as [A1 A2].
    cps_destruct (HF _ (KF _ A1 A2)) as ([xst xp] & EK & HPF). rewrite EK in H6. cbn [membed] in H6.
    apply tpath_ret_inv in H6 as (E6 & -> & ->). injection E6 as -> -> <-.
    unfold mupd, mret in H4. tp_bind H4. cps_destruct H4 as (tr9 & [u s4] & mo5 & tr10 & H9 & H10 & ->).
    apply tpath_ret_inv in H9 as (E9 & -> & ->). injection E9 as E9a E9b. subst u s4.
    apply tpath_ret_inv in H10 as (E10 & -> & ->). injection E10 as E10a E10b. subst r s'.
    exists len, K, (neg_errno ENOMEM), (st', p). cbn [fst snd].
    split; [exact E|]. split; [exact Hlen|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    left. auto.
  - (* [comment removed for export] *)
    cps_destruct CX as (AOK & RF & VM4).
    assert (Hh4 : m_halted mo4 = None) by (rewrite (vm_only_halted _ _ VO); exact (proj1 KLh)).
    assert (Hl4 : m_vm_lazy mo4 = []) by (apply LZ; exact (proj2 KLh)).
    cps_pose (KL_mmap_new L (ps_brk s) MD mo4 a len false HK QUIET LENMAX AOK RF Hl4 Hh4 VM4) as (_ & AOK2 & NERR).
    cps_destruct SR as (st & BL & LS & Est & INV & _).
    rewrite (mmap_answer_ok_eq x0 st L (proj1 INV)) in AOK2. rewrite <- Est, live_ranges_strip in KS.
    cps_destruct (HS _ _ (KS _ AOK2 NERR)) as ([xst xp] & EK & HPS). rewrite EK in H6. cbn [membed] in H6.
    apply tpath_ret_inv in H6 as (E6 & -> & ->). injection E6 as -> -> <-.
    unfold mupd, mret in H4. tp_bind H4. cps_destruct H4 as (tr9 & [u s4] & mo5 & tr10 & H9 & H10 & ->).
    apply tpath_ret_inv in H9 as (E9 & -> & ->). injection E9 as E9a E9b. subst u s4.
    apply tpath_ret_inv in H10 as (E10 & -> & ->). injection E10 as E10a E10b. subst r s'.
    exists len, K, a, (st', p). cbn [fst snd].
    split; [exact E|]. split; [exact Hlen|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    right. split; [exact NERR|]. split; [exact HPS|]. split; [exact VO|]. split; [exact Hl4|]. split; [exact Hh4|]. split; [exact VM4|]. split; [exact AOK|].
    split; [| exact RF].
    rewrite (nstep_mmap_ok_exact len MD rsp mo4 [] a ltac:(lia) NS DX). apply m_vm_materialized_with_vmmaps.
Qed.

Lemma raw_malloc_paths : forall tr r s' MD',
  tpath nstep (raw_malloc n s) MD tr (Ok (r, s')) MD' ->
  exists len K z x,
    cmalloc (ps_m s) n = SVis (EMmap 0 len PROT_RW MAPF) K /\ 0 < len <= 2^30 /\ tr = []
    /\ s' = set_m (fst x) s
    /\ r = match snd x with Some c => Some (c, fresh_off (fst x) c n) | None => None end
    /\ ( (is_err z = true /\ PF x /\ MD' = MD)
       \/ (is_err z = false /\ PS z x /\ vm_only MD MD' /\ m_vm_lazy MD' = [] /\ m_halted MD' = None
           /\ let h := m_vmmaps MD in
              m_vmmaps MD' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 z, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                          (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
           /\ mmap_addr_ok len [] z = true /\ m_vm_materialized MD' = m_vm_materialized MD
           /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true) ).
Proof.
  intros tr r s' MD' Hp.
  destruct (raw_malloc_paths04 tr r s' MD' Hp) as (len & K & z & x & E & Hlen & Etr & Es & Er & CASES).
  exists len, K, z, x. split; [exact E|]. split; [exact Hlen|]. split; [exact Etr|]. split; [exact Es|]. split; [exact Er|].
  destruct CASES as [(A & B & C & _)|R]; [left; auto| right; exact R].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End PATHS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_munmap_exact : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  0 <= addr -> addr mod 4096 = 0 -> 0 < len -> addr + mmap_len len <= TASK_SIZE ->   (* [comment removed for export] *)
  map_has (vm_maps h) a n = true ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\ m_halted mo' = m_halted mo
  /\ (m_vm_materialized mo = [] -> m_vm_materialized mo' = [])
  /\ dec_munmap addr len rsp = Some (RgDone true)
  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                (maps_subtract (vm_noaccess h) addr (addr + mmap_len len))
                                (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros addr len mo rsp mo' evs h a n Ha0 Hal Hlen Hlen2T HAS H.
  assert (Hlen2 : addr + mmap_len len < 2^64) by (unfold TASK_SIZE in Hlen2T; lia).
  pose proof (mmap_len_ge len Hlen) as Hb.
  apply nstep_munmap_iff in H. destruct H as [H _].
  destruct (check_munmap_shape _ _ _ _ _ _ H) as [(Hv & -> & Hh) HL].
  destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  replace (negb (bv_unsigned a mod page_size =? 0) || w_is0 (Z_to_bv 64 len)) with false in H.
  2:{ symmetry. subst a. rewrite unsigned_lit by lia. unfold page_size. rewrite Hal. cbn. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia. }
  cbv zeta in H. subst a. rewrite unsigned_lit in H by lia.
  replace (TASK_SIZE <? addr + mmap_len len) with false in H by (symmetry; apply Z.ltb_ge; lia).
  rewrite HAS in H.
  assert (Un : bv_unsigned n = mmap_len len) by (subst n; apply unsigned_lit; lia). rewrite Un in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  destruct (w_is0 r && listNN_eqb us [(Z_to_bv 64 addr, n)]) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E1 E3]. apply listNN_eqb_eq in E3. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
  cps_pose (with_mmap_destroyed_only (Z_to_bv 64 addr) n
     (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 addr))
        (maps_subtract (vm_noaccess h) addr (addr + mmap_len len))
        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) as (V1 & V2 & V3 & V4).
  split; [reflexivity|]. split; [exact V1|]. split; [exact V4|]. split; [exact V3|]. split.
  { intros HM. unfold with_mmap_destroyed. apply m_vm_materialized_forget. rewrite m_vm_materialized_with_vmmaps. exact HM. }
  split; [| exact V2].
  unfold dec_munmap. rewrite unsigned_lit by lia. cbn [Z.eqb]. subst n. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREEPATHS.
Variables (X : list bptr) (G : PState -> Model -> Prop) (s : PState) (MD : Model) (p : bptr) (cnt : Z).
Variables (g : aptr) (pb : aptr) (sc ml : Z).
Hypothesis HO : OWNX X G s MD.
Hypothesis HT : TT cnt (ps_m s).
Hypothesis HI : INJ (ps_m s).
Hypothesis Hstrip : strip (ps_m s) = ps_m s.
Hypothesis FP : FREEPRE (ps_m s) (fst p) g pb sc ml.
(* [comment removed for export] *)
Variables (base : Z).
Hypothesis RG : exists k l, s_regions (ps_m s) !! (fst pb) = Some (mkRegion k base l).
Hypothesis PB0 : snd pb = 0.
Hypothesis HAS : map_has (vm_maps (m_vmmaps MD)) (Z_to_bv 64 base) (Z_to_bv 64 (ml * 4096)) = true.
Hypothesis Hbase : 0 < base /\ base mod 4096 = 0 /\ base + ml * 4096 <= alloc_ceiling.   (* [comment removed for export] *)

Lemma raw_free_paths : forall tr r s' MD',
  tpath nstep (raw_free p s) MD tr (Ok (r, s')) MD' ->
  exists cs', tr = [] /\ s' = set_m cs' s
    /\ FREEPOST (ps_m s) (fst p) g pb sc cs' /\ TT cnt cs' /\ INJ cs' /\ strip cs' = cs'
    /\ vm_only MD MD' /\ m_vm_lazy MD' = [] /\ m_halted MD' = None
    /\ (m_vm_materialized MD = [] -> m_vm_materialized MD' = [])
    /\ let h := m_vmmaps MD in
       m_vmmaps MD' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 base))
                        (maps_subtract (vm_noaccess h) base (base + ml * 4096))
                        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros tr r s' MD' Hp.
  cps_destruct (cfree_single_tight cnt (ps_m s) (fst p) g pb sc ml HT HI Hstrip FP) as (K & E & KOK).
  pose proof (fp_ml _ _ _ _ _ _ FP) as ML.
  assert (CB : conc (ps_m s) pb = base).
  { unfold conc, get_region. cps_destruct RG as (k & l & R). rewrite R. cbn [r_base]. rewrite PB0. lia. }
  rewrite CB in E.
  destruct HO as [(L & SR & HK & Hincl) [Hnd HG]].
  assert (KLh : m_halted MD = None /\ m_vm_lazy MD = []) by (split; [exact (kl_halt _ _ _ HK)| exact (kl_lazy _ _ _ HK)]).
  unfold raw_free, mbind, mget in Hp.
  tp_bind Hp. cps_destruct Hp as (tr1 & [s0 s0'] & mo1 & tr2 & H1 & H2 & ->).
  apply tpath_ret_inv in H1 as (E1 & -> & ->). injection E1 as <- <-. cbn [fst snd] in H2.
  tp_bind H2. cps_destruct H2 as (tr3 & [st' s1] & mo2 & tr4 & H3 & H4 & ->).
  rewrite E in H3. cbn [membed] in H3. unfold mbind in H3.
  tp_bind H3. cps_destruct H3 as (tr5 & [z s2] & mo3 & tr6 & H5 & H6 & ->).
  unfold ev_step in H5. unfold mbind in H5.
  tp_bind H5. cps_destruct H5 as (tr7 & [a s3] & mo4 & tr8 & H7 & H8 & ->).
  unfold msys in H7. apply tpath_enode in H7 as (rsp & NS & ER).
  pose proof alloc_ceiling_lt47 as HC47.
  cps_pose (nstep_munmap_exact base (ml * 4096) MD rsp mo4 tr7 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite mmap_len_of_aligned by (try lia; apply Z_mod_mult); unfold TASK_SIZE; lia)
                ltac:(rewrite mmap_len_of_aligned by (try lia; apply Z_mod_mult); exact HAS) NS)
    as (-> & VO & LZ & HH & MAT & DX & VM4).
  rewrite DX in ER. injection ER as -> ->.
  apply tpath_ret_inv in H8 as (E8 & -> & ->). injection E8 as E8a E8b. subst z s2.
  cbn [fst snd] in H6, H4.
  cps_destruct (KOK 0 eq_refl) as (cs' & EK & FQ & HT' & HI' & HS').
  rewrite EK in H6. cbn [membed] in H6.
  apply tpath_ret_inv in H6 as (E6 & -> & ->). injection E6 as E6a E6b. subst st' s1.
  unfold mupd in H4. apply tpath_ret_inv in H4 as (E4 & -> & ->). injection E4 as E4a E4b. subst r s'.
  exists cs'. split; [reflexivity|]. split; [reflexivity|]. split; [exact FQ|]. split; [exact HT'|]. split; [exact HI'|]. split; [exact HS'|].
  split; [exact VO|]. split; [apply LZ; exact (proj2 KLh)|]. split; [rewrite HH; exact (proj1 KLh)|]. split; [exact MAT|].
  rewrite VM4. rewrite mmap_len_of_aligned by (try lia; apply Z_mod_mult). reflexivity.
Qed.
End FREEPATHS.

End ACeilS2.
