(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import AcctCore ModelX MmXfer NodesA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanCtrlProps SizeHist Gap AsanEmbed AsanProgDeps
  AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree StepB RSim RSimProg EquivZA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Notation atot a := (atotal (aokS a) (apost a)) (only parsing).   (* [comment removed for export] *)
Local Notation STOTA := (STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition live_pairs (st : astate) : list (AsanCtrl.aptr * Z) :=
  map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (a_live st)).

Definition AI (Y : list (AsanCtrl.aptr * Z)) (s : APS) (mo : Model) : Prop :=
  INV (aps_resv s) (aps_atop s) [] [] (aps_m s) mo
  /\ Permutation Y (live_pairs (aps_m s))
  /\ a_qloc_bytes (aps_m s) <= Q_CACHE /\ a_qglob_bytes (aps_m s) <= Q_MAX
  /\ minv (strip mo) /\ m_halted mo = None.

Lemma AI_perm : forall Y Y' s mo, Permutation Y Y' -> AI Y s mo -> AI Y' s mo.
Proof. intros Y Y' s mo HP (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3]. eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H2]. Qed.

Lemma AI_so : forall Y s mo v, AI Y s mo -> AI Y (aset_so v s) mo.
Proof. intros Y [m so rv atp cl] mo v H. exact H. Qed.

(* [comment removed for export] *)
Lemma AI_cl : forall Y s mo v, AI Y s mo -> AI Y (aset_cl v s) mo.
Proof. intros Y [m so rv atp cl] mo v H. exact H. Qed.

Lemma AI_model : forall Y s mo, AI Y s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y s mo (HI & _ & _ & _ & Hmi & Hh). split; [|exact Hh]. split; [exact Hmi|]. destruct HI as [_ (M1 & _)]. exact M1. Qed.

Lemma AI_fds : forall Y s mo f, AI Y s mo -> minvA (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y s (with_fds f mo).
Proof.
  intros Y s mo f (HI & HP & Hq1 & Hq2 & Hmi & Hh) [Hmi' _] Hh'. unfold AI.
  split; [| repeat (split; [assumption|]); assumption].
  destruct HI as [HA HM]. split; [exact HA|]. apply AMI_with_fds. exact HM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FR (mo mo' : Model) : Prop :=
  (minv (strip mo) -> minv (strip mo')) /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo.

Lemma FR_refl : forall mo, FR mo mo. Proof. intros. unfold FR. split; [intros H; exact H|]. split; [reflexivity|]. split; reflexivity. Qed.
Lemma FR_trans : forall m1 m2 m3, FR m1 m2 -> FR m2 m3 -> FR m1 m3.
Proof. intros m1 m2 m3 (A1&A2&A3&A4) (B1&B2&B3&B4). unfold FR. split; [intros H; apply B1, A1, H|]. split; [congruence|]. split; congruence. Qed.

(* [comment removed for export] *)
Lemma FR_with_vmmaps_strip : forall mo mo' h, strip mo' = with_vmmaps h (strip mo) ->
  vm_init_sp h = vm_init_sp (m_vmmaps mo) ->
  m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> m_halted mo' = m_halted mo -> FR mo mo'.
Proof.
  intros mo mo' h Hs Hsp Hf Hfs Hh. unfold FR. split; [| split; [exact Hf| split; [exact Hfs| exact Hh]]].
  intros Hmi. rewrite Hs. eapply minv_vm_only; [apply vm_only_with_vmmaps; exact Hsp| exact Hmi].
Qed.

Lemma apost_FR : forall atop e mo z mo', apost atop e mo z mo' -> FR mo mo'.
Proof.
  intros atop e mo z mo' H. destruct e as [t|b|addr len prot flags|addr len|a l p|addr len|w]; cbn [AsanNodeSem.apost] in H; try contradiction.
  - destruct (addr =? 0).
    + destruct H as (_ & _ & _ & _ & ->). unfold grant_model. eapply FR_with_vmmaps_strip; try reflexivity.
    + destruct H as (_ & ->). unfold fixed_model. eapply (FR_with_vmmaps_strip _ _ (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)))).
      * rewrite strip_with_mmap_replacement. apply strip_with_vmmaps.
      * reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
  - destruct H as (_ & ->). unfold munmap_model. eapply FR_with_vmmaps_strip; try reflexivity.
  - (* [comment removed for export] *) destruct H as (_ & ->). apply FR_refl.
Qed.

Lemma atotal_FR : forall atop {R} (t : AM R) mo (Post : R -> Model -> Prop),
  atot atop t mo Post -> atot atop t mo (fun r mo' => Post r mo' /\ FR mo mo').
Proof.
  intros atop R t. induction t as [r|e k IH]; intros mo Post H; cbn in *.
  - split; [exact H| apply FR_refl].
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp.
    eapply atotal_mono; [| apply IH; exact (Hk _ _ Hp)]. cbv beta. intros r mo'' [HP HF]. split; [exact HP|].
    eapply FR_trans; [apply (apost_FR _ _ _ _ _ Hp)| exact HF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PhiA : node -> Model -> Prop := PhiB.

Lemma tglob_mbind_l : forall {X Y} (m : Monad.M APS X) (f : X -> Monad.M APS Y) s mo,
  tglob nstepA PhiA (mbind m f s) mo -> tglob nstepA PhiA (m s) mo.
Proof. intros X Y m f s mo H. unfold mbind in H. exact (tglob_ebind_l nstepA PhiA _ _ _ H). Qed.

Lemma tglob_getk : forall {X} (k : APS -> Monad.M APS X) s mo,
  tglob nstepA PhiA (mbind mget k s) mo -> tglob nstepA PhiA (k s s) mo.
Proof. intros X k s mo H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sizes_live_pairs : forall st, map snd (live_pairs st) = sizes (live_chunks st).
Proof. intros. unfold live_pairs, sizes, live_chunks. rewrite !map_map. reflexivity. Qed.

Lemma HISTOK_perm : forall M M', Permutation M M' -> HISTOK M -> HISTOK M'.
Proof.
  intros M M' HP (I & Zl & H1 & H2 & H3 & H4 & H5). exists I, Zl. split; [|auto].
  eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H1].
Qed.

Theorem asan_ok_malloc : forall Y n s mo,
  AI Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  tglob nstepA PhiA (amalloc_M n s) mo ->        (* [comment removed for export] *)
  STOTA (amalloc_M n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ aps_so s' = aps_so s /\ aps_cl s' = aps_cl s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y n [st so RESV ATOP CL] mo HAI Hn HH HG. pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_atop aps_resv] in *.
  unfold amalloc_M in HG. pose proof (tglob_getk _ _ _ HG) as HG0. cbv beta in HG0. pose proof (tglob_mbind_l _ _ _ _ HG0) as HG1.   (* [comment removed for export] *)
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  unfold amalloc_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan_glob ATOP); [split; assumption| reflexivity| | exact HG1]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)).
    intros mb ms.
    (* [comment removed for export] *)
    set (dummy := mkch n 70368744177664 (sec_map_size n)).
    assert (Hwf : chunk_wf ATOP dummy).
    { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
      - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
      - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(unfold REQMAX in Hn; lia)).
        unfold KHIGH. unfold REQMAX in Hn. repeat split; try lia. }
    apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
    apply (live_budget_of_HISTOK (ATOP:=ATOP)).
    + constructor; [exact Hwf|]. destruct HI as [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
      apply Forall_app in HW as [HWl _]. exact HWl.
    + unfold sizes. cbn [map]. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
      fold (sizes (live_chunks st)). rewrite <- sizes_live_pairs. eapply HISTOK_perm; [|exact HH]. apply perm_skip. apply Permutation_map. exact HPY. }
  cbv beta. intros [st' op] s2 mo2 (-> & (ch & Hop & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & Eq3 & Eq4) & HFR). cbn [fst snd] in *.
  eapply STOT_bind; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  eapply STOT_mono; [apply STOT_ret|]. cbv beta. intros r s4 mo4 (-> & -> & ->).
  exists (a_next st). subst op. split; [reflexivity|]. destruct HFR as (F1 & F2 & F3 & F4).
  split; [| split; [unfold REQMAX in Hn; lia| repeat split; auto]].
  unfold AI. cbn [aps_m aset_m aps_so aps_atop aps_resv]. split; [exact HI2|]. split.
  - unfold live_pairs. rewrite Hlive.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
    cbn [map fst snd]. rewrite Hsz. apply perm_skip. exact HPY.
  - rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_pairs_In : forall st p cap, In (p, cap) (live_pairs st) -> exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = cap.
Proof.
  intros st p cap H. unfold live_pairs in H. apply in_map_iff in H as ([k ch] & E & Hin). cbn in E. injection E as -> <-.
  exists ch. split; [|reflexivity]. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin.
Qed.

Theorem aannotate_core : forall RESV ATOP st mo p cap old new ch,
  INV RESV ATOP [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = cap ->
  0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  atot ATOP (aannotate st p cap old new) mo (fun st' mo' => st' = st /\ INV RESV ATOP [] [] st mo').
Proof.
  intros RESV ATOP st mo p cap old new ch HI Hq1 Hq2 Hl Hsz Hold Hnew Hmin.
  pose proof HI as [HA HM]. pose proof HA as (_ & HW & _).
  assert (Hwf : chunk_wf ATOP ch).
  { unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HWl _]. unfold live_chunks in HWl.
    rewrite Forall_forall in HWl. apply HWl. apply in_map_iff. exists (p, ch). split; [reflexivity|].
    apply list_elem_of_In. apply elem_of_map_to_list. exact Hl. }
  assert (Hcap : 0 <= cap <= 2^30) by (subst cap; destruct ch; cbn in Hwf |- *; lia).
  unfold aannotate. rewrite Hl.
  replace (negb ((0 <=? old) && (old <=? cap) && (0 <=? new) && (new <=? cap))) with false.
  2:{ symmetry. rewrite (proj2 (Z.leb_le 0 old)), (proj2 (Z.leb_le old cap)), (proj2 (Z.leb_le 0 new)), (proj2 (Z.leb_le new cap)) by lia. reflexivity. }
  destruct (Z.ltb_spec (2^40) cap); [lia|].
  destruct (Z.eqb_spec old new) as [|Hne]; [apply atotal_ret; auto|].
  assert (Hrdn : 0 <= rdn cap 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  replace (rdn cap 8 <? Z.min old new) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
  destruct (Z.ltb_spec old new) as [Hlt|]; [|apply atotal_ret; auto].
  destruct ch as [c n|mb ms n]; [apply atotal_ret; auto|]. cbv zeta. cbn [chunk_user_beg].
  pose proof (rdn_le old 8 ltac:(lia)) as R1. pose proof (rdn_le new 8 ltac:(lia)) as R2.
  assert (R0 : 0 <= rdn old 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  destruct (Z.ltb_spec (rdn old 8) (rdn new 8)) as [Hab|]; [|apply atotal_ret; auto].
  cbn in Hwf. destruct Hwf as (Hn & -> & Hal & Hmb & Hrange). cbn in Hsz. subst cap.
  pose proof (sec_map_size_ge n ltac:(lia)) as SG.
  assert (Hrz : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hrz. unfold PG.
  destruct (CH_bounds [] [] st HA) as [_ HCS].
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  { unfold zlen; cbn; lia. } { cbn; lia. }
  apply (@poison0_ok RESV ATOP _ _ [] [] st _ mo); auto; try lia.
  all: try (destruct Hrange as [Hlo|[Hh1 Hh2]]; [left; lia| right; lia]).
  intros mo' HI'. apply atotal_ret. auto.
Qed.

Theorem asan_ok_annot : forall Y q cap old new s mo,
  AI Y s mo -> In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
  tglob nstepA PhiA (aannot_M q cap old new s) mo ->        (* [comment removed for export] *)
  STOTA (aannot_M q cap old new s) mo
        (fun _ s' mo' => AI Y s' mo' /\ aps_so s' = aps_so s /\ aps_cl s' = aps_cl s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y q cap old new [st so RESV ATOP CL] mo HAI Hin Hold Hnew Hmin HG. pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_atop aps_resv] in *.
  unfold aannot_M in HG. pose proof (tglob_getk _ _ _ HG) as HG0. cbv beta in HG0. pose proof (tglob_mbind_l _ _ _ _ HG0) as HG1.   (* [comment removed for export] *)
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold aannot_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan_glob ATOP); [split; assumption| reflexivity| | exact HG1]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. eapply aannotate_core; eauto. }
  cbv beta. intros st' s2 mo2 (-> & [-> HI2] & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| repeat split; auto].
  unfold AI. cbn [aps_m aset_m aps_atop aps_resv]. split; [exact HI2|]. split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem asan_ok_free : forall Y q n s mo,
  AI ((q, n) :: Y) s mo ->
  tglob nstepA PhiA (afree_M q s) mo ->        (* [comment removed for export] *)
  STOTA (afree_M q s) mo
        (fun _ s' mo' => AI Y s' mo' /\ aps_so s' = aps_so s /\ aps_cl s' = aps_cl s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros Y q n [st so RESV ATOP CL] mo HAI HG. pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_atop aps_resv] in *.
  unfold afree_M in HG. pose proof (tglob_getk _ _ _ HG) as HG0. cbv beta in HG0. pose proof (tglob_mbind_l _ _ _ _ HG0) as HG1.   (* [comment removed for export] *)
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold afree_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan_glob ATOP); [split; assumption| reflexivity| | exact HG1]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. eapply afree_core; eauto. }
  cbv beta. intros st' s2 mo2 (-> & (HI2 & Hlive & Hnext & Hq1' & Hq2') & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| repeat split; auto].
  unfold AI. cbn [aps_m aset_m aps_atop aps_resv]. split; [exact HI2|]. split.
  - unfold live_pairs. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
    eapply Permutation_trans; [exact HPY|]. unfold live_pairs. rewrite <- Hsz.
    change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
      with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
    apply Permutation_map. apply Permutation_sym. apply map_to_list_delete. exact Hl.
  - split; [exact Hq1'|]. split; [exact Hq2'|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mat_with_fds : forall x m, m_vm_materialized (with_fds x m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma halted_with_fds : forall x m, m_halted (with_fds x m) = m_halted m. Proof. reflexivity. Qed.
Lemma mat_with_tid : forall x m, m_vm_materialized (with_tid x m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma halted_with_tid : forall x m, m_halted (with_tid x m) = m_halted m. Proof. reflexivity. Qed.

Lemma nstep_close_strip : forall fd m eff mo' evs,
  nstep (NClose fd) m eff mo' evs -> nstep (NClose fd) (strip m) eff (strip mo') evs /\ (mo' = m \/ exists x, mo' = with_fds x m).
Proof.
  intros fd m eff mo' evs Hn. cbn [nstep] in Hn |- *. rewrite m_fds_strip. destruct Hn as (He & Hr & H).
  destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)).
  - destruct H as [Heff ->]. rewrite strip_with_fds. split; [| right; eexists; reflexivity]. auto.
  - destruct H as [Heff ->]. split; [| left; reflexivity]. auto.
Qed.

Theorem asan_ok_MI2 : forall n mo rsp mo' evs,
  nstep n mo rsp mo' evs -> io_node n -> minvA mo -> m_halted mo = None -> minvA mo' /\ m_halted mo' = None.
Proof.
  intros n mo rsp mo' evs Hst Hio [Hmi Hmat] Hh.
  assert (Hsh : m_halted (strip mo) = None) by (rewrite m_halted_strip; exact Hh).
  destruct n as [fd bs|fd bufs|path|fd buf count|fd|fd req| |code|req|a l p f|a l|a l p|a l]; cbn [io_node] in Hio; try contradiction.
  - destruct Hst as (k & _ & _ & -> & _). split; [split|]; assumption.
  - destruct Hst as [-> _]. split; [split|]; assumption.
  - pose proof (minv_preserved _ _ _ _ _ Hmi Hsh (nstep_open_strip _ _ _ _ _ Hst)) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct (nstep_open_shape _ _ _ _ _ Hst) as [-> | (x & ->)]; [exact Hmat| rewrite mat_with_fds; exact Hmat].
  - pose proof (minv_preserved _ _ _ _ _ Hmi Hsh (nstep_read_strip _ _ _ _ _ _ _ Hst)) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct (nstep_read_shape _ _ _ _ _ _ _ Hst) as [(E & _) | (x & ->)]; [rewrite E; exact Hmat| rewrite mat_with_fds; exact Hmat].
  - destruct (nstep_close_strip _ _ _ _ _ Hst) as [Hs Hsh2].
    pose proof (minv_preserved _ _ _ _ _ Hmi Hsh Hs) as [Hh' Hmi']. rewrite m_halted_strip in Hh'.
    split; [split; [exact Hmi'|]| exact Hh'].
    destruct Hsh2 as [-> | (x & ->)]; [exact Hmat| rewrite mat_with_fds; exact Hmat].
  - destruct Hst as (_ & _ & ->). split; [split|]; assumption.
  - destruct Hst as (_ & t & _ & H). destruct (m_tid mo); destruct H as [_ ->]; [split; [split|]; assumption|].
    split; [split; [rewrite strip_with_tid; exact Hmi| rewrite mat_with_tid; exact Hmat]| rewrite halted_with_tid; exact Hh].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma nstepA_sub : forall n mo r mo' e, ~ nf_node n -> nstepA n mo r mo' e -> nstep n mo r mo' e.
Proof. intros n mo r mo' e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstepA n mo r mo e.
Proof. intros n mo r e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_io : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstepA n mo r mo' e.
Proof. intros n mo r mo' e Hio H; destruct n; cbn [io_node] in Hio; try contradiction; exact H. Qed.

Definition AAllocAsanOK : AAllocOK AAllocAsan nstepA PhiA minvA :=
  mkAAllocOK AAllocAsan nstepA PhiA minvA nstepA_sub nstepA_same nstepA_io asan_ok_MI2
    aps_get_set aps_set_set aps_set_get aps_addr_so
    aps_cl_get_set aps_cl_so aps_so_cl
    AI AI_perm AI_so AI_cl AI_model AI_fds
    asan_ok_malloc asan_ok_free asan_ok_annot.   (* [comment removed for export] *)
