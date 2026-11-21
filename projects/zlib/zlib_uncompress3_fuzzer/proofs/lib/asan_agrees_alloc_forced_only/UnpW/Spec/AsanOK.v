(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import AcctCore ModelX MmXfer NodesA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import BackingAlgebra.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.Prelim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.Monad OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.STree OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.Stdio OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanCtrl OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanCtrlProps OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.SizeHist OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.Gap OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanEmbed OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanProgDeps OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanInv OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanBudget OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanTotalCore OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanNodeSem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanTotal OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanFree OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.StepB OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.RSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.RSimProg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Spec.EquivPA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanVol.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation atot a := (atotal (aok a) (apost a)) (only parsing).
Local Notation STOTA := (STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit)).


Definition live_pairs (st : astate) : list (AsanCtrl.aptr * Z) :=
  map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (a_live st)).

Definition AI (Y : list (AsanCtrl.aptr * Z)) (s : APS) (mo : Model) : Prop :=
  INV (aps_resv s) (aps_atop s) [] [] (aps_m s) mo
  /\ Permutation Y (live_pairs (aps_m s))
  /\ a_qloc_bytes (aps_m s) <= Q_CACHE /\ a_qglob_bytes (aps_m s) <= Q_MAX
  /\ minv (strip mo) /\ m_halted mo = None.

Fixpoint lcost (Y : list (AsanCtrl.aptr * Z)) : Z := match Y with [] => 0 | p :: Y' => snd p + Q_BATCH_BYTES + lcost Y' end.
Definition acost0 (st : astate) : Z := a_qloc_bytes st + a_qglob_bytes st + lcost (live_pairs st).
Definition nch (st : astate) : Z := zlen (live_pairs st) + nq st.
Definition acost (st : astate) : Z := Z.max (acost0 st) (Q_BATCH_BYTES * nch st).
Lemma acost_ge0 : forall st, acost0 st <= acost st. Proof. intros. unfold acost. apply Z.le_max_l. Qed.
Lemma acost_gen : forall st, Q_BATCH_BYTES * nch st <= acost st. Proof. intros. unfold acost. apply Z.le_max_r. Qed.
Ltac max_le := match goal with |- _ <= ?R => match R with context [Z.max ?A ?B] => pose proof (Z.le_max_l A B); pose proof (Z.le_max_r A B) end end;
               apply Z.max_lub; lia.
Lemma acost_ainit0 : forall sb pa, acost (ainit sb pa) = 0.
Proof.
  intros. unfold acost, acost0, nch, nq, live_pairs, ainit. cbn [a_qloc_bytes a_qglob_bytes a_live a_qloc a_qglob app].
  rewrite map_to_list_empty. reflexivity.
Qed.
Lemma zlen_perm : forall {A} (l l' : list A), Permutation l l' -> zlen l = zlen l'.
Proof. intros A l l' HP. unfold zlen. f_equal. apply Permutation_length. exact HP. Qed.

Lemma bsum_split : forall bs, Forall batch_wf bs -> bsum bs = Q_BATCH_BYTES * zlen bs + zsumc (qchunks bs).
Proof.
  induction bs as [|b bs IH]; intros HF.
  - unfold zlen. cbn. lia.
  - apply Forall_cons_iff in HF as [(B1 & B2 & B3 & B4) HF]. specialize (IH HF).
    cbn [bsum]. rewrite qchunks_cons, zsumc_app, zlen_cons, IH, B3. lia.
Qed.
Lemma lcost_pairs : forall (L : list (AsanCtrl.aptr * achunk)),
  lcost (map (fun kc => (fst kc, chunk_size (snd kc))) L) = zsumc (map snd L) + Q_BATCH_BYTES * zlen (map snd L)
  /\ zlen (map (fun kc => (fst kc, chunk_size (snd kc))) L) = zlen (map snd L).
Proof.
  induction L as [|[k ch] L [IH1 IH2]]; [unfold zlen; cbn; lia|].
  cbn [map lcost zsumc fst snd]. rewrite !zlen_cons, IH1, IH2. lia.
Qed.
Lemma W_cost : forall RESV ATOP st mo, INV RESV ATOP [] [] st mo -> 64 * W [] [] st <= 129 * acost st.
Proof.
  intros RESV ATOP st mo [HA _]. pose proof HA as (_ & _ & HBW & Hb1 & Hb2 & _).
  unfold qbatches in HBW. cbn [app] in HBW.
  pose proof (bsum_split _ HBW) as BS. rewrite bsum_app in BS.
  assert (L1 : lcost (live_pairs st) = zsumc (live_chunks st) + Q_BATCH_BYTES * zlen (live_chunks st))
    by exact (proj1 (lcost_pairs (map_to_list (a_live st)))).
  assert (L2 : zlen (live_pairs st) = zlen (live_chunks st)) by exact (proj2 (lcost_pairs (map_to_list (a_live st)))).
  pose proof (acost_ge0 st) as C0. pose proof (acost_gen st) as C1. unfold acost0, nch, nq in *.
  unfold W, all_chunks, qbatches. cbn [app]. rewrite zsumc_app, zlen_app.
  pose proof (zlen_nonneg (a_qloc st ++ a_qglob st)). pose proof (zlen_nonneg (live_chunks st)).
  rewrite Hb1, Hb2 in C0. unfold Q_BATCH_BYTES in *. lia.
Qed.
Lemma vroom_cost : forall RESV ATOP st mo, INV RESV ATOP [] [] st mo -> acost st <= Q_MAX -> vroom [] [] st.
Proof. intros RESV ATOP st mo HI HC. pose proof (W_cost _ _ _ _ HI). unfold vroom, WPCAP, Q_MAX in *. change (2 ^ 30) with 1073741824. change (2 ^ 22) with 4194304. lia. Qed.

Lemma lcost_perm : forall Y Y', Permutation Y Y' -> lcost Y = lcost Y'.
Proof. intros Y Y' HP. induction HP; cbn [lcost] in *; lia. Qed.
Lemma lcost_nonneg : forall Y, Forall (fun p => 0 <= snd p) Y -> 0 <= lcost Y.
Proof. intros Y HF. induction HF; cbn [lcost] in *; unfold Q_BATCH_BYTES in *; lia. Qed.

Lemma AI_perm : forall Y Y' s mo, Permutation Y Y' -> AI Y s mo -> AI Y' s mo.
Proof. intros Y Y' s mo HP (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3]. eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H2]. Qed.

Lemma AI_so : forall Y s mo v, AI Y s mo -> AI Y (aset_so v s) mo.
Proof. intros Y [m so rv atp] mo v H. exact H. Qed.

Lemma AI_model : forall Y s mo, AI Y s mo -> minvA mo /\ m_halted mo = None.
Proof. intros Y s mo (HI & _ & _ & _ & Hmi & Hh). split; [|exact Hh]. split; [exact Hmi|]. destruct HI as [_ (M1 & _)]. exact M1. Qed.

Lemma AI_fds : forall Y s mo f, AI Y s mo -> minvA (with_fds f mo) -> m_halted (with_fds f mo) = None -> AI Y s (with_fds f mo).
Proof.
  intros Y s mo f (HI & HP & Hq1 & Hq2 & Hmi & Hh) [Hmi' _] Hh'. unfold AI.
  split; [| repeat (split; [assumption|]); assumption].
  destruct HI as [HA HM]. split; [exact HA|]. apply AMI_with_fds. exact HM.
Qed.


Definition FR (mo mo' : Model) : Prop :=
  (minv (strip mo) -> minv (strip mo')) /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo.

Lemma FR_refl : forall mo, FR mo mo. Proof. intros. unfold FR. split; [intros H; exact H|]. split; [reflexivity|]. split; reflexivity. Qed.
Lemma FR_trans : forall m1 m2 m3, FR m1 m2 -> FR m2 m3 -> FR m1 m3.
Proof. intros m1 m2 m3 (A1&A2&A3&A4) (B1&B2&B3&B4). unfold FR. split; [intros H; apply B1, A1, H|]. split; [congruence|]. split; congruence. Qed.

Lemma FR_with_vmmaps_strip : forall mo mo' h, strip mo' = with_vmmaps h (strip mo) ->
  vm_init_sp h = vm_init_sp (m_vmmaps mo) ->
  m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> m_halted mo' = m_halted mo -> FR mo mo'.
Proof.
  intros mo mo' h Hs Hsp Hf Hfs Hh. unfold FR. split; [| split; [exact Hf| split; [exact Hfs| exact Hh]]].
  (* port727 (rme's NodesA c2 form): minv reads neither m_kernel nor vm_mmap_base, which 727298f3's vm_only now pins *)
  intros Hmi. rewrite Hs. apply minv_with_vmmapsA; [exact Hsp| exact Hmi].
Qed.

Lemma apost_FR : forall atop e mo z mo', apost atop e mo z mo' -> FR mo mo'.
Proof.
  intros atop e mo z mo' H. destruct e as [t|b|addr len prot flags|addr len|a l p|w]; cbn [AsanNodeSem.apost] in H; try contradiction.
  - destruct (addr =? 0).
    + destruct H as (_ & _ & _ & _ & ->). unfold grant_model. eapply FR_with_vmmaps_strip; try reflexivity.
    + destruct H as (_ & ->). unfold fixed_model. eapply (FR_with_vmmaps_strip _ _ (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)))).
      * rewrite strip_with_mmap_replacement. apply strip_with_vmmaps.
      * reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
      * unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b _); reflexivity.
  - destruct H as (_ & ->). unfold munmap_model. eapply FR_with_vmmaps_strip; try reflexivity.
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


Lemma sizes_live_pairs : forall st, map snd (live_pairs st) = sizes (live_chunks st).
Proof. intros. unfold live_pairs, sizes, live_chunks. rewrite !map_map. reflexivity. Qed.

Lemma HISTOK_perm : forall M M', Permutation M M' -> HISTOK M -> HISTOK M'.
Proof.
  intros M M' HP (I & Zl & H1 & H2 & H3 & H4 & H5). exists I, Zl. split; [|auto].
  eapply Permutation_trans; [apply Permutation_sym; exact HP| exact H1].
Qed.

Theorem asan_ok_malloc : forall Y n s mo,
  AI Y s mo -> 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
  acost (aps_m s) + n + Q_BATCH_BYTES <= Q_MAX ->
  STOTA (amalloc_M n s) mo
        (fun r s' mo' => exists q, r = Some q /\ AI ((q, n) :: Y) s' mo' /\ n < 2^63
                         /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ acost (aps_m s') <= acost (aps_m s) + n + Q_BATCH_BYTES).
Proof.
  intros Y n [st so RESV ATOP] mo HAI Hn HH HCST. pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (HWR : W [] [] st + 2 * n + 128 <= WCAP).
  { pose proof (W_cost _ _ _ _ HI). unfold WCAP, Q_MAX, Q_BATCH_BYTES, REQMAX in *. change (2 ^ 33) with 8589934592. lia. }
  unfold amalloc_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. apply (amalloc_core st mo n HI Hq1 Hq2 ltac:(unfold REQMAX in Hn; lia)); [| exact HWR| eapply vroom_cost; [exact HI| unfold Q_BATCH_BYTES in *; lia]].
    intros mb ms.
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
  assert (HPL : Permutation ((a_next st, n) :: live_pairs st) (live_pairs st')).
  { unfold live_pairs. rewrite Hlive.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
    cbn [map fst snd]. rewrite Hsz. apply Permutation_refl. }
  split; [| split; [unfold REQMAX in Hn; lia| split; [auto| split; [auto| split; [auto|]]]]].
  2:{ cbn [aps_m aset_m]. unfold acost, acost0, nch, nq. rewrite Eq1, Eq2, Eq3, Eq4, <- (lcost_perm _ _ HPL), <- (zlen_perm (A:=(AsanCtrl.aptr * Z)%type) _ _ HPL), zlen_cons.
      cbn [lcost snd]. unfold Q_BATCH_BYTES. max_le. }
  unfold AI. cbn [aps_m aset_m aps_so aps_atop aps_resv]. split; [exact HI2|]. split.
  - eapply Permutation_trans; [| exact HPL]. apply perm_skip. exact HPY.
  - rewrite Eq1, Eq2. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.


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
  STOTA (aannot_M q cap old new s) mo
        (fun _ s' mo' => AI Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ acost (aps_m s') <= acost (aps_m s)).
Proof.
  intros Y q cap old new [st so RESV ATOP] mo HAI Hin Hold Hnew Hmin. pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, cap) (live_pairs st)) by (eapply Permutation_in; [exact HPY| exact Hin]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold aannot_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. eapply aannotate_core; eauto. }
  cbv beta. intros st' s2 mo2 (-> & [-> HI2] & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| split; [auto| split; [auto| split; [auto| cbn [aps_m aset_m]; lia]]]].
  unfold AI. cbn [aps_m aset_m aps_atop aps_resv]. split; [exact HI2|]. split; [exact HPY|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.


Lemma live_pairs_nonneg : forall RESV ATOP st mo, INV RESV ATOP [] [] st mo -> Forall (fun p => 0 <= snd p) (live_pairs st).
Proof.
  intros RESV ATOP st mo [HA _]. destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW.
  apply Forall_app in HW as [HWl _]. unfold live_chunks in HWl. unfold live_pairs.
  rewrite Forall_map in HWl |- *. eapply Forall_impl; [| exact HWl]. intros [k ch] Hwf. cbn [fst snd] in *.
  destruct ch; cbn in Hwf |- *; lia.
Qed.

Theorem asan_ok_free : forall Y q n s mo,
  AI ((q, n) :: Y) s mo -> acost (aps_m s) <= Q_MAX ->
  STOTA (afree_M q s) mo
        (fun _ s' mo' => AI Y s' mo' /\ aps_so s' = aps_so s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo
                         /\ acost (aps_m s') <= acost (aps_m s)).
Proof.
  intros Y q n [st so RESV ATOP] mo HAI HCOST. pose proof HAI as (HI & HPY & Hq1 & Hq2 & Hmi & Hh). cbn [aps_m aps_atop aps_resv] in *.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (Hin' : In (q, n) (live_pairs st)) by (eapply Permutation_in; [exact HPY| left; reflexivity]).
  destruct (live_pairs_In _ _ _ Hin') as (ch & Hl & Hsz).
  unfold afree_M. eapply STOT_bind; [apply STOT_get|]. cbv beta. intros s0 s1 mo1 (-> & -> & ->).
  assert (HPD : Permutation ((q, n) :: map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st)))) (live_pairs st)).
  { unfold live_pairs. rewrite <- Hsz.
    change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
      with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
    apply Permutation_map. apply map_to_list_delete. exact Hl. }
  pose proof (live_pairs_nonneg _ _ _ _ HI) as HNN.
  assert (HNN' : 0 <= lcost (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))).
  { apply lcost_nonneg. pose proof (Permutation_Forall (Permutation_sym HPD) HNN) as X. apply Forall_cons_iff in X as [_ X]. exact X. }
  assert (HLC : lcost (live_pairs st) = n + Q_BATCH_BYTES + lcost (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))).
  { rewrite <- (lcost_perm _ _ HPD). reflexivity. }
  assert (HROOM : a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES <= Q_MAX).
  { pose proof (acost_ge0 st) as HC0. unfold acost0 in HC0. rewrite Hsz. lia. }
  pose proof (vroom_cost _ _ _ _ HI HCOST) as HVR.
  eapply STOT_bind.
  { apply (atotal_STOT_asan ATOP); [split; assumption| reflexivity|]. cbn [aps_m aps_atop aps_resv]. apply atotal_FR. eapply afree_core; eauto. }
  cbv beta. intros st' s2 mo2 (-> & (HI2 & Hlive & Hnext & Hq1' & Hq2' & HG & HNQ) & (F1 & F2 & F3 & F4)).
  eapply STOT_mono; [apply STOT_upd|]. cbv beta. intros [] s3 mo3 (-> & ->).
  split; [| split; [auto| split; [auto| split; [auto|]]]].
  2:{ cbn [aps_m aset_m]. specialize (HG ch Hl). rewrite Hsz in HG.
      assert (HZ : zlen (live_pairs st) = 1 + zlen (live_pairs st')).
      { rewrite <- (zlen_perm (A:=(AsanCtrl.aptr * Z)%type) _ _ HPD), zlen_cons. unfold live_pairs. rewrite Hlive. reflexivity. }
      assert (HL2 : lcost (live_pairs st') = lcost (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st)))))
        by (unfold live_pairs; rewrite Hlive; reflexivity).
      unfold acost, acost0, nch. rewrite HNQ, HLC, HL2. unfold Q_BATCH_BYTES in *. max_le. }
  unfold AI. cbn [aps_m aset_m aps_atop aps_resv]. split; [exact HI2|]. split.
  - unfold live_pairs at 1. rewrite Hlive. eapply (Permutation_cons_inv (a := (q, n))).
    eapply Permutation_trans; [exact HPY|]. apply Permutation_sym. exact HPD.
  - split; [exact Hq1'|]. split; [exact Hq2'|]. split; [apply F1; exact Hmi|]. rewrite F4. exact Hh.
Qed.

Lemma acost_malloc : forall st st' n ch,
  a_live st' = <[a_next st := ch]> (a_live st) -> (a_live st) !! (a_next st) = None -> chunk_size ch = n ->
  a_qloc_bytes st' = a_qloc_bytes st -> a_qglob_bytes st' = a_qglob_bytes st ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st -> 0 <= n ->
  acost st' <= acost st + n + Q_BATCH_BYTES.
Proof.
  intros st st' n ch Hlive Hnone Hsz Eq1 Eq2 Eq3 Eq4 Hn0.
  assert (HPL : Permutation ((a_next st, n) :: live_pairs st) (live_pairs st')).
  { unfold live_pairs. rewrite Hlive.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply map_to_list_insert; exact Hnone].
    cbn [map fst snd]. rewrite Hsz. apply Permutation_refl. }
  unfold acost, acost0, nch, nq. rewrite Eq1, Eq2, Eq3, Eq4, <- (lcost_perm _ _ HPL), <- (zlen_perm (A:=(AsanCtrl.aptr * Z)%type) _ _ HPL), zlen_cons.
  cbn [lcost snd]. unfold Q_BATCH_BYTES. max_le.
Qed.

Lemma lcost_delete : forall st q ch, (a_live st) !! q = Some ch ->
  lcost (live_pairs st) = chunk_size ch + Q_BATCH_BYTES
                          + lcost (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st)))).
Proof.
  intros st q ch Hl.
  assert (HPD : Permutation ((q, chunk_size ch) :: map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st)))) (live_pairs st)).
  { unfold live_pairs.
    change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
      with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
    apply Permutation_map. apply map_to_list_delete. exact Hl. }
  rewrite <- (lcost_perm _ _ HPD). reflexivity.
Qed.

Lemma acost_free : forall st q ch st', (a_live st) !! q = Some ch -> a_live st' = delete q (a_live st) ->
  a_qloc_bytes st' + a_qglob_bytes st' <= a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES ->
  nq st' = nq st + 1 ->
  acost st' <= acost st.
Proof.
  intros st q ch st' Hl Hlive HG HNQ.
  assert (HPD : Permutation ((q, chunk_size ch) :: live_pairs st') (live_pairs st)).
  { unfold live_pairs. rewrite Hlive.
    change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
      with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
    apply Permutation_map. apply map_to_list_delete. exact Hl. }
  unfold acost, acost0, nch. rewrite HNQ, <- (lcost_perm _ _ HPD), <- (zlen_perm (A:=(AsanCtrl.aptr * Z)%type) _ _ HPD), zlen_cons. cbn [lcost snd]. unfold Q_BATCH_BYTES in *.
  max_le.
Qed.

Lemma acost_room : forall RESV ATOP st mo q ch, INV RESV ATOP [] [] st mo -> (a_live st) !! q = Some ch -> acost st <= Q_MAX ->
  a_qloc_bytes st + a_qglob_bytes st + chunk_size ch + Q_BATCH_BYTES <= Q_MAX.
Proof.
  intros RESV ATOP st mo q ch HI Hl HC. pose proof (acost_ge0 st) as HC0. unfold acost0 in HC0. rewrite (lcost_delete st q ch Hl) in HC0.
  pose proof (live_pairs_nonneg _ _ _ _ HI) as HNN.
  assert (HPD : Permutation ((q, chunk_size ch) :: map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st)))) (live_pairs st)).
  { unfold live_pairs.
    change ((q, chunk_size ch) :: map (fun kc => (fst kc, chunk_size (snd kc))) (map_to_list (delete q (a_live st))))
      with (map (fun kc : AsanCtrl.aptr * achunk => (fst kc, chunk_size (snd kc))) ((q, ch) :: map_to_list (delete q (a_live st)))).
    apply Permutation_map. apply map_to_list_delete. exact Hl. }
  pose proof (Permutation_Forall (Permutation_sym HPD) HNN) as X. apply Forall_cons_iff in X as [_ X].
  pose proof (lcost_nonneg _ X). lia.
Qed.


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
  destruct n as [fd bs|fd bufs|path|fd buf count|fd|fd req| |code|req|a l p f|a l|a l p]; cbn [io_node] in Hio; try contradiction.
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


Definition PhiA : node -> Model -> Prop := fun _ _ => True.

Lemma nstepA_sub : forall n mo r mo' e, ~ nf_node n -> nstepA n mo r mo' e -> nstep n mo r mo' e.
Proof. intros n mo r mo' e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> nstepA n mo r mo e.
Proof. intros n mo r e Hnf H; destruct n; cbn [nf_node] in Hnf; try (exfalso; exact (Hnf I)); exact H. Qed.
Lemma nstepA_io : forall n mo r mo' e, io_node n -> nstep n mo r mo' e -> nstepA n mo r mo' e.
Proof. intros n mo r mo' e Hio H; destruct n; cbn [io_node] in Hio; try contradiction; exact H. Qed.

Lemma asan_room : CDONE Q_BATCH_BYTES + Driver.MAX_INPUT + Q_BATCH_BYTES + CRUNX Q_BATCH_BYTES <= Q_MAX.
Proof. rewrite CRUNX_eq. unfold CDONE, CK, Q_BATCH_BYTES, Driver.MAX_INPUT, Q_MAX. change (2 ^ (Z.of_nat 10 + 1)) with 2048. lia. Qed.
Lemma asan_qov0 : 0 <= Q_BATCH_BYTES. Proof. unfold Q_BATCH_BYTES. lia. Qed.
Lemma acost_so : forall v s, acost (aps_m (aset_so v s)) = acost (aps_m s). Proof. intros v [m so rv atp]. reflexivity. Qed.

Definition AAllocAsanOK : AAllocOK AAllocAsan nstepA PhiA minvA :=
  mkAAllocOK AAllocAsan nstepA PhiA minvA nstepA_sub nstepA_same nstepA_io asan_ok_MI2
    aps_get_set aps_set_set aps_set_get aps_addr_so
    AI AI_perm AI_so AI_model AI_fds
    Q_BATCH_BYTES Q_MAX asan_qov0 asan_room (fun s => acost (aps_m s)) acost_so
    (fun Y n s mo HA Hn HH HCST _ => asan_ok_malloc Y n s mo HA Hn HH HCST)
    (fun Y q n s mo HA HC _ => asan_ok_free Y q n s mo HA HC)
    (fun Y q cap old new s mo HA Hin Ho Hn Hz _ => asan_ok_annot Y q cap old new s mo HA Hin Ho Hn Hz).
