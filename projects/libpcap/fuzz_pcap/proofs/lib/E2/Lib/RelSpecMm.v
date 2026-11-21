(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: mmap's freely placed arms (place_declined_b premises and lemmas, the linux_place address and its witnesses), mprotect's vDSO premise, munmap in the injected allocation family, and mremap's TASK_SIZE -EINVAL arm, split grow arm and move to Linux's one placement. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree RelSpec Nodes PlacementSearch.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export Lps04.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_err_out (forced : bool) (m : Model) (o : outcome SyscallEffect) : Prop :=
  exists e, In e (mmap_errnos_when forced) /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

Lemma mmap_err_out_false : forall m o, mmap_err_out false m o <-> False.
Proof. intros m o. unfold mmap_err_out. cbn. split; [intros (e & [] & _) | intros []]. Qed.

(* LPS 727298f3: the two freely placed arms of [mmap_spec] open with
   [m <- get_model ;; ... if place_declined_b (m_kernel m) h addr nZ then unmodeled],
   and the placed address is [linux_place]'s answer.  A NULL hint is never declined:
   the first conjunct is [negb (hint_address hint =? 0)], false by computation. *)
Lemma place_declined_b_null : forall kb h nZ,
  place_declined_b kb h (Z_to_bv 64 0) nZ = false.
Proof.
  intros kb h nZ. unfold place_declined_b, hint_address.
  rewrite (unsigned_lit 0) by lia. reflexivity.
Qed.

(* An [Ok] answer of a freely placed arm says the hint was not declined: the declined
   branch answers [Unmodeled] only. *)
Lemma mmap_ok_not_declined : forall addr len prot flags fd off i m eff m' evs,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  (mmap_modeled_b prot flags off = true \/ mmap_noaccess_b prot flags off = true) ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs) ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = false.
Proof.
  intros addr len prot flags fd off i m eff m' evs Hoff Hanon Hlen Hmn H.
  destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)))
    eqn:Hdecl; [exfalso|reflexivity].
  revert H. unfold mmap_spec. rewrite Hoff, Hanon, Hlen. cbn [negb].
  destruct (mmap_modeled_b prot flags off) eqn:Hm; cbv beta iota.
  - rewrite bind_model. cbv beta zeta. rewrite Hdecl. intros H.
    cbv beta iota delta [unmodeled] in H. discriminate H.
  - destruct Hmn as [Hmn | Hmn]; [discriminate Hmn|]. rewrite Hmn. cbv beta iota.
    rewrite bind_model. cbv beta zeta. rewrite Hdecl. intros H.
    cbv beta iota delta [unmodeled] in H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = true ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = false ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out true m o
  \/ exists a, (linux_place h (kb_thp (m_kernel m)) addr nZ (bv_unsigned a)
                /\ mmap_noreserve_backed_ok flags m nZ = true)
               /\ o = Ok (mkEffect a [] [(a, n)])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                               (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hdecl. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Hanon, Hlen, Hmod. cbn [negb].
  rewrite bind_model. cbv beta zeta. rewrite Hdecl. cbv beta iota.
  unfold mmap_err_out, mmap_errnos_when. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* Given an [Ok] answer: the decline is ruled out by the answer itself, and the placed
   address meets the four conditions [Placement.linux_place_admissible] reads off
   [linux_place]. *)
Lemma mmap_rw_ok_inv : forall addr len prot flags fd off i m eff m' evs,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs) ->
  mmap_err_out true m (Ok eff m' evs)
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z
                /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ mmap_noreserve_backed_ok flags m nZ = true)
               /\ Ok eff m' evs = Ok (mkEffect a [] [(a, n)])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                               (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m eff m' evs Hoff Hanon Hlen Hmod. cbv zeta. intros H.
  pose proof (mmap_ok_not_declined _ _ _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen (or_introl Hmod) H) as Hdecl.
  apply (mmap_rw_outcome _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen Hmod Hdecl) in H.
  destruct H as [He | (a & (Hpl & Hnr) & Heq)]; [left; exact He|right].
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z /\ (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z).
  { split; [|apply page_round_up_Z_aligned].
    pose proof (Syscall.w_is0_false_pos len Hlen). pose proof (page_round_up_Z_ge (bv_unsigned len)). lia. }
  destruct (Placement.linux_place_admissible _ _ _ _ _ (proj1 HnZ) (proj2 HnZ) Hpl) as (A1 & A2 & A3 & A4).
  rewrite Z_to_bv_bv_unsigned in A4.
  exists a. split; [|exact Heq]. repeat split; assumption.
Qed.

Lemma mmap_noaccess_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = true ->
  place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = false ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out true m o
  \/ exists a, linux_place h (kb_thp (m_kernel m)) addr nZ (bv_unsigned a)
               /\ o = Ok (mkEffectU a [] [] [(a, n)] [] [])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
                               (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hdecl. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Hanon, Hlen, Hmod, Hna. cbn [negb].
  rewrite bind_model. cbv beta zeta. rewrite Hdecl. cbv beta iota.
  unfold mmap_err_out, mmap_errnos_when. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. eexists _, _, _, _. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noaccess_ok_inv : forall addr len prot flags fd off i m eff m' evs,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs) ->
  mmap_err_out true m (Ok eff m' evs)
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z
                /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
               /\ Ok eff m' evs = Ok (mkEffectU a [] [] [(a, n)] [] [])
                        (with_mmap_backing flags a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
                               (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m eff m' evs Hoff Hanon Hlen Hmod Hna. cbv zeta. intros H.
  pose proof (mmap_ok_not_declined _ _ _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen (or_intror Hna) H) as Hdecl.
  apply (mmap_noaccess_outcome _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen Hmod Hna Hdecl) in H.
  destruct H as [He | (a & Hpl & Heq)]; [left; exact He|right].
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z /\ (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z).
  { split; [|apply page_round_up_Z_aligned].
    pose proof (Syscall.w_is0_false_pos len Hlen). pose proof (page_round_up_Z_ge (bv_unsigned len)). lia. }
  destruct (Placement.linux_place_admissible _ _ _ _ _ (proj1 HnZ) (proj2 HnZ) Hpl) as (A1 & A2 & A3 & A4).
  rewrite Z_to_bv_bv_unsigned in A4.
  exists a. split; [|exact Heq]. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true -> mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out true m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
         (with_mmap_replacement flags addr n
            (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
               ((addr, n) :: maps_subtract (vm_noaccess h)
                               (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []
  \/ (exists e, In e mmap_errnos /\
        o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
               (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har. pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfx. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. lia. }
  rewrite E1. rewrite bind_model. cbv beta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out, mmap_errnos_when. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. reflexivity.
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [-> | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; [|reflexivity].
      eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mprotect_expose_outcome : forall addr len prot i m o,
  mprotect_grows_conflict_b prot = false ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  mprotect_modeled_b prot = true ->
  map_contains (vm_noaccess h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  (* LPS 727298f3: [mprotect_spec] answers [unmodeled] for a range that meets the
     vDSO/vvar pair, before it reads the maps. *)
  region_free (vdso_reserved (m_kernel m) (vdso_top h)) addr n = true ->
  mprotect_spec addr len prot i m o <->
  (exists e, In e mprotect_errnos
             /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ (mprotect_budget_ok m addr n = true
      /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model_next m addr n) []).
Proof.
  intros addr len prot i m o Hgc Hal Hlen. cbv zeta. intros Hnw Hmod Hna Hmc Hvd.
  unfold mprotect_spec. rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod.
  cbn [negb]. rewrite bind_model. cbv beta zeta. rewrite Hvd. cbn [negb]. rewrite Hna, Hmc. cbn [andb]. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Open Scope Z_scope.

Lemma refusal_b_222 : forall args m r,
  refusal_b (pure_input 222 args) m r = ret_in_errnos mmap_errnos r.
Proof. reflexivity. Qed.

Lemma refusal_b_226 : forall args m r,
  refusal_b (pure_input 226 args) m r = ret_in_errnos mprotect_errnos r.
Proof. reflexivity. Qed.

Lemma refusal_b_216 : forall args m r,
  refusal_b (pure_input 216 args) m r = ret_in_errnos mremap_errnos r.
Proof. reflexivity. Qed.

Lemma family_off_222 : forall args, injected_family_off CFG (pure_input 222 args) = true.
Proof. reflexivity. Qed.
Lemma family_off_226 : forall args, injected_family_off CFG (pure_input 226 args) = true.
Proof. reflexivity. Qed.
Lemma family_off_216 : forall args, injected_family_off CFG (pure_input 216 args) = true.
Proof. reflexivity. Qed.
Lemma family_off_214 : forall args, injected_family_off CFG (pure_input 214 args) = true.
Proof. reflexivity. Qed.
(* 08b1429: munmap (215) joined the injected allocation family (Run.v injected_table,
   mkInjectedArm 215 FamAlloc munmap_errnos), so under CFG its family is off. *)
Lemma family_off_215 : forall args, injected_family_off CFG (pure_input 215 args) = true.
Proof. reflexivity. Qed.
Lemma refusal_b_215 : forall args m r,
  refusal_b (pure_input 215 args) m r = ret_in_errnos munmap_errnos r.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ret_in_errnos_in : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e H. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact H| apply bv_eqb_refl].
Qed.

(* [comment removed for export] *)
Lemma ret_in_enomem_small : forall r, bv_unsigned r < 2^64 - 4095 ->
  ret_in_errnos [ENOMEM] r = false.
Proof.
  intros r Hr. unfold ret_in_errnos. cbn [existsb]. rewrite orb_false_r.
  unfold bv_eqb. apply Z.eqb_neq. intros E. rewrite E in Hr. revert Hr. vm_compute. intros Hr. discriminate Hr.
Qed.

Lemma ret_in_mmap_small : forall r, bv_unsigned r < 2^64 - 4095 -> ret_in_errnos mmap_errnos r = false.
Proof. exact ret_in_enomem_small. Qed.
Lemma ret_in_mprotect_small : forall r, bv_unsigned r < 2^64 - 4095 -> ret_in_errnos mprotect_errnos r = false.
Proof. exact ret_in_enomem_small. Qed.
Lemma ret_in_mremap_small : forall r, bv_unsigned r < 2^64 - 4095 -> ret_in_errnos mremap_errnos r = false.
Proof. exact ret_in_enomem_small. Qed.

(* [comment removed for export] *)
Lemma grant_not_errno : forall (a : word) h nZ, 0 <= nZ -> bv_unsigned a + nZ <= alloc_top h -> bv_unsigned a < 2^64 - 4095.
Proof. intros a h nZ Hn H. pose proof (alloc_top_room h). unfold stack_max_size, two_pow_64 in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grant_witness : forall flags m nZ,
  band_ceiling <= alloc_top (m_vmmaps m) ->
  mmap_grant_refusable flags m nZ = false ->
  exists a, (bv_unsigned a mod page_size = 0)
            /\ (0 < bv_unsigned a)
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true
            /\ mmap_noreserve_backed_ok flags m nZ = true.
Proof.
  intros flags m nZ Hband H. unfold mmap_grant_refusable in H. apply orb_false_iff in H as [H1 H2].
  apply negb_false_iff in H1. apply negb_false_iff in H2.
  apply vm_gap_available_find in H2 as [a Ha]. apply vm_find_base_sound in Ha as (A1 & A2 & A3 & A4 & A5).
  exists a. repeat split; try assumption. lia.
Qed.

Lemma reserve_witness : forall m nZ,
  band_ceiling <= alloc_top (m_vmmaps m) ->
  mmap_reserve_refusable m nZ = false ->
  exists a, (bv_unsigned a mod page_size = 0)
            /\ (0 < bv_unsigned a)
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros m nZ Hband H. unfold mmap_reserve_refusable in H. apply negb_false_iff in H.
  apply vm_gap_available_find in H as [a Ha]. apply vm_find_base_sound in Ha as (A1 & A2 & A3 & A4 & A5).
  exists a. repeat split; try assumption. lia.
Qed.

(* The search's base [a] fits the revision's bottom-up window [task_unmapped_base,
   alloc_top) ([bottomup_floor] is above [task_unmapped_base]), so [linux_place] has an
   answer ([Placement.linux_place_exists]), whatever the hint. *)
Lemma gap_base_fits : forall h nZ a,
  band_ceiling <= alloc_top h ->
  vm_find_base h nZ = Some a ->
  gap_fits (vm_reserved h ++ vm_maps h) task_unmapped_base (alloc_top h) nZ (bv_unsigned a).
Proof.
  intros h nZ a Hband Ha. apply vm_find_base_sound in Ha as (A1 & A2 & A3 & A4 & A5).
  unfold gap_fits. rewrite Z_to_bv_bv_unsigned.
  split; [exact A1|]. split; [unfold task_unmapped_base, bottomup_floor in *; lia|].
  split; [lia | exact A5].
Qed.

Lemma place_word_of : forall h thp hint nZ aZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  linux_place h thp hint nZ aZ ->
  exists a : word, aZ = bv_unsigned a /\ linux_place h thp hint nZ (bv_unsigned a).
Proof.
  intros h thp hint nZ aZ Hn1 Hn2 Hpl.
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hn1 Hn2 Hpl) as (_ & B2 & B3 & _).
  pose proof (alloc_top_room h). unfold stack_max_size, two_pow_64 in *.
  exists (Z_to_bv 64 aZ). rewrite unsigned_lit by lia. split; [reflexivity | exact Hpl].
Qed.

Lemma grant_place_witness : forall flags m hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  band_ceiling <= alloc_top (m_vmmaps m) ->
  mmap_grant_refusable flags m nZ = false ->
  exists a : word, linux_place (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ (bv_unsigned a)
                   /\ mmap_noreserve_backed_ok flags m nZ = true.
Proof.
  intros flags m hint nZ Hn1 Hn2 Hband H. unfold mmap_grant_refusable in H. apply orb_false_iff in H as [H1 H2].
  apply negb_false_iff in H1. apply negb_false_iff in H2.
  apply vm_gap_available_find in H2 as [a Ha].
  destruct (Placement.linux_place_exists (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ Hn1 Hn2) as [aZ HaZ].
  { exists (bv_unsigned a). right. exact (gap_base_fits _ _ _ Hband Ha). }
  destruct (place_word_of _ _ _ _ _ Hn1 Hn2 HaZ) as (a' & _ & Ha').
  exists a'. split; [exact Ha' | exact H1].
Qed.

Lemma reserve_place_witness : forall m hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  band_ceiling <= alloc_top (m_vmmaps m) ->
  mmap_reserve_refusable m nZ = false ->
  exists a : word, linux_place (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ (bv_unsigned a).
Proof.
  intros m hint nZ Hn1 Hn2 Hband H. unfold mmap_reserve_refusable in H. apply negb_false_iff in H.
  apply vm_gap_available_find in H as [a Ha].
  destruct (Placement.linux_place_exists (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ Hn1 Hn2) as [aZ HaZ].
  { exists (bv_unsigned a). right. exact (gap_base_fits _ _ _ Hband Ha). }
  destruct (place_word_of _ _ _ _ _ Hn1 Hn2 HaZ) as (a' & _ & Ha').
  exists a'. exact Ha'.
Qed.

Lemma len_round_pos : forall len : word, w_is0 len = false ->
  (0 < page_round_up_Z (bv_unsigned len))%Z /\ (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z.
Proof.
  intros len Hlen. split; [|apply page_round_up_Z_aligned].
  pose proof (Syscall.w_is0_false_pos len Hlen). pose proof (page_round_up_Z_ge (bv_unsigned len)). lia.
Qed.

Lemma page_round_up_Z_nonneg' : forall z, 0 <= z -> 0 <= page_round_up_Z z.
Proof. intros z Hz. unfold page_round_up_Z, page_size. apply Z.mul_nonneg_nonneg; [|lia]. apply Z.div_pos; lia. Qed.

Section NstepMmap.
Variables (addr len prot flags : Z).
Let aw := Z_to_bv 64 addr.  Let lw := Z_to_bv 64 len.  Let pw := Z_to_bv 64 prot.  Let fw := Z_to_bv 64 flags.
Let i := pure_input 222 [aw; lw; pw; fw; Z_to_bv 64 (-1); Z_to_bv 64 0].

#[using="Type"] Lemma nstep_mmap_spec : forall mo eff mo' evs,
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  evs = [] /\ mmap_spec aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo (Ok eff mo' evs)
  /\ ~ spurious_refusal_cfg CFG i mo eff.
Proof.
  intros mo eff mo' evs (He & Hsp & Hns). split; [exact He|]. split; [|exact Hns].
  rewrite syscall_spec_222 in Hsp by reflexivity. exact Hsp.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nstep_mmap_errno_forced : forall mo e mo' evs eff1 mo1 evs1,
  nstep (NMmap addr len prot flags) mo (mkEffect (errno_ret e) [] []) mo' evs -> In e mmap_errnos ->
  mmap_spec aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo (Ok eff1 mo1 evs1) ->
  ret_in_errnos mmap_errnos (eff_ret eff1) = true.
Proof.
  intros mo e mo' evs eff1 mo1 evs1 Hst He Hsp1.
  destruct (ret_in_errnos mmap_errnos (eff_ret eff1)) eqn:E; [reflexivity|]. exfalso.
  destruct Hst as (_ & _ & Hns). apply Hns. split; [reflexivity|]. split.
  - rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_errnos_in. exact He.
  - exists eff1, mo1, evs1. split; [rewrite syscall_spec_222 by reflexivity; exact Hsp1| rewrite refusal_b_222; exact E].
Qed.

(* [comment removed for export] *)
#[using="aw i"] Lemma nstep_mmap_rw_outcome : forall mo eff mo' evs,
  mmap_off_aligned_b (Z_to_bv 64 0) = true -> mmap_anon_b fw = true ->
  w_is0 lw = false -> mmap_modeled_b pw fw (Z_to_bv 64 0) = true ->
  band_ceiling <= alloc_top (m_vmmaps mo) ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned lw) in
  let n := Z_to_bv 64 nZ in
  mmap_err_out (mmap_grant_refusable fw mo nZ) mo (Ok eff mo' evs)
  \/ exists a, ((bv_unsigned a mod page_size = 0)
                /\ (0 < bv_unsigned a)
                /\ (bv_unsigned a + nZ <= alloc_top h)
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ mmap_noreserve_backed_ok fw mo nZ = true)
               /\ Ok eff mo' evs = Ok (mkEffect a [] [(a, n)])
                        (with_mmap_backing fw a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                               (vm_mmap_base h) (vm_init_sp h)) mo)) [].
Proof.
  intros mo eff mo' evs Hoff Hanon Hlen Hmod Hband Hst. cbv zeta.
  pose proof (nstep_mmap_spec _ _ _ _ Hst) as (_ & Hsp & _).
  pose proof (mmap_ok_not_declined _ _ _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen (or_introl Hmod) Hsp) as Hdecl.
  pose proof (mmap_rw_ok_inv _ _ _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen Hmod Hsp) as [(e & He & Heq) | Hg]; [|right; exact Hg].
  left. apply Ok_inj in Heq as (-> & -> & ->). exists e. split; [|reflexivity].
  destruct (mmap_grant_refusable fw mo (page_round_up_Z (bv_unsigned lw))) eqn:Er; [exact He|]. exfalso.
  pose proof (len_round_pos lw Hlen) as [Hn1 Hn2].
  destruct (grant_place_witness fw mo aw _ Hn1 Hn2 Hband Er) as (a & Hpl & Hnr).
  pose proof (nstep_mmap_errno_forced mo e mo [] _ _ _ Hst He
                (proj2 (mmap_rw_outcome aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo _ Hoff Hanon Hlen Hmod Hdecl)
                   (or_intror (ex_intro _ a (conj (conj Hpl Hnr) eq_refl))))) as Hr.
  cbn [eff_ret] in Hr. rewrite (ret_in_mmap_small a) in Hr; [discriminate|].
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hn1 Hn2 Hpl) as (_ & _ & A3 & _).
  eapply grant_not_errno; [|exact A3]. lia.
Qed.

(* [comment removed for export] *)
#[using="aw i"] Lemma nstep_mmap_noaccess_outcome : forall mo eff mo' evs,
  mmap_off_aligned_b (Z_to_bv 64 0) = true -> mmap_anon_b fw = true ->
  w_is0 lw = false -> mmap_modeled_b pw fw (Z_to_bv 64 0) = false -> mmap_noaccess_b pw fw (Z_to_bv 64 0) = true ->
  band_ceiling <= alloc_top (m_vmmaps mo) ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned lw) in
  let n := Z_to_bv 64 nZ in
  mmap_err_out (mmap_reserve_refusable mo nZ) mo (Ok eff mo' evs)
  \/ exists a, ((bv_unsigned a mod page_size = 0)
                /\ (0 < bv_unsigned a)
                /\ (bv_unsigned a + nZ <= alloc_top h)
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
               /\ Ok eff mo' evs = Ok (mkEffectU a [] [] [(a, n)] [] [])
                        (with_mmap_backing fw a n
                          (with_vmmaps
                            (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                               ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h)
                               (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) [].
Proof.
  intros mo eff mo' evs Hoff Hanon Hlen Hmod Hna Hband Hst. cbv zeta.
  pose proof (nstep_mmap_spec _ _ _ _ Hst) as (_ & Hsp & _).
  pose proof (mmap_ok_not_declined _ _ _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen (or_intror Hna) Hsp) as Hdecl.
  pose proof (mmap_noaccess_ok_inv _ _ _ _ _ _ _ _ _ _ _ Hoff Hanon Hlen Hmod Hna Hsp) as [(e & He & Heq) | Hg]; [|right; exact Hg].
  left. apply Ok_inj in Heq as (-> & -> & ->). exists e. split; [|reflexivity].
  destruct (mmap_reserve_refusable mo (page_round_up_Z (bv_unsigned lw))) eqn:Er; [exact He|]. exfalso.
  pose proof (len_round_pos lw Hlen) as [Hn1 Hn2].
  destruct (reserve_place_witness mo aw _ Hn1 Hn2 Hband Er) as (a & Hpl).
  pose proof (nstep_mmap_errno_forced mo e mo [] _ _ _ Hst He
                (proj2 (mmap_noaccess_outcome aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo _ Hoff Hanon Hlen Hmod Hna Hdecl)
                   (or_intror (ex_intro _ a (conj Hpl eq_refl))))) as Hr.
  cbn [eff_ret] in Hr. rewrite (ret_in_mmap_small a) in Hr; [discriminate|].
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hn1 Hn2 Hpl) as (_ & _ & A3 & _).
  eapply grant_not_errno; [|exact A3]. lia.
Qed.

(* [comment removed for export] *)
#[using="i"] Lemma nstep_mmap_fixed_noaccess_outcome : forall mo eff mo' evs,
  mmap_off_aligned_b (Z_to_bv 64 0) = true -> mmap_anon_b fw = true ->
  w_is0 lw = false -> mmap_modeled_b pw fw (Z_to_bv 64 0) = false -> mmap_noaccess_b pw fw (Z_to_bv 64 0) = false ->
  mmap_fixed_noaccess_b pw fw (Z_to_bv 64 0) = true ->
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned lw) in
  let n := Z_to_bv 64 nZ in
  bv_unsigned aw + nZ <= alloc_top h -> bv_unsigned aw mod page_size = 0 -> 0 < bv_unsigned aw ->
  region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  Ok eff mo' evs = Ok (mkEffectU aw [] [] [(aw, n)] [] [])
         (with_mmap_replacement fw aw n
            (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
               ((aw, n) :: maps_subtract (vm_noaccess h)
                               (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) [].
Proof.
  intros mo eff mo' evs Hoff Hanon Hlen Hmod Hna Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc Hst.
  pose proof (nstep_mmap_spec _ _ _ _ Hst) as (_ & Hsp & Hns).
  pose proof (mmap_fixed_noaccess_outcome aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo) as Hout.
  cbv zeta in Hout.
  assert (Hsucc := proj2 (Hout _ Hoff Hanon Hlen Hmod Hna Hfx Hce Hal Hpos Hrf Hmc) (or_intror (or_introl eq_refl))).
  assert (Hnr : ret_in_errnos mmap_errnos aw = false).
  { apply ret_in_mmap_small. eapply grant_not_errno; [|exact Hce]. apply page_round_up_Z_nonneg'. apply bv_unsigned_in_range. }
  assert (Hspur : forall eff0, ret_in_errnos mmap_errnos (eff_ret eff0) = true -> spurious_refusal_cfg CFG i mo eff0).
  { intros eff0 Hr. split; [reflexivity|]. split; [exact Hr|].
    eexists _, _, _. split; [rewrite syscall_spec_222 by reflexivity; exact Hsucc|]. exact Hnr. }
  apply (Hout _ Hoff Hanon Hlen Hmod Hna Hfx Hce Hal Hpos Hrf Hmc) in Hsp as [(e & He & Heq) | [Heq | (e & He & Heq)]].
  - exfalso. apply Ok_inj in Heq as (-> & _ & _). apply Hns, Hspur. cbn [eff_ret]. apply ret_in_errnos_in. exact He.
  - exact Heq.
  - exfalso. apply Ok_inj in Heq as (-> & _ & _). apply Hns, Hspur. cbn [eff_ret]. apply ret_in_errnos_in. exact He.
Qed.

End NstepMmap.

(* An [Ok] answer of [mprotect_spec]'s modeled arm says the range missed the vDSO/vvar
   pair: a range meeting it answers [Unmodeled] only. *)
Lemma mprotect_ok_vdso_free : forall addr len prot i m eff m' evs,
  mprotect_grows_conflict_b prot = false ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  mprotect_modeled_b prot = true ->
  mprotect_spec addr len prot i m (Ok eff m' evs) ->
  region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true.
Proof.
  intros addr len prot i m eff m' evs Hgc Hal Hlen Hnw Hmod H.
  destruct (region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hvd; [reflexivity|exfalso].
  revert H. unfold mprotect_spec. rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod.
  cbn [negb]. rewrite bind_model. cbv beta zeta. rewrite Hvd. cbn [negb]. intros H.
  cbv beta iota delta [unmodeled] in H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma nstep_mprotect_expose_outcome : forall addr len prot mo eff mo' evs,
  let aw := Z_to_bv 64 addr in let lw := Z_to_bv 64 len in let pw := Z_to_bv 64 prot in
  mprotect_grows_conflict_b pw = false ->
  (bv_unsigned aw mod page_size = 0) ->
  w_is0 lw = false ->
  let h := m_vmmaps mo in
  let nZ := page_round_up_Z (bv_unsigned lw) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned aw + nZ < two_pow_64) ->
  mprotect_modeled_b pw = true ->
  map_contains (vm_noaccess h) aw n = true ->
  map_contains (vm_maps h) aw n = true ->
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  (exists e, In e (mprotect_errnos_when (mprotect_refusable mo aw n))
             /\ Ok eff mo' evs = Ok (mkEffect (errno_ret e) [] []) mo [])
  \/ (mprotect_budget_ok mo aw n = true
      /\ Ok eff mo' evs = Ok (mkEffect (Z_to_bv 64 0) [] [(aw, n)]) (mprotect_model_next mo aw n) []).
Proof.
  intros addr len prot mo eff mo' evs aw lw pw Hgc Hal Hlen h nZ n Hnw Hmod Hna Hmc (_ & Hsp & Hns).
  cbn [node_input] in Hsp, Hns. fold aw lw pw in Hsp, Hns.
  set (i := pure_input 226 [aw; lw; pw]) in *.
  rewrite syscall_spec_226 in Hsp by reflexivity. cbn [in_arg in_args pure_input nth i] in Hsp.
  pose proof (mprotect_expose_outcome aw lw pw i mo) as Hout. cbv zeta in Hout. fold nZ n h in Hout.
  pose proof (mprotect_ok_vdso_free aw lw pw i mo eff mo' evs Hgc Hal Hlen Hnw Hmod Hsp) as Hvd. fold nZ n h in Hvd.
  apply (Hout _ Hgc Hal Hlen Hnw Hmod Hna Hmc Hvd) in Hsp as [(e & He & Heq) | Hg]; [|right; exact Hg].
  left. exists e. split; [|exact Heq]. apply Ok_inj in Heq as (-> & -> & ->).
  unfold mprotect_errnos_when, mprotect_refusable.
  destruct (mprotect_budget_ok mo aw n) eqn:Eb; [|exact He]. exfalso. apply Hns.
  split; [reflexivity|]. split; [unfold i; rewrite refusal_b_226; cbn [eff_ret]; apply ret_in_errnos_in; exact He|].
  eexists _, _, _. split.
  - unfold i. rewrite syscall_spec_226 by reflexivity. cbn [in_arg in_args pure_input nth].
    apply (Hout _ Hgc Hal Hlen Hnw Hmod Hna Hmc Hvd). right. split; reflexivity.
  - unfold i. rewrite refusal_b_226. cbn [eff_ret]. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nsafe_of : forall (spec : Sys SyscallEffect) i mo,
  (forall o, syscall_spec i mo o <-> spec i mo o) ->
  ~ spec i mo Unmodeled -> (exists o, spec i mo o) -> spec_live i mo.
Proof.
  intros spec i mo Hc Hnu [o Ho]. split.
  - intros Hu. apply Hnu. apply Hc. exact Hu.
  - exists o. apply Hc. exact Ho.
Qed.

Lemma page_round_up_Z_pos : forall z, 0 < z -> 4096 <= page_round_up_Z z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  assert (1 <= (z + 4096 - 1) / 4096) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma nsafe_brk : forall req mo, nsafe (NBrk req) mo.
Proof.
  intros req mo. cbn [nsafe node_input].
  set (rq := Z_to_bv 64 req). set (b := vm_brk (m_vmmaps mo)).
  assert (Hb : brk_r_ok mo rq b = true).
  { unfold brk_r_ok. cbv zeta. fold b.
    destruct (w_is0 rq || _)%bool; [apply bv_eqb_refl|].
    destruct (bv_unsigned rq <? _); rewrite bv_eqb_refl, ?orb_true_r; [reflexivity|].
    cbn [andb]. unfold brk_grow_ok. cbv zeta. fold b. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. }
  assert (Hout : forall r, brk_r_ok mo rq r = true ->
            syscall_spec (pure_input 214 [rq]) mo
              (Ok (mkEffectU r [] (brk_zeros rq r b) (brk_unmaps r b) [] []) (with_brk_next mo rq r) [])).
  { intros r Hr. rewrite syscall_spec_214 by reflexivity. cbn [in_arg in_args pure_input nth]. apply brk_outcome. exists r. auto. }
  split.
  - apply (nsafe_of (brk_spec rq)).
    + intros o. rewrite syscall_spec_214 by reflexivity. reflexivity.
    + intros Hu. apply brk_outcome in Hu as (r & _ & H). discriminate H.
    + eexists. apply brk_outcome. exists b. split; [exact Hb|reflexivity].
  - intros _.
    destruct (brk_refusal_b mo rq b) eqn:Eref.
    2:{ left. eexists _, _, _. split; [exact (Hout b Hb)|]. exact Eref. }
    destruct (brk_r_ok mo rq rq) eqn:Egr.
    + left. eexists _, _, _. split; [exact (Hout rq Egr)|].
      change (brk_refusal_b mo rq rq = false).
      unfold brk_refusal_b in Eref |- *. cbv zeta in Eref |- *. fold b in Eref |- *.
      apply andb_true_iff in Eref as [Eref _]. apply andb_true_iff in Eref as [_ Hne]. apply negb_true_iff in Hne.
      rewrite Hne, andb_false_r. reflexivity.
    + right. intros eff' m' evs' Hsp.
      rewrite syscall_spec_214 in Hsp by reflexivity. cbn [in_arg in_args pure_input nth] in Hsp.
      apply brk_outcome in Hsp as (r & Hr & Heq). apply Ok_inj in Heq as (-> & _ & _).
      change (brk_refusal_b mo rq r = true).
      assert (r = b); [|subst r; exact Eref].
      pose proof Eref as Eref'. unfold brk_refusal_b in Eref'. cbv zeta in Eref'. fold b in Eref'.
      apply andb_true_iff in Eref' as [Eref' _]. apply andb_true_iff in Eref' as [Eref' _]. apply andb_true_iff in Eref' as [Hq1 Hq2].
      apply negb_true_iff in Hq1. apply negb_true_iff in Hq2.
      unfold brk_r_ok in Hr, Egr. cbv zeta in Hr, Egr. fold b in Hr, Egr. rewrite Hq1, Hq2 in Hr, Egr. cbn [orb] in Hr, Egr.
      destruct (bv_unsigned rq <? bv_unsigned b).
      * rewrite bv_eqb_refl in Egr. discriminate Egr.
      * rewrite bv_eqb_refl in Egr. cbn [orb andb] in Egr.
        apply andb_true_iff in Hr as [Hor Hg]. apply orb_true_iff in Hor as [He|He]; apply bv_eqb_eq in He; [|exact He].
        subst r. rewrite Hg in Egr. discriminate Egr.
Qed.

Section NsafeMmap.
Variables (addr len prot flags : Z) (mo : Model).
Let aw := Z_to_bv 64 addr.  Let lw := Z_to_bv 64 len.  Let pw := Z_to_bv 64 prot.  Let fw := Z_to_bv 64 flags.
Let i := pure_input 222 [aw; lw; pw; fw; Z_to_bv 64 (-1); Z_to_bv 64 0].
Let sp := mmap_spec aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0).
Let h := m_vmmaps mo.
Let nZ := page_round_up_Z (bv_unsigned lw).

Hypothesis Hlen : 0 < len < 2^64.
(* LPS 727298f3: the freely placed arms answer [unmodeled] for a declined hint, so a
   lemma that rules [Unmodeled] out takes the decline test as a premise; each caller
   proves it where the hint is known. *)
Hypothesis Hdecl : place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr)
  (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false.

#[using="nZ Hlen"] Lemma nsafe_mmap_lw : w_is0 lw = false.
Proof. unfold lw. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia. Qed.

#[using="Hlen"] Lemma nsafe_mmap_nZ : 4096 <= nZ /\ nZ mod page_size = 0.
Proof.
  unfold nZ, lw. rewrite unsigned_lit by lia. split; [apply page_round_up_Z_pos; lia|apply page_round_up_Z_aligned].
Qed.

#[using="Type"] Lemma spec_i_iff : forall o, syscall_spec i mo o <-> sp i mo o.
Proof. intros o. unfold i, sp. rewrite syscall_spec_222 by reflexivity. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Hlen"] Lemma place_decides : forall (P : word -> Prop),
  (forall a : word, P a <-> (bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h
                             /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true)) ->
  {a : word | P a} + {forall a, ~ P a}.
Proof.
  intros P HP. pose proof nsafe_mmap_nZ as [Hn1 Hn2].
  destruct (place_in_model h nZ) as [a|] eqn:Ep.
  - left. exists (Z_to_bv 64 a). apply HP.
    destruct (place_in_model_admissible h nZ a ltac:(lia) Ep) as (_ & A1 & A2 & A3 & A4). auto.
  - right. intros a Ha. apply HP in Ha as (A1 & A2 & A3 & A4).
    destruct (place_in_model_complete h nZ (bv_unsigned a) ltac:(lia) Hn2 A1) as [a' Ha'].
    + unfold page_size in *. pose proof (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) as [Hd _]. destruct (Hd A1) as [k Hk]. lia.
    + exact A3.
    + rewrite Z_to_bv_bv_unsigned. exact A4.
    + congruence.
Qed.

(* [comment removed for export] *)
#[using="aw lw i sp h nZ Hlen Hdecl"] Lemma nsafe_mmap_rw_gen :
  mmap_off_aligned_b (Z_to_bv 64 0) = true -> mmap_anon_b fw = true -> mmap_modeled_b pw fw (Z_to_bv 64 0) = true ->
  nsafe (NMmap addr len prot flags) mo.
Proof.
  intros Hoff Hanon Hm. cbn [nsafe node_input]. fold aw lw pw fw i.
  pose proof nsafe_mmap_lw as Hl. pose proof nsafe_mmap_nZ as [Hn1 Hn2].
  pose proof (mmap_rw_outcome aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo) as Hout. cbv zeta in Hout. fold h nZ in Hout.
  assert (Herr : sp i mo (Ok (mkEffect (errno_ret ENOMEM) [] []) mo [])).
  { apply (Hout _ Hoff Hanon Hl Hm Hdecl). left. exists ENOMEM. split; [left; reflexivity|reflexivity]. }
  split.
  - apply (nsafe_of sp); [exact spec_i_iff| |eexists; exact Herr].
    intros Hu. apply (Hout _ Hoff Hanon Hl Hm Hdecl) in Hu. destruct Hu as [(e & _ & H) | (a & _ & H)]; discriminate H.
  - intros _.
    destruct (mmap_noreserve_backed_ok fw mo nZ) eqn:Eb.
    2:{ right. intros eff' m' evs' Hsp. apply spec_i_iff in Hsp. apply (Hout _ Hoff Hanon Hl Hm Hdecl) in Hsp.
        destruct Hsp as [(e & He & Heq) | (a & (_ & A5) & _)]; [|congruence].
        apply Ok_inj in Heq as (-> & _ & _). unfold i. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_errnos_in. exact He. }
    (* the placement is [linux_place]'s answer; its executable twin decides whether one exists *)
    assert (Hn0 : 0 < nZ) by lia.
    destruct (Placement.linux_place_b_spec h (kb_thp (m_kernel mo)) aw nZ Hn0 Hn2) as [Hsome Hnone].
    destruct (Placement.linux_place_b h (kb_thp (m_kernel mo)) aw nZ) as [aZ|] eqn:Ep.
    + destruct (place_word_of _ _ _ _ _ Hn0 Hn2 (proj1 (Hsome aZ) eq_refl)) as (a & _ & Hpl).
      left. eexists _, _, _. split.
      * apply spec_i_iff. apply (Hout _ Hoff Hanon Hl Hm Hdecl). right. exists a. split; [|reflexivity].
        split; [exact Hpl | first [exact Eb | reflexivity]].
      * unfold i. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_mmap_small.
        destruct (Placement.linux_place_admissible _ _ _ _ _ Hn0 Hn2 Hpl) as (_ & _ & A3 & _).
        eapply grant_not_errno; [|exact A3]. lia.
    + right. intros eff' m' evs' Hsp. apply spec_i_iff in Hsp. apply (Hout _ Hoff Hanon Hl Hm Hdecl) in Hsp.
      destruct Hsp as [(e & He & Heq) | (a & (Hpl & _) & _)]; [|exfalso; exact (proj1 Hnone eq_refl _ Hpl)].
      apply Ok_inj in Heq as (-> & _ & _). unfold i. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_errnos_in. exact He.
Qed.

(* [comment removed for export] *)
#[using="aw lw i sp h nZ Hlen Hdecl"] Lemma nsafe_mmap_none_gen :
  mmap_off_aligned_b (Z_to_bv 64 0) = true -> mmap_anon_b fw = true -> mmap_modeled_b pw fw (Z_to_bv 64 0) = false ->
  mmap_noaccess_b pw fw (Z_to_bv 64 0) = true ->
  nsafe (NMmap addr len prot flags) mo.
Proof.
  intros Hoff Hanon Hm Hn. cbn [nsafe node_input]. fold aw lw pw fw i.
  pose proof nsafe_mmap_lw as Hl. pose proof nsafe_mmap_nZ as [Hn1 Hn2].
  pose proof (mmap_noaccess_outcome aw lw pw fw (Z_to_bv 64 (-1)) (Z_to_bv 64 0) i mo) as Hout. cbv zeta in Hout. fold h nZ in Hout.
  assert (Herr : sp i mo (Ok (mkEffect (errno_ret ENOMEM) [] []) mo [])).
  { apply (Hout _ Hoff Hanon Hl Hm Hn Hdecl). left. exists ENOMEM. split; [left; reflexivity|reflexivity]. }
  split.
  - apply (nsafe_of sp); [exact spec_i_iff| |eexists; exact Herr].
    intros Hu. apply (Hout _ Hoff Hanon Hl Hm Hn Hdecl) in Hu. destruct Hu as [(e & _ & H) | (a & _ & H)]; discriminate H.
  - intros _.
    assert (Hn0 : 0 < nZ) by lia.
    destruct (Placement.linux_place_b_spec h (kb_thp (m_kernel mo)) aw nZ Hn0 Hn2) as [Hsome Hnone].
    destruct (Placement.linux_place_b h (kb_thp (m_kernel mo)) aw nZ) as [aZ|] eqn:Ep.
    + destruct (place_word_of _ _ _ _ _ Hn0 Hn2 (proj1 (Hsome aZ) eq_refl)) as (a & _ & Hpl).
      left. eexists _, _, _. split.
      * apply spec_i_iff. apply (Hout _ Hoff Hanon Hl Hm Hn Hdecl). right. exists a. split; [exact Hpl|reflexivity].
      * unfold i. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_mmap_small.
        destruct (Placement.linux_place_admissible _ _ _ _ _ Hn0 Hn2 Hpl) as (_ & _ & A3 & _).
        eapply grant_not_errno; [|exact A3]. lia.
    + right. intros eff' m' evs' Hsp. apply spec_i_iff in Hsp. apply (Hout _ Hoff Hanon Hl Hm Hn Hdecl) in Hsp.
      destruct Hsp as [(e & He & Heq) | (a & Hpl & _)]; [|exfalso; exact (proj1 Hnone eq_refl _ Hpl)].
      apply Ok_inj in Heq as (-> & _ & _). unfold i. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_errnos_in. exact He.
Qed.

End NsafeMmap.

(* [comment removed for export] *)
Lemma nsafe_mmap_rw : forall addr len mo,
  0 < len < 2^64 ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr)
    (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  nsafe (NMmap addr len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hlen Hdecl. apply nsafe_mmap_rw_gen; [exact Hlen|exact Hdecl|reflexivity|reflexivity|reflexivity]. Qed.

(* [comment removed for export] *)
Lemma nsafe_mmap_none : forall addr len mo,
  0 < len < 2^64 ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr)
    (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo.
Proof. intros addr len mo Hlen Hdecl. apply nsafe_mmap_none_gen; [exact Hlen|exact Hdecl|reflexivity|reflexivity|reflexivity|reflexivity]. Qed.

(* [comment removed for export] *)
Lemma nsafe_mmap_fixed_none : forall addr len mo,
  0 < len -> 0 < addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps mo) ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  nsafe (NMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) mo.
Proof.
  intros addr len mo Hlen Hpos Hal Hce Hrf Hmc. cbn [nsafe node_input].
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold stack_max_size, two_pow_64 in Hroom.
  assert (Hlen2 : len < 2^64).
  { pose proof (page_round_up_Z_mono 0 len ltac:(lia)).
    unfold page_round_up_Z, page_size in *. lia. }
  assert (Haddr : 0 <= addr < 2^64) by (pose proof (page_round_up_Z_nonneg len); lia).
  set (sp := mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_NONE)
                       (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)).
  set (i := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 PROT_NONE; Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED); Z_to_bv 64 (-1); Z_to_bv 64 0]).
  assert (Hl : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (H1 : bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= alloc_top (m_vmmaps mo)) by (rewrite !unsigned_lit by lia; exact Hce).
  assert (H2 : bv_unsigned (Z_to_bv 64 addr) mod page_size = 0) by (rewrite unsigned_lit by lia; exact Hal).
  assert (H3 : 0 < bv_unsigned (Z_to_bv 64 addr)) by (rewrite unsigned_lit by lia; exact Hpos).
  assert (H4 : region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true)
    by (rewrite unsigned_lit by lia; exact Hrf).
  assert (H5 : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true)
    by (rewrite unsigned_lit by lia; exact Hmc).
  pose proof (fun o => mmap_fixed_noaccess_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_NONE)
            (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
            i mo o eq_refl eq_refl Hl eq_refl eq_refl eq_refl H1 H2 H3 H4 H5) as Hout.
  assert (Hsi : forall o, syscall_spec i mo o <-> sp i mo o).
  { intros o. unfold i, sp. rewrite syscall_spec_222 by reflexivity. reflexivity. }
  split.
  - apply (nsafe_of sp); [exact Hsi| |].
    + intros Hu. apply Hout in Hu. destruct Hu as [(e & _ & H) | [H | (e & _ & H)]]; discriminate H.
    + eexists. apply Hout. right; left. reflexivity.
  - intros _. left. eexists _, _, _. split; [apply Hsi; apply Hout; right; left; reflexivity|].
    unfold i. rewrite refusal_b_222. cbn [eff_ret]. apply ret_in_mmap_small.
    rewrite unsigned_lit by lia. pose proof (page_round_up_Z_nonneg len). lia.
Qed.

(* [comment removed for export] *)
Lemma nsafe_munmap_exact : forall addr len mo,
  0 <= addr < 2^64 -> 0 < len < 2^64 -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  nsafe (NMunmap addr len) mo.
Proof.
  intros addr len mo Ha Hlen Hal Hnw Hhas. cbn [nsafe node_input].
  set (sp := munmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len)).
  assert (H1 : bv_unsigned (Z_to_bv 64 addr) mod page_size = 0) by (rewrite unsigned_lit by lia; exact Hal).
  assert (H2 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (H3 : bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= TASK_SIZE)
    by (rewrite !unsigned_lit by lia; lia).
  assert (H4 : map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true)
    by (rewrite unsigned_lit by lia; exact Hhas).
  pose proof (fun o => munmap_exact_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo o
                         H1 H2 H3 H4) as Hout.
  split.
  - apply (nsafe_of sp).
    + intros o. rewrite syscall_spec_215 by reflexivity. reflexivity.
    + intros Hu. apply Hout in Hu. destruct Hu as [(e & _ & Hu) | Hu]; discriminate Hu.
    + eexists. apply Hout. right. reflexivity.
  - intros _. left. eexists _, _, _. split; [apply Hout; right; reflexivity|].
    rewrite refusal_b_215. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nsafe_mprotect_expose : forall addr len mo,
  0 <= addr < 2^64 -> 0 < len < 2^64 -> addr mod page_size = 0 ->
  addr + page_round_up_Z len < 2^64 ->
  map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  nsafe (NMprotect addr len (PROT_READ + PROT_WRITE)) mo.
Proof.
  intros addr len mo Ha Hlen Hal Hnw Hna Hmc Hvd0. cbn [nsafe node_input].
  set (sp := mprotect_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE))).
  set (i := pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 (PROT_READ + PROT_WRITE)]).
  assert (H1 : bv_unsigned (Z_to_bv 64 addr) mod page_size = 0) by (rewrite unsigned_lit by lia; exact Hal).
  assert (H2 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (H3 : bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) < two_pow_64)
    by (rewrite !unsigned_lit by lia; unfold two_pow_64; lia).
  assert (H4 : map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true)
    by (rewrite unsigned_lit by lia; exact Hna).
  assert (H5 : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true)
    by (rewrite unsigned_lit by lia; exact Hmc).
  assert (H6 : region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) = true)
    by (rewrite unsigned_lit by lia; exact Hvd0).
  pose proof (fun o => mprotect_expose_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE))
                         i mo o eq_refl H1 H2 H3 eq_refl H4 H5 H6) as Hout.
  assert (Hsi : forall o, syscall_spec i mo o <-> sp i mo o).
  { intros o. unfold i, sp. rewrite syscall_spec_226 by reflexivity. reflexivity. }
  cbv zeta in Hout.
  split.
  - apply (nsafe_of sp); [exact Hsi| |].
    + intros Hu. apply Hout in Hu. destruct Hu as [(e & _ & H) | (_ & H)]; discriminate H.
    + eexists. apply Hout. left. exists ENOMEM. split; [left; reflexivity|reflexivity].
  - intros _.
    destruct (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))) eqn:E.
    + left. eexists _, _, _. split; [apply Hsi; apply Hout; right; split; reflexivity|].
      unfold i. rewrite refusal_b_226. reflexivity.
    + right. intros eff' m' evs' Hsp. apply Hsi in Hsp. apply Hout in Hsp.
      destruct Hsp as [(e & He & Heq) | (Hb & _)]; [|congruence].
      apply Ok_inj in Heq as (-> & _ & _). unfold i. rewrite refusal_b_226. cbn [eff_ret]. apply ret_in_errnos_in. exact He.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* LPS 727298f3: [mremap_spec] answers -EINVAL for a page-rounded new length above
   TASK_SIZE before it reads the model; a grow with room in place charges the budget
   there (a failing charge leaves only the errno answers), and a grow without room
   moves to the one address [Mmap.linux_place] gives at hint 0 ([mremap_dst_ok]). *)
Lemma mremap_exact_outcome : forall old oldlen newlen i m o,
  let h := m_vmmaps m in
  let onZ := page_round_up_Z (bv_unsigned oldlen) in
  let nnZ := page_round_up_Z (bv_unsigned newlen) in
  let on := Z_to_bv 64 onZ in
  let nn := Z_to_bv 64 nnZ in
  (bv_unsigned old mod page_size = 0)%Z ->
  w_is0 oldlen = false -> w_is0 newlen = false ->
  (bv_unsigned old + onZ <= alloc_top h)%Z -> (nnZ < two_pow_64)%Z ->
  m_vm_lazy m = [] ->
  region_free (vm_reserved h) old on = true ->
  map_has (vm_maps h) old on = true ->
  region_free (vm_noaccess h) old on = true ->
  mremap_spec old oldlen newlen (Z_to_bv 64 MREMAP_MAYMOVE) i m o <->
     ((TASK_SIZE < nnZ)%Z /\ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
  \/ ((nnZ <= TASK_SIZE)%Z /\
     ((onZ = nnZ /\ o = Ok (mkEffect old [] []) m [])
  \/ (onZ <> nnZ /\ exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
  \/ ((nnZ < onZ)%Z
      /\ o = Ok (mkEffectU old [] [] [((old + nn)%bv, Z_to_bv 64 (onZ - nnZ))] [] []) (mremap_model_next m old on old nn) [])
  \/ ((onZ < nnZ)%Z /\ mremap_inplace_grow_b m old on nn onZ nnZ = true
      /\ o = Ok (mkEffect old [] [((old + on)%bv, Z_to_bv 64 (nnZ - onZ))]) (mremap_model_next m old on old nn) [])
  \/ (exists dst, (onZ < nnZ)%Z /\ mremap_inplace_room_b m old on nn onZ nnZ = false
      /\ mremap_dst_ok m onZ nnZ old on dst nn
      /\ o = Ok (mkEffectU dst [] [((dst + on)%bv, Z_to_bv 64 (nnZ - onZ))] [(old, on)] [mkCopy old dst on] [])
               (mremap_model_next m old on dst nn) []))).
Proof.
  intros old oldlen newlen i m o h onZ nnZ on nn Hal Hol Hnl Hce Hnw Hlazy Hrf Hhas Hna.
  pose proof (bv_unsigned_in_range 64 old) as Rold. pose proof (bv_unsigned_in_range 64 oldlen) as Rol.
  pose proof (bv_unsigned_in_range 64 newlen) as Rnl. unfold bv_modulus in Rold, Rol, Rnl.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rold, Rol, Rnl.
  assert (Holpos : (0 < bv_unsigned oldlen)%Z).
  { unfold w_is0, bv_eqb in Hol. apply Z.eqb_neq in Hol. rewrite unsigned_lit in Hol by lia. lia. }
  assert (Hnlpos : (0 < bv_unsigned newlen)%Z).
  { unfold w_is0, bv_eqb in Hnl. apply Z.eqb_neq in Hnl. rewrite unsigned_lit in Hnl by lia. lia. }
  assert (Hon1 : (bv_unsigned oldlen <= onZ)%Z).
  { subst onZ. unfold page_round_up_Z, page_size. nia. }
  assert (Hnn1 : (bv_unsigned newlen <= nnZ)%Z).
  { subst nnZ. unfold page_round_up_Z, page_size. nia. }
  assert (Honw : (onZ < two_pow_64)%Z).
  { pose proof (alloc_top_lt h). lia. }
  assert (EnnZ : nnZ = page_round_up_Z (bv_unsigned newlen)) by reflexivity.
  assert (Hg1 : negb (bv_unsigned (Z_to_bv 64 MREMAP_MAYMOVE) =? MREMAP_MAYMOVE)%Z = false) by reflexivity.
  assert (Hg2 : negb (bv_unsigned old mod page_size =? 0)%Z = false) by (rewrite Hal; reflexivity).
  assert (Hg3 : page_align_is0_b newlen = false).
  { unfold page_align_is0_b. rewrite Hnl. cbn [orb]. apply Z.leb_gt. exact Hnw. }
  assert (Hg4 : page_align_is0_b oldlen = false).
  { unfold page_align_is0_b. rewrite Hol. cbn [orb]. apply Z.leb_gt. exact Honw. }
  assert (Hg5 : negb (mremap_source_b (m_vmmaps m) old on onZ && mremap_backing_uniform_b m old on) = false).
  { unfold mremap_source_b. fold h. rewrite (proj2 (Z.leb_le _ _) Hce), Hrf, Hhas, Hna.
    unfold mremap_backing_uniform_b. rewrite Hlazy. reflexivity. }
  unfold mremap_spec. rewrite Hg1, Hg2, Hg3.
  destruct (Z.ltb_spec TASK_SIZE (page_round_up_Z (bv_unsigned newlen))) as [Hbig|Hsmall].
  { (* the new length leaves the user address space: -EINVAL, whatever the model *)
    cbv beta iota. sys_unfold. split.
    - intros H. left. split; [lia|]. destruct o; inv_sys. reflexivity.
    - intros [[_ ->] | [Hs _]]; [reflexivity | lia]. }
  assert (HR : forall P Q : Prop, ((TASK_SIZE < nnZ)%Z /\ P) \/ ((nnZ <= TASK_SIZE)%Z /\ Q) <-> Q).
  { intros P Q. split; [intros [[Hc _]|[_ Hq]]; [lia | exact Hq] | intros Hq; right; split; [lia | exact Hq]]. }
  rewrite HR. clear HR.
  rewrite Hg4. cbv beta iota. rewrite bind_model. cbv beta zeta.
  fold onZ nnZ. fold on nn. rewrite Hg5. cbv beta iota.
  unfold mremap_inplace_effect, mremap_move_effect, mremap_tail.
  destruct (Z.eqb_spec onZ nnZ) as [Heq|Hne].
  { (* [comment removed for export] *)
    sys_unfold. split.
    - intros H. left. split; [exact Heq|]. destruct o; inv_sys. reflexivity.
    - intros [[_ ->] | [[Hc _] | [[Hc _] | [[Hc _] | (dst & Hc & _)]]]]; try lia. reflexivity. }
  sys_unfold. split.
  - intros H. right. destruct o as [x m' evs|]; inv_sys.
    + left. split; [exact Hne|]. eexists. split; [eassumption|reflexivity].
    + destruct (Z.ltb_spec nnZ onZ) as [Hlt|Hge].
      * inv_sys. right; left. split; [exact Hlt|]. try replace (onZ <? nnZ)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * assert (Hlt : (onZ < nnZ)%Z) by lia. try replace (onZ <? nnZ)%Z with true in * by (symmetry; apply Z.ltb_lt; lia).
        destruct (mremap_inplace_room_b m old on nn onZ nnZ) eqn:Er; inv_sys.
        -- right; right; left. split; [exact Hlt|]. split; [|reflexivity].
           unfold mremap_inplace_grow_b. rewrite Er. cbn [andb]. assumption.
        -- right; right; right. eexists. split; [exact Hlt|]. split; [first [reflexivity | exact Er]|].
           split; [eassumption|reflexivity].
    + exfalso. repeat first [ progress inv_sys
                            | match goal with
                              | H : (if ?b then _ else _) _ _ _ |- _ => destruct b
                              | H : (if ?b then _ else _) |- _ => destruct b
                              end ].
  - intros [[Hc _] | [(_ & e & He & ->) | [[Hlt ->] | [(Hlt & Hg & ->) | (dst & Hlt & Hroom & Hdst & ->)]]]]; [lia| | | |].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. replace (nnZ <? onZ)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + right. replace (nnZ <? onZ)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      try replace (onZ <? nnZ)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      unfold mremap_inplace_grow_b in Hg. apply andb_prop in Hg as [Hroom Hbud]. rewrite Hroom.
      eexists _, _, _, _. split; [exists tt; split; [exact Hbud|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + right. replace (nnZ <? onZ)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      try replace (onZ <? nnZ)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Hroom.
      eexists _, _, _, _. split; [exists dst; split; [exact Hdst|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma maps_subtract_app : forall l1 l2 lo hi,
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] r IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma maps_subtract_all_app : forall cuts l1 l2,
  maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof.
  induction cuts as [|[a n] r IH]; intros l1 l2; [reflexivity|].
  cbn [maps_subtract_all]. rewrite maps_subtract_app. apply IH.
Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = (live_bytes l1 + live_bytes l2)%Z.
Proof. induction l1 as [|[a sz] r IH]; intros l2; cbn [live_bytes app]; [reflexivity| rewrite IH; lia]. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_miss : forall (a sz : word) lo hi,
  (0 < bv_unsigned sz)%Z -> (lo <= hi)%Z ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a)%Z ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a)%Z with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_all_miss : forall cuts (d nn : word),
  (0 < bv_unsigned nn)%Z ->
  region_free cuts d nn = true ->
  maps_subtract_all [(d, nn)] cuts = [(d, nn)].
Proof.
  induction cuts as [|[a n] r IH]; intros d nn Hnn Hrf; [reflexivity|].
  cbn [region_free] in Hrf. apply andb_true_iff in Hrf as [Hov Hrf]. apply negb_true_iff in Hov.
  cbn [maps_subtract_all maps_subtract]. rewrite app_nil_r.
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  rewrite iv_subtract_miss; [apply IH; assumption|exact Hnn|lia|].
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

(* [comment removed for export] *)
Lemma nsafe_mremap : forall old oldlen newlen mo,
  0 <= old -> old mod page_size = 0 -> 0 < oldlen -> 0 < newlen ->
  old + page_round_up_Z oldlen <= alloc_top (m_vmmaps mo) ->
  page_round_up_Z newlen < 2^64 ->
  lazyfree mo ->
  let h := m_vmmaps mo in
  let old_n := Z_to_bv 64 (page_round_up_Z oldlen) in
  region_free (vm_reserved h) (Z_to_bv 64 old) old_n = true ->
  map_has (vm_maps h) (Z_to_bv 64 old) old_n = true ->
  region_free (vm_noaccess h) (Z_to_bv 64 old) old_n = true ->
  (forall d, region_free (vm_reserved h ++ vm_maps h) d (Z_to_bv 64 (page_round_up_Z newlen)) = true ->
             region_free (vm_noaccess h) d (Z_to_bv 64 (page_round_up_Z newlen)) = true) ->
  nsafe (NMremap old oldlen newlen) mo.
Proof.
  intros old oldlen newlen mo Ho Hal Hol Hnl Hce Hnw Hlf h old_n Hrf Hhas Hna Hfresh. cbn [nsafe node_input].
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold stack_max_size, two_pow_64 in Hroom. fold h in Hroom, Hce.
  pose proof (page_round_up_Z_pos oldlen Hol) as Hon4. pose proof (page_round_up_Z_pos newlen Hnl) as Hnn4.
  assert (Hold : old < 2^64) by lia.
  assert (Holr : oldlen < 2^64).
  { pose proof (page_round_up_Z_mono 0 oldlen ltac:(lia)). unfold page_round_up_Z, page_size in *. lia. }
  assert (Hnlr : newlen < 2^64) by (unfold page_round_up_Z, page_size in Hnw; lia).
  set (ow := Z_to_bv 64 old). set (olw := Z_to_bv 64 oldlen). set (nlw := Z_to_bv 64 newlen).
  set (i := pure_input 216 [ow; olw; nlw; Z_to_bv 64 MREMAP_MAYMOVE; Z_to_bv 64 0]).
  set (sp := mremap_spec ow olw nlw (Z_to_bv 64 MREMAP_MAYMOVE)).
  assert (Hsi : forall o, syscall_spec i mo o <-> sp i mo o).
  { intros o. unfold i, sp. rewrite syscall_spec_216 by reflexivity. reflexivity. }
  pose proof (mremap_exact_outcome ow olw nlw i mo) as Hout. cbv zeta in Hout.
  unfold ow, olw, nlw in Hout. rewrite !unsigned_lit in Hout by lia. fold ow olw nlw in Hout.
  set (onZ := page_round_up_Z oldlen) in *. set (nnZ := page_round_up_Z newlen) in *.
  set (on := Z_to_bv 64 onZ) in *. set (nn := Z_to_bv 64 nnZ) in *.
  assert (Hg : forall o, sp i mo o <-> _) by
    (intros o; apply (Hout o); [exact Hal| unfold olw; rewrite w_is0_lit by lia; apply Z.eqb_neq; lia
                               | unfold nlw; rewrite w_is0_lit by lia; apply Z.eqb_neq; lia
                               | exact Hce | unfold two_pow_64; exact Hnw | exact (proj1 Hlf) | exact Hrf | exact Hhas | exact Hna]).
  clear Hout.
  assert (Hnr_addr : forall a : word, bv_unsigned a + 0 <= alloc_top h -> ret_in_errnos mremap_errnos a = false).
  { intros a Ha. apply ret_in_mremap_small. lia. }
  assert (Hunn : bv_unsigned nn = nnZ) by (unfold nn; apply unsigned_lit; lia).
  assert (Hn0 : 0 < nnZ) by lia.
  assert (Hnal : nnZ mod page_size = 0) by (unfold nnZ; apply page_round_up_Z_aligned).
  assert (Hinval : ret_in_errnos mremap_errnos (errno_ret EINVAL) = false) by (first [reflexivity | vm_compute; reflexivity]).
  split.
  - apply (nsafe_of sp); [exact Hsi| |].
    + intros Hu. apply Hg in Hu.
      destruct Hu as [[_ H] | [_ [[_ H] | [(_ & e & _ & H) | [[_ H] | [(_ & _ & H) | (dst & _ & _ & _ & H)]]]]]]; discriminate H.
    + destruct (Z_lt_le_dec TASK_SIZE nnZ) as [Hbig|Hsmall].
      * eexists. apply Hg. left. split; [exact Hbig|reflexivity].
      * destruct (Z.eq_dec onZ nnZ) as [E|E].
        -- eexists. apply Hg. right. split; [exact Hsmall|]. left. split; [exact E|reflexivity].
        -- eexists. apply Hg. right. split; [exact Hsmall|]. right; left. split; [exact E|].
           exists ENOMEM. split; [left; reflexivity|reflexivity].
  - intros _.
    assert (Hleft : forall eff m' , sp i mo (Ok eff m' []) -> ret_in_errnos mremap_errnos (eff_ret eff) = false ->
              (exists eff' m1 evs', syscall_spec i mo (Ok eff' m1 evs') /\ refusal_b i mo (eff_ret eff') = false)
              \/ (forall eff' m1 evs', syscall_spec i mo (Ok eff' m1 evs') -> refusal_b i mo (eff_ret eff') = true)).
    { intros eff m' Hs Hr. left. exists eff, m', []. split; [apply Hsi; exact Hs|]. unfold i. rewrite refusal_b_216. exact Hr. }
    assert (How : bv_unsigned ow + 0 <= alloc_top h) by (unfold ow; rewrite unsigned_lit by lia; lia).
    destruct (Z_lt_le_dec TASK_SIZE nnZ) as [Hbig|Hsmall].
    { (* -EINVAL is not one of the injected answers *)
      eapply Hleft; [apply Hg; left; split; [exact Hbig|reflexivity]|]. cbn [eff_ret]. exact Hinval. }
    destruct (Z.eq_dec onZ nnZ) as [E|E].
    { eapply Hleft; [apply Hg; right; split; [exact Hsmall|]; left; split; [exact E|reflexivity]|]. cbn [eff_ret]. exact (Hnr_addr ow How). }
    destruct (Z.ltb_spec nnZ onZ) as [Hlt|Hge].
    { eapply Hleft; [apply Hg; right; split; [exact Hsmall|]; right; right; left; split; [exact Hlt|reflexivity]|]. cbn [eff_ret]. exact (Hnr_addr ow How). }
    assert (Hgt : onZ < nnZ) by lia.
    destruct (mremap_inplace_grow_b mo ow on nn onZ nnZ) eqn:Eg.
    { eapply Hleft; [apply Hg; right; split; [exact Hsmall|]; right; right; right; left; split; [exact Hgt|split; [first [exact Eg | reflexivity]|reflexivity]]|].
      cbn [eff_ret]. exact (Hnr_addr ow How). }
    (* A grow with room in place but no budget has only the errno answers. *)
    destruct (mremap_inplace_room_b mo ow on nn onZ nnZ) eqn:Er.
    { right. intros eff' m1 evs' Hsp. apply Hsi, Hg in Hsp. unfold i. rewrite refusal_b_216.
      destruct Hsp as [[Hc _] | [_ Hsp]]; [lia|].
      destruct Hsp as [[Hc _] | [(_ & e & He & Heq) | [[Hc _] | [(_ & Hc & _) | (dst & _ & Hc & _)]]]]; try lia; try congruence.
      apply Ok_inj in Heq as (-> & _ & _). cbn [eff_ret]. apply ret_in_errnos_in. exact He. }
    (* Without room the move goes to Linux's one placement at hint 0. *)
    destruct (Placement.linux_place_b_spec h (kb_thp (m_kernel mo)) (Z_to_bv 64 0) nnZ Hn0 Hnal) as [Hsome Hnone].
    destruct (Placement.linux_place_b h (kb_thp (m_kernel mo)) (Z_to_bv 64 0) nnZ) as [aZ|] eqn:Ep.
    2:{ right. intros eff' m1 evs' Hsp. apply Hsi, Hg in Hsp. unfold i. rewrite refusal_b_216.
        destruct Hsp as [[Hc _] | [_ Hsp]]; [lia|].
        destruct Hsp as [[Hc _] | [(_ & e & He & Heq) | [[Hc _] | [(_ & Hc & _) | (dst & _ & _ & (Hpl & _) & _)]]]]; try lia; try congruence.
        - apply Ok_inj in Heq as (-> & _ & _). cbn [eff_ret]. apply ret_in_errnos_in. exact He.
        - exfalso. exact (proj1 Hnone eq_refl _ Hpl). }
    destruct (place_word_of _ _ _ _ _ Hn0 Hnal (proj1 (Hsome aZ) eq_refl)) as (dw & _ & Hpl).
    destruct (Placement.linux_place_admissible _ _ _ _ _ Hn0 Hnal Hpl) as (A1 & A2 & A3 & A4).
    rewrite Z_to_bv_bv_unsigned in A4. fold nn in A4.
    destruct (mremap_final_budget_b mo ow on dw nn) eqn:Eb.
    + (* [comment removed for export] *)
      assert (Hne : bv_eqb dw ow = false).
      { destruct (bv_eqb dw ow) eqn:E1; [|reflexivity]. exfalso. apply bv_eqb_eq in E1.
        unfold map_has in Hhas. apply existsb_exists in Hhas as ([b sz] & Hin & Hb). cbn [fst snd] in Hb.
        apply andb_true_iff in Hb as [Hb1 Hb2]. apply bv_eqb_eq in Hb1. apply bv_eqb_eq in Hb2. subst b sz.
        pose proof (region_free_In _ _ _ _ _ A4 (in_or_app _ _ _ (or_intror Hin))) as Hno. fold ow in Hno.
        assert (Huon : bv_unsigned on = onZ) by (unfold on; apply unsigned_lit; lia).
        unfold iv_overlap in Hno. rewrite E1 in Hno. fold nn in Hno. unfold old_n in Hno. rewrite Hunn, Huon in Hno.
        apply andb_false_iff in Hno as [Hno|Hno]; apply Z.ltb_ge in Hno; lia. }
      eapply Hleft.
      * apply Hg. right. split; [exact Hsmall|]. right; right; right; right. exists dw. split; [exact Hgt|].
        split; [first [exact Er | reflexivity]|]. split; [|reflexivity]. split; [exact Hpl|].
        unfold mremap_fresh_b. cbv zeta. fold h. rewrite Hne, (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3), A4, Eb. reflexivity.
      * cbn [eff_ret]. apply Hnr_addr. lia.
    + (* [comment removed for export] *)
      right. intros eff' m1 evs' Hsp. apply Hsi, Hg in Hsp. unfold i. rewrite refusal_b_216.
      destruct Hsp as [[Hc _] | [_ Hsp]]; [lia|].
      destruct Hsp as [[Hc _] | [(_ & e & He & Heq) | [[Hc _] | [(_ & Hc & _) | (dst & _ & _ & (Hpl' & Hfr) & _)]]]]; try lia; try congruence.
      * apply Ok_inj in Heq as (-> & _ & _). cbn [eff_ret]. apply ret_in_errnos_in. exact He.
      * exfalso. pose proof (Placement.linux_place_unique _ _ _ _ _ _ Hpl Hpl') as Eu.
        assert (dst = dw) by (apply bv_eq; symmetry; exact Eu). subst dst.
        unfold mremap_fresh_b in Hfr. cbv zeta in Hfr. apply andb_true_iff in Hfr as [_ Hfr]. congruence.
Qed.
