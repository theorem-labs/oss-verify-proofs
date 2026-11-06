(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import AsanCeil PropExec AgentLib PureModel AllocSim MmapSim RefNodes AllocRefusal.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_mmap (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_noacc (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_munmap (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
               (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_fixed_ok (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
               ((a, n) :: maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_fixed_destroy (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_unprotect (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
               (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
(* [comment removed for export] *)
Definition vm_brk_grow (req : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((vm_brk h, (req - vm_brk h)%bv) :: vm_maps h) (vm_noaccess h)
               (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grant_ok_vm (h : VmMaps) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n)
  && (vm_backed_bytes h + n <=? vm_limit h)%Z.

(* [comment removed for export] *)
Definition grant_ok_na_vm (h : VmMaps) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n).

(* [comment removed for export] *)
Definition brk_grow_ok_vm (h : VmMaps) (req r : word) : bool :=
  if Z.ltb 0 (bv_unsigned (vm_brk h))
     && Z.ltb (bv_unsigned (vm_brk h)) (bv_unsigned r)
  then let lo := page_round_up_Z (bv_unsigned (vm_brk h)) in
       let hi := page_round_up_Z (bv_unsigned r) in
       (if Z.ltb lo hi
        then Z.leb hi (alloc_top h)
             && region_free (vm_reserved h ++ vm_maps h)
                            (Z_to_bv 64 lo) (Z_to_bv 64 (hi + page_size - lo))
        else true)
       && Z.leb (vm_backed_bytes h + bv_unsigned (r - vm_brk h)) (vm_limit h)
  else true.

(* [comment removed for export] *)
Definition mprot_ok_vm (h : VmMaps) (addr n : word) : bool :=
  (vm_backed_bytes (vm_unprotect addr n h) <=? vm_limit h)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_refusable_vm (h : VmMaps) (n : Z) : bool :=
  negb (vm_backed_bytes h + n <=? vm_limit h)%Z || negb (vm_gap_available h n).
Definition mmap_na_refusable_vm (h : VmMaps) (n : Z) : bool :=
  negb (vm_gap_available h n).
Definition mprot_refusable_vm (h : VmMaps) (addr n : word) : bool :=
  negb (mprot_ok_vm h addr n).

Lemma vm_gap_available_na_iff : forall h n,
  vm_gap_available h n = true <-> exists a, grant_ok_na_vm h a n = true.
Proof.
  intros h n. rewrite vm_gap_available_iff. split.
  - intros (a & H1 & H2 & H3 & H4). exists a. unfold grant_ok_na_vm.
    rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4. reflexivity.
  - intros [a Ha]. exists a. unfold grant_ok_na_vm in Ha. rewrite !andb_true_iff in Ha.
    destruct Ha as [[[H1 H2] H3] H4].
    apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. repeat split; assumption.
Qed.

Lemma mmap_na_refusable_vm_false_iff : forall h n,
  mmap_na_refusable_vm h n = false <-> exists a, grant_ok_na_vm h a n = true.
Proof.
  intros h n. unfold mmap_na_refusable_vm. rewrite negb_false_iff. apply vm_gap_available_na_iff.
Qed.

Lemma mmap_na_refusable_vm_iff : forall h n,
  mmap_na_refusable_vm h n = true <-> forall a, grant_ok_na_vm h a n = false.
Proof.
  intros h n. split.
  - intros H a. destruct (grant_ok_na_vm h a n) eqn:E; [|reflexivity].
    assert (Hf : mmap_na_refusable_vm h n = false) by (apply mmap_na_refusable_vm_false_iff; exists a; exact E).
    rewrite Hf in H. discriminate.
  - intros H. destruct (mmap_na_refusable_vm h n) eqn:E; [reflexivity|].
    apply mmap_na_refusable_vm_false_iff in E as [a Ha]. rewrite H in Ha. discriminate.
Qed.

Lemma mmap_refusable_vm_false_iff : forall h n,
  mmap_refusable_vm h n = false <-> exists a, grant_ok_vm h a n = true.
Proof.
  intros h n. unfold mmap_refusable_vm. rewrite orb_false_iff, !negb_false_iff, vm_gap_available_na_iff. split.
  - intros [Hb [a Ha]]. exists a. unfold grant_ok_vm. unfold grant_ok_na_vm in Ha. rewrite Ha, Hb. reflexivity.
  - intros [a Ha]. unfold grant_ok_vm in Ha. apply andb_true_iff in Ha as [Ha Hb].
    split; [exact Hb | exists a; exact Ha].
Qed.

Lemma mmap_refusable_vm_iff : forall h n,
  mmap_refusable_vm h n = true <-> forall a, grant_ok_vm h a n = false.
Proof.
  intros h n. split.
  - intros H a. destruct (grant_ok_vm h a n) eqn:E; [|reflexivity].
    assert (Hf : mmap_refusable_vm h n = false) by (apply mmap_refusable_vm_false_iff; exists a; exact E).
    rewrite Hf in H. discriminate.
  - intros H. destruct (mmap_refusable_vm h n) eqn:E; [reflexivity|].
    apply mmap_refusable_vm_false_iff in E as [a Ha]. rewrite H in Ha. discriminate.
Qed.

Lemma mprot_refusable_vm_iff : forall h addr n,
  mprot_refusable_vm h addr n = true <-> mprot_ok_vm h addr n = false.
Proof. intros h addr n. unfold mprot_refusable_vm. apply negb_true_iff. Qed.

Lemma mprot_refusable_vm_false_iff : forall h addr n,
  mprot_refusable_vm h addr n = false <-> mprot_ok_vm h addr n = true.
Proof. intros h addr n. unfold mprot_refusable_vm. apply negb_false_iff. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vm_backing_used_pure : forall md,
  md_pure md -> vm_backing_used md = vm_backed_bytes (m_vmmaps md).
Proof. intros md [_ Hl Hm]. apply vm_backing_used_simple; assumption. Qed.

Lemma with_vm_backing_pure : forall md,
  md_pure md -> with_vm_backing [] [] md = md.
Proof.
  intros md [_ Hl Hm]. destruct md as [? [? l mt] ? ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_pure : forall lo hi md,
  md_pure md -> vm_forget_range lo hi md = md.
Proof. intros lo hi md [_ Hl Hm]. apply vm_forget_range_id; assumption. Qed.

(* [comment removed for export] *)
Lemma md_pure_vmmaps : forall h md, md_pure md -> md_pure (with_vmmaps h md).
Proof. exact md_pure_with_vmmaps. Qed.

Lemma with_vmmaps_vmmaps : forall h md, m_vmmaps (with_vmmaps h md) = h.
Proof. reflexivity. Qed.
Lemma with_vmmaps_twice : forall h h' md, with_vmmaps h (with_vmmaps h' md) = with_vmmaps h md.
Proof. reflexivity. Qed.
Lemma with_vmmaps_same : forall md, with_vmmaps (m_vmmaps md) md = md.
Proof. exact with_vmmaps_eta. Qed.

(* [comment removed for export] *)
Lemma grant_ok_pure : forall hint md a n,
  md_pure md -> grant_ok hint md a n = grant_ok_vm (m_vmmaps md) a n.
Proof.
  intros hint md a n Hp. unfold grant_ok, grant_ok_vm.
  rewrite (vm_backing_used_pure md Hp). reflexivity.
Qed.

Lemma grant_ok_na_pin_vm : forall md a n,
  grant_ok_na_pin md a n = grant_ok_na_vm (m_vmmaps md) a n.
Proof. reflexivity. Qed.

Lemma grant_ok_vm_na : forall h a n,
  grant_ok_vm h a n = true -> grant_ok_na_vm h a n = true.
Proof.
  intros h a n H. unfold grant_ok_vm in H. unfold grant_ok_na_vm.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma brk_grow_ok_pure : forall md req r,
  md_pure md -> Mmap.brk_grow_ok md req r = brk_grow_ok_vm (m_vmmaps md) req r.
Proof.
  intros md req r Hp. unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok, brk_grow_ok_vm.
  rewrite (vm_backing_used_pure md Hp). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_allocsim : forall h req r,
  AllocSim.brk_grow_ok h req r = brk_grow_ok_vm h req r.
Proof.
  intros h req r. unfold AllocSim.brk_grow_ok.
  rewrite (brk_grow_ok_pure (vm_model h) req r) by (constructor; reflexivity). reflexivity.
Qed.

Lemma mprotect_budget_ok_pure : forall md addr n,
  md_pure md -> mprotect_budget_ok md addr n = mprot_ok_vm (m_vmmaps md) addr n.
Proof.
  intros md addr n Hp. unfold mprotect_budget_ok, vm_backing_within_limit, mprot_ok_vm.
  rewrite (vm_backing_used_pure (mprotect_model_next md addr n))
    by (unfold mprotect_model_next; apply md_pure_with_vmmaps; exact Hp).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_refusable_pure : forall md n,
  md_pure md -> mmap_refusable md n = mmap_refusable_vm (m_vmmaps md) n.
Proof.
  intros md n Hp. rewrite mmap_refusable_unfold. unfold mmap_refusable_vm.
  rewrite (vm_backing_used_pure md Hp). reflexivity.
Qed.

Lemma mmap_reserve_refusable_vm : forall md n,
  mmap_reserve_refusable md n = mmap_na_refusable_vm (m_vmmaps md) n.
Proof. reflexivity. Qed.

Lemma mprotect_refusable_pure : forall md addr n,
  md_pure md -> mprotect_refusable md addr n = mprot_refusable_vm (m_vmmaps md) addr n.
Proof.
  intros md addr n Hp. unfold mprotect_refusable, mprot_refusable_vm.
  rewrite (mprotect_budget_ok_pure md addr n Hp). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_model_vm : forall a n md,
  mmap_model a n md = with_vmmaps (vm_mmap a n (m_vmmaps md)) md.
Proof. reflexivity. Qed.

Lemma noaccess_model_vm : forall a n md,
  noaccess_model a n md = with_vmmaps (vm_noacc a n (m_vmmaps md)) md.
Proof. reflexivity. Qed.

Lemma mprotect_model_vm : forall a n md,
  mprotect_model a n md = with_vmmaps (vm_unprotect a n (m_vmmaps md)) md.
Proof. reflexivity. Qed.

Lemma mprotect_model_next_vm : forall a n md,
  mprotect_model_next md a n = with_vmmaps (vm_unprotect a n (m_vmmaps md)) md.
Proof. reflexivity. Qed.

Lemma munmap_model_pure : forall a n md,
  md_pure md -> munmap_model a n md = with_vmmaps (vm_munmap a n (m_vmmaps md)) md.
Proof. intros a n md [_ Hl Hm]. apply munmap_model_simple; assumption. Qed.

Lemma fixed_noaccess_model_pure : forall a n md,
  md_pure md -> fixed_noaccess_model a n md = with_vmmaps (vm_fixed_ok a n (m_vmmaps md)) md.
Proof. intros a n md [_ Hl Hm]. apply fixed_noaccess_model_simple; assumption. Qed.

Lemma fixed_destroyed_model_pure : forall a n md,
  md_pure md -> fixed_destroyed_model a n md = with_vmmaps (vm_fixed_destroy a n (m_vmmaps md)) md.
Proof. intros a n md [_ Hl Hm]. apply fixed_destroyed_model_simple; assumption. Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_vm : forall md req,
  let h := m_vmmaps md in
  (0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned req)%Z ->
  brk_model req req md = with_vmmaps (vm_brk_grow req h) md.
Proof.
  intros md req h Hb0 Hlt.
  pose proof (u64_range req) as Hr.
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. rewrite E in Hlt. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hlt.
    pose proof (u64_range (vm_brk h)). lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h.
  rewrite (brk_unmaps_grow req (vm_brk h)) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_brk h)))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req (vm_brk h) Hreq0 Hb0 Hlt), (brk_unmaps_grow req (vm_brk h)) by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep_vm : forall md req, brk_model req (vm_brk (m_vmmaps md)) md = md.
Proof. exact brk_model_keep. Qed.

(* [comment removed for export] *)
Lemma grant_ok_vm_unpack : forall h a n,
  grant_ok_vm h a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true
  /\ (vm_backed_bytes h + n <= vm_limit h)%Z.
Proof.
  intros h a n H. unfold grant_ok_vm in H.
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H5.
  repeat split; assumption.
Qed.

Lemma grant_ok_na_vm_unpack : forall h a n,
  grant_ok_na_vm h a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true.
Proof.
  intros h a n H. unfold grant_ok_na_vm in H.
  apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_vm_top : forall h a n,
  grant_ok_vm h a n = true -> (bv_unsigned a + n <= alloc_top h)%Z.
Proof. intros h a n H. apply grant_ok_vm_unpack in H. tauto. Qed.

Lemma grant_ok_na_vm_top : forall h a n,
  grant_ok_na_vm h a n = true -> (bv_unsigned a + n <= alloc_top h)%Z.
Proof. intros h a n H. apply grant_ok_na_vm_unpack in H. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma vm_mmap_reserved : forall a n h, vm_reserved (vm_mmap a n h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_mmap_limit : forall a n h, vm_limit (vm_mmap a n h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_mmap_init_sp : forall a n h, vm_init_sp (vm_mmap a n h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_mmap_start_brk : forall a n h, vm_start_brk (vm_mmap a n h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_mmap_mmap_base : forall a n h, vm_mmap_base (vm_mmap a n h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_mmap_alloc_top : forall a n h, alloc_top (vm_mmap a n h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_mmap_brk : forall a n h, vm_brk (vm_mmap a n h) = vm_brk h.
Proof. reflexivity. Qed.
Lemma vm_mmap_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_mmap a n h).
Proof. intros. exact H. Qed.
Lemma vm_noacc_reserved : forall a n h, vm_reserved (vm_noacc a n h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_noacc_limit : forall a n h, vm_limit (vm_noacc a n h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_noacc_init_sp : forall a n h, vm_init_sp (vm_noacc a n h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_noacc_start_brk : forall a n h, vm_start_brk (vm_noacc a n h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_noacc_mmap_base : forall a n h, vm_mmap_base (vm_noacc a n h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_noacc_alloc_top : forall a n h, alloc_top (vm_noacc a n h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_noacc_brk : forall a n h, vm_brk (vm_noacc a n h) = vm_brk h.
Proof. reflexivity. Qed.
Lemma vm_noacc_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_noacc a n h).
Proof. intros. exact H. Qed.
Lemma vm_munmap_reserved : forall a n h, vm_reserved (vm_munmap a n h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_munmap_limit : forall a n h, vm_limit (vm_munmap a n h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_munmap_init_sp : forall a n h, vm_init_sp (vm_munmap a n h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_munmap_start_brk : forall a n h, vm_start_brk (vm_munmap a n h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_munmap_mmap_base : forall a n h, vm_mmap_base (vm_munmap a n h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_munmap_alloc_top : forall a n h, alloc_top (vm_munmap a n h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_munmap_brk : forall a n h, vm_brk (vm_munmap a n h) = vm_brk h.
Proof. reflexivity. Qed.
Lemma vm_munmap_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_munmap a n h).
Proof. intros. exact H. Qed.
Lemma vm_fixed_ok_reserved : forall a n h, vm_reserved (vm_fixed_ok a n h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_limit : forall a n h, vm_limit (vm_fixed_ok a n h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_init_sp : forall a n h, vm_init_sp (vm_fixed_ok a n h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_start_brk : forall a n h, vm_start_brk (vm_fixed_ok a n h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_mmap_base : forall a n h, vm_mmap_base (vm_fixed_ok a n h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_alloc_top : forall a n h, alloc_top (vm_fixed_ok a n h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_brk : forall a n h, vm_brk (vm_fixed_ok a n h) = vm_brk h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_fixed_ok a n h).
Proof. intros. exact H. Qed.
Lemma vm_fixed_destroy_reserved : forall a n h, vm_reserved (vm_fixed_destroy a n h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_limit : forall a n h, vm_limit (vm_fixed_destroy a n h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_init_sp : forall a n h, vm_init_sp (vm_fixed_destroy a n h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_start_brk : forall a n h, vm_start_brk (vm_fixed_destroy a n h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_mmap_base : forall a n h, vm_mmap_base (vm_fixed_destroy a n h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_alloc_top : forall a n h, alloc_top (vm_fixed_destroy a n h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_brk : forall a n h, vm_brk (vm_fixed_destroy a n h) = vm_brk h.
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_fixed_destroy a n h).
Proof. intros. exact H. Qed.
Lemma vm_unprotect_reserved : forall a n h, vm_reserved (vm_unprotect a n h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_limit : forall a n h, vm_limit (vm_unprotect a n h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_init_sp : forall a n h, vm_init_sp (vm_unprotect a n h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_start_brk : forall a n h, vm_start_brk (vm_unprotect a n h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_mmap_base : forall a n h, vm_mmap_base (vm_unprotect a n h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_alloc_top : forall a n h, alloc_top (vm_unprotect a n h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_brk : forall a n h, vm_brk (vm_unprotect a n h) = vm_brk h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_init_sp_ok : forall a n h, init_sp_ok h -> init_sp_ok (vm_unprotect a n h).
Proof. intros. exact H. Qed.
Lemma vm_brk_grow_reserved : forall req h, vm_reserved (vm_brk_grow req h) = vm_reserved h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_limit : forall req h, vm_limit (vm_brk_grow req h) = vm_limit h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_init_sp : forall req h, vm_init_sp (vm_brk_grow req h) = vm_init_sp h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_start_brk : forall req h, vm_start_brk (vm_brk_grow req h) = vm_start_brk h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_mmap_base : forall req h, vm_mmap_base (vm_brk_grow req h) = vm_mmap_base h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_alloc_top : forall req h, alloc_top (vm_brk_grow req h) = alloc_top h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_init_sp_ok : forall req h, init_sp_ok h -> init_sp_ok (vm_brk_grow req h).
Proof. intros. exact H. Qed.
Lemma vm_brk_grow_brk : forall req h, vm_brk (vm_brk_grow req h) = req.
Proof. reflexivity. Qed.
Lemma vm_mmap_maps : forall a n h, vm_maps (vm_mmap a n h) = (a, n) :: vm_maps h.
Proof. reflexivity. Qed.
Lemma vm_mmap_noaccess : forall a n h, vm_noaccess (vm_mmap a n h) = vm_noaccess h.
Proof. reflexivity. Qed.
Lemma vm_noacc_maps : forall a n h, vm_maps (vm_noacc a n h) = (a, n) :: vm_maps h.
Proof. reflexivity. Qed.
Lemma vm_noacc_noaccess : forall a n h, vm_noaccess (vm_noacc a n h) = (a, n) :: vm_noaccess h.
Proof. reflexivity. Qed.
Lemma vm_munmap_maps : forall a n h, vm_maps (vm_munmap a n h) = map_remove (vm_maps h) a.
Proof. reflexivity. Qed.
Lemma vm_munmap_noaccess : forall a n h,
  vm_noaccess (vm_munmap a n h) = maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_maps : forall a n h, vm_maps (vm_fixed_ok a n h) = vm_maps h.
Proof. reflexivity. Qed.
Lemma vm_fixed_ok_noaccess : forall a n h,
  vm_noaccess (vm_fixed_ok a n h) = (a, n) :: maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_maps : forall a n h,
  vm_maps (vm_fixed_destroy a n h) = maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma vm_fixed_destroy_noaccess : forall a n h,
  vm_noaccess (vm_fixed_destroy a n h) = maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma vm_unprotect_maps : forall a n h, vm_maps (vm_unprotect a n h) = vm_maps h.
Proof. reflexivity. Qed.
Lemma vm_unprotect_noaccess : forall a n h,
  vm_noaccess (vm_unprotect a n h) = maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma vm_brk_grow_maps : forall req h, vm_maps (vm_brk_grow req h) = (vm_brk h, (req - vm_brk h)%bv) :: vm_maps h.
Proof. reflexivity. Qed.
Lemma vm_brk_grow_noaccess : forall req h, vm_noaccess (vm_brk_grow req h) = vm_noaccess h.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition init_sp_win (h : VmMaps) : Prop :=
  (sp_window_lo <= bv_unsigned (vm_init_sp h) <= sp_window_hi)%Z.

Lemma init_sp_win_ok : forall h, init_sp_win h -> init_sp_ok h.
Proof. intros h [H _]. exact H. Qed.

Lemma init_sp_win_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_win (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & Hhi & _). unfold init_sp_win. cbn. split; [exact Hlo | exact Hhi]. Qed.

Lemma init_sp_win_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_win h -> init_sp_win h'.
Proof. intros h h' E H. unfold init_sp_win in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)
Lemma alloc_top_win : forall h,
  init_sp_win h -> (alloc_ceiling <= alloc_top h <= sp_window_hi - stack_max_size)%Z.
Proof.
  intros h [Hlo Hhi]. unfold alloc_top, alloc_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.

Lemma alloc_top_win_vals : forall h,
  init_sp_win h -> (0x7fff7f800000 <= alloc_top h <= 0x7fffff800000)%Z.
Proof. intros h H. pose proof (alloc_top_win h H). unfold alloc_ceiling, sp_window_hi, stack_max_size in *. lia. Qed.

(* [comment removed for export] *)
Lemma alloc_top_lt_errno : forall h, (alloc_top h + stack_max_size < 2 ^ 64)%Z.
Proof. intros h. pose proof (alloc_top_room h). unfold two_pow_64 in *. lia. Qed.
