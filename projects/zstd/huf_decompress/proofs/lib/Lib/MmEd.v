(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg Placement MmapComplete.
Import ListNotations.
Open Scope bv_scope.

Lemma page_aligned_not_ENOMEM : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> bv_eqb a (errno_ret ENOMEM) = false.
Proof.
  intros a on_page. unfold bv_eqb. apply Z.eqb_neq. intros same_value.
  rewrite same_value, errno_ret_unsigned in on_page by (unfold ENOMEM; lia).
  revert on_page. unfold two_pow_64, ENOMEM, page_size. now vm_compute.
Qed.

Lemma ret_in_errnos_ENOMEM_aligned : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> ret_in_errnos [ENOMEM] a = false.
Proof.
  intros a on_page. pose proof (page_aligned_not_ENOMEM a on_page) as not_enomem.
  cbn [ret_in_errnos existsb]. now rewrite not_enomem.
Qed.

Lemma vm_base_ok_intro : forall h nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  vm_base_ok h nZ a = true.
Proof.
  intros h nZ a on_page above_zero under_top free_range.
  apply Z.eqb_eq in on_page. apply Z.ltb_lt in above_zero. apply Z.leb_le in under_top.
  unfold vm_base_ok. now rewrite free_range, under_top, above_zero, on_page.
Qed.

Lemma region_free_false_In : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. destruct (iv_overlap lo n b s) eqn:Ho.
  - exists b, s. split; [now left|exact Ho].
  - cbn in H. destruct (IH lo n H) as (a & sz & Hin & Hov).
    exists a, sz. split; [now right|exact Hov].
Qed.

Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros h nZ a Hok.
  pose proof (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & Htop & Hfree).
  pose proof (bv_unsigned_in_range 64 a) as [_ Ha]. unfold bv_modulus in Ha.
  destruct (Z.eq_dec (bv_unsigned a) page_size) as [Heq|Hne].
  { left. left. rewrite <- Heq. apply Z_to_bv_bv_unsigned. }
  assert (Hge : (2 * page_size <= bv_unsigned a)%Z).
  { unfold page_size in *.
    pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096). lia. }
  set (a' := Z_to_bv 64 (bv_unsigned a - page_size)).
  assert (Ua' : bv_unsigned a' = (bv_unsigned a - page_size)%Z).
  { subst a'. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus, page_size in *. lia. }
  destruct (vm_base_ok h nZ a') eqn:Hok'.
  { right. exists a'. split; [exact Ua'|exact Hok']. }
  left. unfold vm_base_ok in Hok'. rewrite Ua' in Hok'.
  assert (H1 : ((bv_unsigned a - page_size) mod page_size =? 0)%Z = true)
    by (apply Z.eqb_eq; rewrite Zminus_mod, Hal, Z_mod_same_full; reflexivity).
  assert (H2 : (0 <? bv_unsigned a - page_size)%Z = true)
    by (apply Z.ltb_lt; unfold page_size in *; lia).
  assert (H3 : (bv_unsigned a - page_size + nZ <=? alloc_top h)%Z = true)
    by (apply Z.leb_le; unfold page_size in *; lia).
  rewrite H1, H2, H3 in Hok'. cbn [andb] in Hok'.
  destruct (region_free_false_In _ _ _ Hok') as (lo & sz & Hin & Hov).
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hnov.
  unfold iv_overlap in Hov, Hnov. rewrite Ua' in Hov.
  apply andb_true_iff in Hov as [O1 O2].
  apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  apply andb_false_iff in Hnov as [N|N]; apply Z.ltb_ge in N;
    [|unfold page_size in *; lia].
  right. apply in_map_iff. exists (lo, sz). split; [|exact Hin].
  cbn [fst snd].
  replace (page_round_up_Z (bv_unsigned lo + bv_unsigned sz))
    with (bv_unsigned a); [apply Z_to_bv_bv_unsigned|].
  unfold page_round_up_Z, page_size in *.
  pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096) as Hq.
  rewrite Hal, Z.add_0_r in Hq.
  rewrite <- (Z.div_unique_pos (bv_unsigned lo + bv_unsigned sz + 4096 - 1)
                4096 (bv_unsigned a / 4096)
                (bv_unsigned lo + bv_unsigned sz + 4096 - 1
                 - 4096 * (bv_unsigned a / 4096))); lia.
Qed.

Lemma vm_find_base_complete_aux : forall h nZ k a,
  (bv_unsigned a <= Z.of_nat k * page_size)%Z ->
  vm_base_ok h nZ a = true ->
  exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true.
Proof.
  intros h nZ k. induction k as [|k IH]; intros a Hk Hok.
  - pose proof (vm_base_ok_sound h nZ a Hok) as (_ & Hpos & _). cbn in Hk. lia.
  - destruct (vm_base_ok_step h nZ a Hok) as [Hin | (a' & Ua' & Hok')].
    + exists a. split; assumption.
    + apply (IH a'); [|exact Hok'].
      rewrite Ua'. rewrite Nat2Z.inj_succ in Hk. unfold page_size in *. lia.
Qed.

Lemma vm_base_ok_gap_available : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ a Hok.
  pose proof (bv_unsigned_in_range 64 a) as [Ha _].
  destruct (vm_find_base_complete_aux h nZ (Z.to_nat (bv_unsigned a)) a)
    as (c & Hin & Hc); [unfold page_size; lia|exact Hok|].
  unfold vm_gap_available, vm_find_base.
  destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) eqn:Hf;
    [reflexivity|exfalso].
  pose proof (List.find_none _ _ Hf c Hin) as Hn. cbn beta in Hn.
  rewrite Hc in Hn. discriminate Hn.
Qed.

Lemma vm_gap_available_iff : forall h nZ,
  vm_gap_available h nZ = true <->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ. split.
  - intros H. apply vm_gap_available_find in H as [a Ha].
    exists a. exact (vm_find_base_sound h nZ a Ha).
  - intros (a & Hal & Hpos & Htop & Hfree).
    apply (vm_base_ok_gap_available h nZ a). apply vm_base_ok_intro; assumption.
Qed.

Lemma mmap_grant_refusable_false_iff : forall flags m nZ,
  mmap_grant_refusable flags m nZ = false <->
  mmap_noreserve_backed_ok flags m nZ = true /\ vm_gap_available (m_vmmaps m) nZ = true.
Proof.
  intros flags m nZ. unfold mmap_grant_refusable.
  destruct (vm_gap_available (m_vmmaps m) nZ), (mmap_noreserve_backed_ok flags m nZ);
    cbn [negb orb]; intuition congruence.
Qed.

Lemma mmap_reserve_refusable_false_iff : forall m nZ,
  mmap_reserve_refusable m nZ = false <-> vm_gap_available (m_vmmaps m) nZ = true.
Proof. intros m nZ. unfold mmap_reserve_refusable. exact (negb_false_iff _). Qed.

Lemma grant_conj_not_refusable : forall flags m nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a on_page above_zero under_top free_range backed.
  pose proof (vm_base_ok_gap_available (m_vmmaps m) nZ a
                (vm_base_ok_intro _ _ _ on_page above_zero under_top free_range)) as gap.
  apply mmap_grant_refusable_false_iff. exact (conj backed gap).
Qed.

Lemma reserve_conj_not_refusable : forall m nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a on_page above_zero under_top free_range.
  apply mmap_reserve_refusable_false_iff, vm_gap_available_iff.
  exists a. exact (conj on_page (conj above_zero (conj under_top free_range))).
Qed.

Lemma not_refusable_grant_conj : forall flags m nZ,
  mmap_grant_refusable flags m nZ = false ->
  mmap_noreserve_backed_ok flags m nZ = true /\
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros flags m nZ not_refusable.
  destruct (proj1 (mmap_grant_refusable_false_iff flags m nZ) not_refusable) as [backed gap].
  exact (conj backed (proj1 (vm_gap_available_iff (m_vmmaps m) nZ) gap)).
Qed.

Lemma not_refusable_reserve_conj : forall m nZ,
  mmap_reserve_refusable m nZ = false ->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros m nZ not_refusable.
  apply vm_gap_available_iff, mmap_reserve_refusable_false_iff. exact not_refusable.
Qed.

Definition w_nilb {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

Lemma w_nilb_true {A} (l : list A) : w_nilb l = true -> l = [].
Proof. destruct l; [reflexivity|discriminate]. Qed.

Definition check_mmap_ed (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len
     then check_ret_only eff (errno_ret EINVAL) m []
     else CheckUnmodeled)
  else if negb (mmap_anon_b flags) then CheckUnmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags
     then check_ret_only eff (errno_ret EINVAL) m []
     else CheckUnmodeled)
  else if mmap_modeled_b prot flags off then
    match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in (mmap_errnos_when
             (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)))) r
        then (if w_nilb zs then CheckOk m [] else CheckReject)
        else
          let nZ := page_round_up_Z (bv_unsigned len) in
          let n := Z_to_bv 64 nZ in
          if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
             && (bv_unsigned r + nZ <=? alloc_top (m_vmmaps m))%Z
             && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) r n
             && mmap_noreserve_backed_ok flags m nZ
             && listNN_eqb zs [(r, n)]
          then CheckOk
                 (with_mmap_backing flags r n
                  (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                               ((r, n) :: vm_maps (m_vmmaps m))
                               (vm_noaccess (m_vmmaps m))
                               (vm_start_brk (m_vmmaps m))
                               (vm_brk (m_vmmaps m))
                               (vm_limit (m_vmmaps m))
                               (vm_mmap_base (m_vmmaps m))
                               (vm_init_sp (m_vmmaps m))) m)) []
          else CheckReject
    | _ => CheckReject
    end
  else if mmap_noaccess_b prot flags off then
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in (mmap_errnos_when
             (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)))) r
        then (if w_nilb us then CheckOk m [] else CheckReject)
        else
          let nZ := page_round_up_Z (bv_unsigned len) in
          let n := Z_to_bv 64 nZ in
          if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
             && (bv_unsigned r + nZ <=? alloc_top (m_vmmaps m))%Z
             && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) r n
             && listNN_eqb us [(r, n)]
          then CheckOk
                 (with_mmap_backing flags r n
                  (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                               ((r, n) :: vm_maps (m_vmmaps m))
                               ((r, n) :: vm_noaccess (m_vmmaps m))
                               (vm_start_brk (m_vmmaps m))
                               (vm_brk (m_vmmaps m))
                               (vm_limit (m_vmmaps m))
                               (vm_mmap_base (m_vmmaps m))
                               (vm_init_sp (m_vmmaps m))) m)) []
          else CheckReject
    | _ => CheckReject
    end
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m)) addr n
         && map_contains (vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
              (with_mmap_replacement flags addr n
               (with_vmmaps
                (mkVmMapsFull (vm_reserved (m_vmmaps m))
                  (vm_maps (m_vmmaps m))
                  ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m))
                                  (bv_unsigned addr)
                                  (bv_unsigned addr + bv_unsigned n))
                  (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
                  (vm_limit (m_vmmaps m))
                  (vm_mmap_base (m_vmmaps m))
                  (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 ((addr, n) :: vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                                 (vm_mmap_base (m_vmmaps m))
                                 (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
              (with_mmap_replacement flags addr n
               (with_vmmaps
                 (mmap_fixed_noaccess_span_next (m_vmmaps m) addr n) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else CheckUnmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m)) addr n
         && map_contains (vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs us [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_commit_refusable flags m addr n)) r
               && w_nilb zs && w_nilb us
            then CheckOk m []
            else if errno_ret_in mmap_destructive_errnos r && w_nilb zs
                    && listNN_eqb us [(addr, n)]
            then CheckOk
              (with_mmap_destroyed addr n
                (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
            else match us with
                 | _ :: _ => CheckReject
                 | [] =>
                     if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                        && mmap_fixed_rw_budget_ok flags m addr n
                     then CheckOk
                       (with_mmap_replacement flags addr n
                         (with_vmmaps
                           (mmap_fixed_rw_next (m_vmmaps m) addr n) m)) []
                     else CheckReject
                 end
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r
            then (if w_nilb zs then CheckOk m [] else CheckReject)
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                    && mmap_noreserve_backed_ok flags m nZ
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 (vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                                 (vm_mmap_base (m_vmmaps m))
                                 (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs us [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_span_refusable flags m addr n)) r
               && w_nilb zs && w_nilb us
            then CheckOk m []
            else if errno_ret_in mmap_destructive_errnos r && w_nilb zs
                    && listNN_eqb us [(addr, n)]
            then CheckOk
              (with_mmap_destroyed addr n
                (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
            else match us with
                 | _ :: _ => CheckReject
                 | [] =>
                     if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                        && mmap_fixed_rw_span_budget_ok flags m addr n
                     then CheckOk
                       (with_mmap_replacement flags addr n
                         (with_vmmaps
                           (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)) []
                     else CheckReject
                 end
        | _ => CheckReject
        end
      else CheckUnmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 ((addr, n) :: vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                                 (vm_mmap_base (m_vmmaps m))
                                 (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else check_ret_only eff (errno_ret EEXIST) m []
  else if mmap_noreplace_rw_b prot flags off then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z
    then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
    then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r
            then (if w_nilb zs then CheckOk m [] else CheckReject)
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                    && mmap_noreserve_backed_ok flags m nZ
            then CheckOk
                   (with_mmap_backing flags addr n
                    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                                 ((addr, n) :: vm_maps (m_vmmaps m))
                                 (vm_noaccess (m_vmmaps m))
                                 (vm_start_brk (m_vmmaps m))
                                 (vm_brk (m_vmmaps m))
                                 (vm_limit (m_vmmaps m))
                                 (vm_mmap_base (m_vmmaps m))
                                 (vm_init_sp (m_vmmaps m))) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else check_ret_only eff (errno_ret EEXIST) m []
  else CheckUnmodeled.

Definition check_mprotect_ed (addr len prot : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if mprotect_grows_conflict_b prot
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then check_ret_only eff (errno_ret ENOMEM) m []
  else if negb (mprotect_modeled_b prot) then CheckUnmodeled
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if map_contains (vm_noaccess (m_vmmaps m)) addr n
       && map_contains (vm_maps (m_vmmaps m)) addr n then
      match eff with
      | mkEffectU r [] zs [] [] [] =>
          if errno_ret_in (mprotect_errnos_when (mprotect_refusable m addr n)) r
          then (if w_nilb zs then CheckOk m [] else CheckReject)
          else if mprotect_budget_ok m addr n && w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk (mprotect_model_next m addr n) []
          else CheckReject
      | _ => CheckReject
      end
    else if map_contains (vm_maps (m_vmmaps m)) addr n
            && region_free (vm_noaccess (m_vmmaps m)) addr n then
      match eff with
      | mkEffectU r [] [] [] [] [] => if w_is0 r then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled.

Ltac same := let H := fresh "H" in intros H; exact H.

Lemma errno_ret_in_when_false_of : forall b r,
  errno_ret_in mmap_errnos r = false -> errno_ret_in (mmap_errnos_when b) r = false.
Proof. intros b r not_refusal. destruct b; [exact not_refusal | reflexivity]. Qed.

Lemma errno_ret_in_mprotect_when_false_of : forall b r,
  errno_ret_in mprotect_errnos r = false -> errno_ret_in (mprotect_errnos_when b) r = false.
Proof. intros [|] r not_refusal; cbn [mprotect_errnos_when]; [exact not_refusal | reflexivity]. Qed.

Lemma aligned_not_mmap_errno : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> errno_ret_in mmap_errnos a = false.
Proof. intros a H. exact (ret_in_errnos_ENOMEM_aligned a H). Qed.

Lemma eexist_not_mmap_errno : errno_ret_in mmap_errnos (errno_ret EEXIST) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_not_mprotect_errno : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false.
Proof. exact eq_refl. Qed.

Lemma listNN_eqb_refl' : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition forced_mmap (addr len prot flags fd off : word) (m : Model) (eff : SyscallEffect) : Prop :=
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  forall eff2 m2 evs2, check_mmap addr len prot flags fd off eff2 m = CheckOk m2 evs2 ->
  errno_ret_in mmap_errnos (eff_ret eff2) = true.

Definition forced_mprotect (addr len prot : word) (m : Model) (eff : SyscallEffect) : Prop :=
  errno_ret_in mprotect_errnos (eff_ret eff) = true ->
  forall eff2 m2 evs2, check_mprotect addr len prot eff2 m = CheckOk m2 evs2 ->
  errno_ret_in mprotect_errnos (eff_ret eff2) = true.

(* [comment removed for export] *)
Definition mmap_corner_free (addr len prot flags off : word) (m : Model) (eff : SyscallEffect) : Prop :=
  mmap_fixed_rw_b prot flags off = true ->
  eff_unmaps eff = [] \/
  (region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
   && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
   /\ mmap_fixed_rw_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).

Lemma check_mmap_ed_fwd : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  forced_mmap addr len prot flags fd off m eff ->
  mmap_corner_free addr len prot flags off m eff ->
  check_mmap_ed addr len prot flags fd off eff m = CheckOk m' evs.
Proof.
  intros addr len prot flags fd off eff m m' evs std_ok forced corner_free.
  unfold check_mmap in std_ok. unfold check_mmap_ed.
  destruct (negb (mmap_off_aligned_b off)) eqn:off_misaligned;
    try rewrite off_misaligned in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  destruct (negb (mmap_anon_b flags)) eqn:not_anon;
    try rewrite not_anon in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  destruct (w_is0 len) eqn:empty_len;
    try rewrite empty_len in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  destruct (mmap_modeled_b prot flags off) eqn:hint_rw;
    try rewrite hint_rw in std_ok; cbv iota in std_ok |- *.
  { destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, unmaps, copies, reads; try exact std_ok.
    cbv iota in std_ok |- *.
    destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
      try rewrite answer_refuses in std_ok; cbv iota in std_ok.
    - destruct zeros; [|discriminate std_ok].
      assert (no_gap : mmap_grant_refusable flags m
                         (page_round_up_Z (bv_unsigned len)) = true).
      { destruct (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)))
          eqn:gap_open; [reflexivity|exfalso].
        destruct (not_refusable_grant_conj flags m _ gap_open)
          as [backed (base & on_page & above_zero & under_top & free_range)].
        pose proof (ret_in_errnos_ENOMEM_aligned base on_page) as base_not_errno.
        change (ret_in_errnos [ENOMEM] base)
          with (errno_ret_in mmap_errnos base) in base_not_errno.
        assert (base_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                  (mkEffect base []
                     [(base, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) m
                  = CheckOk m2 evs2).
        { do 2 eexists. unfold check_mmap.
          rewrite off_misaligned, not_anon, empty_len, hint_rw.
          cbv iota zeta. rewrite base_not_errno.
          rewrite (proj2 (Z.eqb_eq _ _) on_page), (proj2 (Z.ltb_lt _ _) above_zero),
                  (proj2 (Z.leb_le _ _) under_top), free_range, backed,
                  (proj2 (listNN_eqb_eq _ _) eq_refl).
          cbn [andb]. reflexivity. }
        destruct base_ok as (m2 & evs2 & base_ok).
        pose proof (forced answer_refuses _ _ _ base_ok) as base_is_errno.
        discriminate (eq_trans (eq_sym base_is_errno) base_not_errno). }
      rewrite no_gap. cbn [mmap_errnos_when]. rewrite answer_refuses.
      cbn [w_nilb]. exact std_ok.
    - rewrite (errno_ret_in_when_false_of _ _ answer_refuses). exact std_ok. }
  destruct (mmap_noaccess_b prot flags off) eqn:hint_none;
    try rewrite hint_none in std_ok; cbv iota in std_ok |- *.
  { destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, zeros, copies, reads; try exact std_ok.
    cbv iota in std_ok |- *.
    destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
      try rewrite answer_refuses in std_ok; cbv iota in std_ok.
    - destruct unmaps; [|discriminate std_ok].
      assert (no_gap : mmap_reserve_refusable m
                         (page_round_up_Z (bv_unsigned len)) = true).
      { destruct (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)))
          eqn:gap_open; [reflexivity|exfalso].
        destruct (not_refusable_reserve_conj m _ gap_open)
          as (base & on_page & above_zero & under_top & free_range).
        pose proof (ret_in_errnos_ENOMEM_aligned base on_page) as base_not_errno.
        change (ret_in_errnos [ENOMEM] base)
          with (errno_ret_in mmap_errnos base) in base_not_errno.
        assert (base_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                  (mkEffectU base [] []
                     [(base, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []) m
                  = CheckOk m2 evs2).
        { do 2 eexists. unfold check_mmap.
          rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none.
          cbv iota zeta. rewrite base_not_errno.
          rewrite (proj2 (Z.eqb_eq _ _) on_page), (proj2 (Z.ltb_lt _ _) above_zero),
                  (proj2 (Z.leb_le _ _) under_top), free_range,
                  (proj2 (listNN_eqb_eq _ _) eq_refl).
          cbn [andb]. reflexivity. }
        destruct base_ok as (m2 & evs2 & base_ok).
        pose proof (forced answer_refuses _ _ _ base_ok) as base_is_errno.
        discriminate (eq_trans (eq_sym base_is_errno) base_not_errno). }
      rewrite no_gap. cbn [mmap_errnos_when]. rewrite answer_refuses.
      cbn [w_nilb]. exact std_ok.
    - rewrite (errno_ret_in_when_false_of _ _ answer_refuses). exact std_ok. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:fixed_none;
    try rewrite fixed_none in std_ok; cbv iota in std_ok |- *.
  { cbv zeta in std_ok |- *.
    destruct ((two_pow_64 <=? bv_unsigned addr
                 + page_round_up_Z (bv_unsigned len))%Z) eqn:length_wraps;
      try rewrite length_wraps in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:above_top;
      try rewrite above_top in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:addr_off_page;
      try rewrite addr_off_page in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:addr_is_zero;
      try rewrite addr_is_zero in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    assert (addr_not_errno : errno_ret_in mmap_errnos addr = false).
    { apply negb_false_iff, Z.eqb_eq in addr_off_page.
      pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as aligned_answer.
      change (ret_in_errnos [ENOMEM] addr)
        with (errno_ret_in mmap_errnos addr) in aligned_answer. exact aligned_answer. }
    let reserve_case := fun _ =>
      destruct eff as [ret writes zeros unmaps copies reads];
      destruct writes, zeros, copies, reads; try exact std_ok;
      cbv iota in std_ok |- *;
      destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
        try rewrite answer_refuses in std_ok; cbv iota in std_ok;
      [ exfalso;
        assert (addr_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                  (mkEffectU addr [] []
                     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []) m
                  = CheckOk m2 evs2);
        [ do 2 eexists; unfold check_mmap;
          rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none, fixed_none;
          cbv iota zeta;
          rewrite length_wraps, above_top, addr_off_page, addr_is_zero;
          cbv iota; try (rewrite spans; cbv iota);
          rewrite contained; cbv iota;
          try (rewrite free_range; cbv iota);
          rewrite addr_not_errno, bv_eqb_refl,
                  (proj2 (listNN_eqb_eq _ _) eq_refl);
          cbn [andb]; reflexivity
        | destruct addr_ok as (m2 & evs2 & addr_ok);
          pose proof (forced answer_refuses _ _ _ addr_ok) as addr_is_errno;
          discriminate (eq_trans (eq_sym addr_is_errno) addr_not_errno) ]
      | exact std_ok ] in
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
              && map_contains (vm_maps (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:contained;
      try rewrite contained in std_ok; cbv iota in std_ok |- *;
    [ reserve_case tt |];
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:free_range;
      try rewrite free_range in std_ok; cbv iota in std_ok |- *;
    [ reserve_case tt |];
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:spans;
      try rewrite spans in std_ok; cbv iota in std_ok |- *;
    [ reserve_case tt | exact std_ok ]. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:fixed_rw;
    try rewrite fixed_rw in std_ok; cbv iota in std_ok |- *.
  { cbv zeta in std_ok |- *.
    destruct ((two_pow_64 <=? bv_unsigned addr
                 + page_round_up_Z (bv_unsigned len))%Z) eqn:length_wraps;
      try rewrite length_wraps in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:above_top;
      try rewrite above_top in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:addr_off_page;
      try rewrite addr_off_page in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:addr_is_zero;
      try rewrite addr_is_zero in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    assert (addr_not_errno : errno_ret_in mmap_errnos addr = false).
    { apply negb_false_iff, Z.eqb_eq in addr_off_page.
      pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as aligned_answer.
      change (ret_in_errnos [ENOMEM] addr)
        with (errno_ret_in mmap_errnos addr) in aligned_answer. exact aligned_answer. }
    destruct (region_free (vm_reserved (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
              && map_contains (vm_maps (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:contained;
      try rewrite contained in std_ok; cbv iota in std_ok |- *.
    - destruct eff as [ret writes zeros unmaps copies reads].
      destruct writes, copies, reads; try exact std_ok.
      cbv iota in std_ok |- *.
      destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
        try rewrite answer_refuses in std_ok; cbv iota in std_ok.
      + destruct zeros; [|discriminate std_ok]. cbv iota in std_ok.
        assert (no_budget : mmap_fixed_rw_budget_ok flags m addr
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false).
        { destruct (mmap_fixed_rw_budget_ok flags m addr
                      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
            eqn:budget_left; [exfalso|reflexivity].
          assert (addr_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                    (mkEffect addr []
                       [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) m
                    = CheckOk m2 evs2).
          { do 2 eexists. unfold check_mmap.
            rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw.
            cbv iota zeta.
            rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
            rewrite contained. cbv iota.
            rewrite addr_not_errno, bv_eqb_refl,
                    (proj2 (listNN_eqb_eq _ _) eq_refl), budget_left.
            cbn [andb]. reflexivity. }
          destruct addr_ok as (m2 & evs2 & addr_ok).
          pose proof (forced answer_refuses _ _ _ addr_ok) as addr_is_errno.
          discriminate (eq_trans (eq_sym addr_is_errno) addr_not_errno). }
        destruct unmaps as [|torn remains].
        * unfold mmap_fixed_commit_refusable. rewrite no_budget.
          cbn [negb mmap_errnos_when]. rewrite answer_refuses.
          cbn [w_nilb andb]. exact std_ok.
        * exfalso.
          destruct (corner_free fixed_rw) as [keeps_range | (_ & budget_left)];
            [discriminate keeps_range|].
          rewrite budget_left in no_budget. discriminate no_budget.
      + rewrite (errno_ret_in_when_false_of _ _ answer_refuses).
        change (errno_ret_in mmap_destructive_errnos ret) with false.
        cbn [andb]. exact std_ok.
    - destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:free_range;
        try rewrite free_range in std_ok; cbv iota in std_ok |- *.
      + destruct eff as [ret writes zeros unmaps copies reads].
        destruct writes, unmaps, copies, reads; try exact std_ok.
        cbv iota in std_ok |- *.
        destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
          try rewrite answer_refuses in std_ok; cbv iota in std_ok.
        * destruct zeros; [|discriminate std_ok].
          assert (no_backing : mmap_noreserve_backed_ok flags m
                    (page_round_up_Z (bv_unsigned len)) = false).
          { destruct (mmap_noreserve_backed_ok flags m
                        (page_round_up_Z (bv_unsigned len))) eqn:backing_left;
              [exfalso|reflexivity].
            assert (addr_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                      (mkEffect addr []
                         [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) m
                      = CheckOk m2 evs2).
            { do 2 eexists. unfold check_mmap.
              rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw.
              cbv iota zeta.
              rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
              rewrite contained. cbv iota. rewrite free_range. cbv iota.
              rewrite addr_not_errno, bv_eqb_refl,
                      (proj2 (listNN_eqb_eq _ _) eq_refl), backing_left.
              cbn [andb]. reflexivity. }
            destruct addr_ok as (m2 & evs2 & addr_ok).
            pose proof (forced answer_refuses _ _ _ addr_ok) as addr_is_errno.
            discriminate (eq_trans (eq_sym addr_is_errno) addr_not_errno). }
          unfold mmap_fixed_fresh_refusable. rewrite no_backing.
          cbn [negb mmap_errnos_when]. rewrite answer_refuses.
          cbn [w_nilb]. exact std_ok.
        * rewrite (errno_ret_in_when_false_of _ _ answer_refuses). exact std_ok.
      + destruct (region_free (vm_reserved (m_vmmaps m)) addr
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:spans;
          try rewrite spans in std_ok; cbv iota in std_ok |- *; [|exact std_ok].
        destruct eff as [ret writes zeros unmaps copies reads].
        destruct writes, copies, reads; try exact std_ok.
        cbv iota in std_ok |- *.
        destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
          try rewrite answer_refuses in std_ok; cbv iota in std_ok.
        * destruct zeros; [|discriminate std_ok]. cbv iota in std_ok.
          assert (no_budget : mmap_fixed_rw_span_budget_ok flags m addr
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false).
          { destruct (mmap_fixed_rw_span_budget_ok flags m addr
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
              eqn:budget_left; [exfalso|reflexivity].
            assert (addr_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                      (mkEffect addr []
                         [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) m
                      = CheckOk m2 evs2).
            { do 2 eexists. unfold check_mmap.
              rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw.
              cbv iota zeta.
              rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
              rewrite spans. cbv iota. rewrite contained. cbv iota.
              rewrite free_range. cbv iota.
              rewrite addr_not_errno, bv_eqb_refl,
                      (proj2 (listNN_eqb_eq _ _) eq_refl), budget_left.
              cbn [andb]. reflexivity. }
            destruct addr_ok as (m2 & evs2 & addr_ok).
            pose proof (forced answer_refuses _ _ _ addr_ok) as addr_is_errno.
            discriminate (eq_trans (eq_sym addr_is_errno) addr_not_errno). }
          destruct unmaps as [|torn remains].
          -- unfold mmap_fixed_span_refusable. rewrite no_budget.
             cbn [negb mmap_errnos_when]. rewrite answer_refuses.
             cbn [w_nilb andb]. exact std_ok.
          -- exfalso.
             destruct (corner_free fixed_rw) as [keeps_range | (inside & _)];
               [discriminate keeps_range|].
             rewrite spans in inside. discriminate (eq_trans (eq_sym inside) contained).
        * rewrite (errno_ret_in_when_false_of _ _ answer_refuses).
          change (errno_ret_in mmap_destructive_errnos ret) with false.
          cbn [andb]. exact std_ok. }
  destruct (mmap_noreplace_noaccess_b prot flags off) eqn:noreplace_none;
    try rewrite noreplace_none in std_ok; cbv iota in std_ok |- *.
  { cbv zeta in std_ok |- *.
    destruct ((two_pow_64 <=? bv_unsigned addr
                 + page_round_up_Z (bv_unsigned len))%Z) eqn:length_wraps;
      try rewrite length_wraps in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                      <=? alloc_top (m_vmmaps m))%Z) eqn:above_top;
      try rewrite above_top in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:addr_off_page;
      try rewrite addr_off_page in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    destruct (negb (0 <? bv_unsigned addr)%Z) eqn:addr_is_zero;
      try rewrite addr_is_zero in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
    assert (addr_not_errno : errno_ret_in mmap_errnos addr = false).
    { apply negb_false_iff, Z.eqb_eq in addr_off_page.
      pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as aligned_answer.
      change (ret_in_errnos [ENOMEM] addr)
        with (errno_ret_in mmap_errnos addr) in aligned_answer. exact aligned_answer. }
    destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:free_range;
      try rewrite free_range in std_ok; cbv iota in std_ok |- *.
    - destruct eff as [ret writes zeros unmaps copies reads].
      destruct writes, zeros, copies, reads; try exact std_ok.
      cbv iota in std_ok |- *.
      destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
        try rewrite answer_refuses in std_ok; cbv iota in std_ok; [|exact std_ok].
      exfalso.
      assert (addr_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                (mkEffectU addr [] []
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []) m
                = CheckOk m2 evs2).
      { do 2 eexists. unfold check_mmap.
        rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw, noreplace_none.
        cbv iota zeta.
        rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
        rewrite free_range. cbv iota.
        rewrite addr_not_errno, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl).
        cbn [andb]. reflexivity. }
      destruct addr_ok as (m2 & evs2 & addr_ok).
      pose proof (forced answer_refuses _ _ _ addr_ok) as addr_is_errno.
      discriminate (eq_trans (eq_sym addr_is_errno) addr_not_errno).
    - destruct eff as [ret writes zeros unmaps copies reads].
      destruct writes, zeros, unmaps, copies, reads; try exact std_ok.
      cbv iota in std_ok |- *.
      destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
        cbv iota in std_ok.
      + exfalso.
        assert (clash_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                  (mkEffect (errno_ret EEXIST) [] []) m = CheckOk m2 evs2).
        { do 2 eexists. unfold check_mmap.
          rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw, noreplace_none.
          cbv iota zeta.
          rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
          rewrite free_range. cbv iota.
          rewrite bv_eqb_refl, orb_true_r. reflexivity. }
        destruct clash_ok as (m2 & evs2 & clash_ok).
        pose proof (forced answer_refuses _ _ _ clash_ok) as clash_is_errno.
        discriminate (eq_trans (eq_sym clash_is_errno) eexist_not_mmap_errno).
      + cbn [orb] in std_ok.
        destruct (bv_eqb ret (errno_ret EEXIST)) eqn:is_clash; [|discriminate std_ok].
        unfold check_ret_only. cbv iota. try rewrite is_clash. exact std_ok. }
  destruct (mmap_noreplace_rw_b prot flags off) eqn:noreplace_rw;
    try rewrite noreplace_rw in std_ok; cbv iota in std_ok |- *; [|exact std_ok].
  cbv zeta in std_ok |- *.
  destruct ((two_pow_64 <=? bv_unsigned addr
               + page_round_up_Z (bv_unsigned len))%Z) eqn:length_wraps;
    try rewrite length_wraps in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:above_top;
    try rewrite above_top in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:addr_off_page;
    try rewrite addr_off_page in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:addr_is_zero;
    try rewrite addr_is_zero in std_ok; cbv iota in std_ok |- *; [exact std_ok|].
  assert (addr_not_errno : errno_ret_in mmap_errnos addr = false).
  { apply negb_false_iff, Z.eqb_eq in addr_off_page.
    pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as aligned_answer.
    change (ret_in_errnos [ENOMEM] addr)
      with (errno_ret_in mmap_errnos addr) in aligned_answer. exact aligned_answer. }
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:free_range;
    try rewrite free_range in std_ok; cbv iota in std_ok |- *.
  - destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, unmaps, copies, reads; try exact std_ok.
    cbv iota in std_ok |- *.
    destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses;
      try rewrite answer_refuses in std_ok; cbv iota in std_ok.
    + destruct zeros; [|discriminate std_ok].
      assert (no_backing : mmap_noreserve_backed_ok flags m
                (page_round_up_Z (bv_unsigned len)) = false).
      { destruct (mmap_noreserve_backed_ok flags m
                    (page_round_up_Z (bv_unsigned len))) eqn:backing_left;
          [exfalso|reflexivity].
        assert (addr_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                  (mkEffect addr []
                     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) m
                  = CheckOk m2 evs2).
        { do 2 eexists. unfold check_mmap.
          rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw, noreplace_none, noreplace_rw.
          cbv iota zeta.
          rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
          rewrite free_range. cbv iota.
          rewrite addr_not_errno, bv_eqb_refl,
                  (proj2 (listNN_eqb_eq _ _) eq_refl), backing_left.
          cbn [andb]. reflexivity. }
        destruct addr_ok as (m2 & evs2 & addr_ok).
        pose proof (forced answer_refuses _ _ _ addr_ok) as addr_is_errno.
        discriminate (eq_trans (eq_sym addr_is_errno) addr_not_errno). }
      unfold mmap_fixed_fresh_refusable. rewrite no_backing.
      cbn [negb mmap_errnos_when]. rewrite answer_refuses. cbn [w_nilb].
      exact std_ok.
    + rewrite (errno_ret_in_when_false_of _ _ answer_refuses). exact std_ok.
  - destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, zeros, unmaps, copies, reads; try exact std_ok.
    cbv iota in std_ok |- *.
    destruct (errno_ret_in mmap_errnos ret) eqn:answer_refuses; cbv iota in std_ok.
    + exfalso.
      assert (clash_ok : exists m2 evs2, check_mmap addr len prot flags fd off
                (mkEffect (errno_ret EEXIST) [] []) m = CheckOk m2 evs2).
      { do 2 eexists. unfold check_mmap.
        rewrite off_misaligned, not_anon, empty_len, hint_rw, hint_none,
                  fixed_none, fixed_rw, noreplace_none, noreplace_rw.
        cbv iota zeta.
        rewrite length_wraps, above_top, addr_off_page, addr_is_zero. cbv iota.
        rewrite free_range. cbv iota.
        rewrite bv_eqb_refl, orb_true_r. reflexivity. }
      destruct clash_ok as (m2 & evs2 & clash_ok).
      pose proof (forced answer_refuses _ _ _ clash_ok) as clash_is_errno.
      discriminate (eq_trans (eq_sym clash_is_errno) eexist_not_mmap_errno).
    + cbn [orb] in std_ok.
      destruct (bv_eqb ret (errno_ret EEXIST)) eqn:is_clash; [|discriminate std_ok].
      unfold check_ret_only. cbv iota. try rewrite is_clash. exact std_ok.
Qed.

Lemma check_mprotect_ed_fwd : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  forced_mprotect addr len prot m eff ->
  check_mprotect_ed addr len prot eff m = CheckOk m' evs.
Proof.
  intros addr len prot eff m m' evs std_ok forced.
  unfold check_mprotect in std_ok. unfold check_mprotect_ed.
  destruct (mprotect_grows_conflict_b prot) eqn:grows;
    try rewrite grows in std_ok; cbv iota in std_ok; [exact std_ok|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:off_page;
    try rewrite off_page in std_ok; cbv iota in std_ok; [exact std_ok|].
  destruct (w_is0 len) eqn:empty_len;
    try rewrite empty_len in std_ok; cbv iota in std_ok; [exact std_ok|].
  destruct ((two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:wraps; try rewrite wraps in std_ok; cbv iota in std_ok; [exact std_ok|].
  destruct (negb (mprotect_modeled_b prot)) eqn:not_modeled;
    try rewrite not_modeled in std_ok; cbv iota in std_ok; [exact std_ok|].
  cbv zeta in std_ok |- *.
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:protected;
    try rewrite protected in std_ok; cbv iota in std_ok; [|exact std_ok].
  destruct eff as [ret writes zeros unmaps copies reads].
  destruct writes, unmaps, copies, reads; try (exact std_ok).
  cbv iota in std_ok |- *.
  destruct (errno_ret_in mprotect_errnos ret) eqn:refusal.
  - destruct zeros; [|discriminate std_ok].
    destruct (mprotect_budget_ok m addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:within_budget.
    + exfalso.
      assert (grant_ok : check_mprotect addr len prot
                (mkEffect (Z_to_bv 64 0) []
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]) m
              = CheckOk (mprotect_model_next m addr
                           (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) []).
      { unfold check_mprotect.
        rewrite grows, off_page, empty_len, wraps, not_modeled.
        cbv iota zeta. rewrite protected. cbv iota.
        rewrite zero_not_mprotect_errno, within_budget.
        unfold w_is0. rewrite bv_eqb_refl.
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb]. reflexivity. }
      pose proof (forced refusal _ _ _ grant_ok) as zero_is_errno.
      discriminate (eq_trans (eq_sym zero_is_errno) zero_not_mprotect_errno).
    + replace (mprotect_refusable m addr
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) with true
        by (unfold mprotect_refusable; rewrite within_budget; reflexivity).
      cbn [mprotect_errnos_when]. rewrite refusal. cbn [w_nilb]. exact std_ok.
  - rewrite (errno_ret_in_mprotect_when_false_of _ _ refusal). exact std_ok.
Qed.

Lemma refusal_neq : forall r a : word,
  errno_ret_in mmap_errnos r = true -> errno_ret_in mmap_errnos a = false -> bv_eqb r a = false.
Proof.
  intros r a Hr Ha. destruct (bv_eqb r a) eqn:Q; [|reflexivity].
  apply bv_eqb_eq in Q. subst a. congruence.
Qed.

Lemma forced_mmap_nonrefusal : forall addr len prot flags fd off m eff,
  errno_ret_in mmap_errnos (eff_ret eff) = false -> forced_mmap addr len prot flags fd off m eff.
Proof. intros addr len prot flags fd off m eff H Hr. congruence. Qed.

Lemma forced_mprotect_nonrefusal : forall addr len prot m eff,
  errno_ret_in mprotect_errnos (eff_ret eff) = false -> forced_mprotect addr len prot m eff.
Proof. intros addr len prot m eff H Hr. congruence. Qed.

(* [comment removed for export] *)
Ltac if_cond H C :=
  lazymatch type of H with
  | context [if ?test then _ else _] =>
      destruct test eqn:C; try rewrite C in H; cbv iota in H
  end.

Ltac andb_split C :=
  repeat match type of C with
  | (_ && _) = true => let C' := fresh "C" in apply andb_prop in C as [C C']
  end.

Lemma check_mmap_ed_bwd : forall addr len prot flags fd off eff m m' evs,
  check_mmap_ed addr len prot flags fd off eff m = CheckOk m' evs ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs
  /\ forced_mmap addr len prot flags fd off m eff.
Proof.
  intros addr len prot flags fd off eff m m' evs ed_ok.
  unfold check_mmap_ed in ed_ok. unfold forced_mmap, check_mmap.
  if_cond ed_ok off_misaligned.
  { if_cond ed_ok pglen_ok; [|discriminate ed_ok].
    split; [exact ed_ok|].
    intros refused other m2 evs2 other_ok.
    apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
    apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
  if_cond ed_ok not_anon; [discriminate ed_ok|].
  if_cond ed_ok empty_len.
  { if_cond ed_ok plain_anon; [|discriminate ed_ok].
    split; [exact ed_ok|].
    intros refused other m2 evs2 other_ok.
    apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
    apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
  if_cond ed_ok hint_rw.
  { destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, unmaps, copies, reads; try discriminate ed_ok.
    cbv iota in ed_ok |- *. cbn [eff_ret].
    destruct (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)))
      eqn:grant_refusable; try rewrite grant_refusable in ed_ok;
      cbn [mmap_errnos_when] in ed_ok.
    - if_cond ed_ok answer_refuses.
      + if_cond ed_ok no_zeros; [|discriminate ed_ok].
        apply w_nilb_true in no_zeros as ->.
        try rewrite answer_refuses. split; [exact ed_ok|].
        intros _ other m2 evs2 other_ok.
        destruct other as [r2 w2 z2 u2 c2 i2]. cbn [eff_ret].
        destruct w2, u2, c2, i2; try discriminate other_ok.
        cbv iota in other_ok.
        destruct (errno_ret_in mmap_errnos r2) eqn:other_refuses; [reflexivity|].
        exfalso. try rewrite other_refuses in other_ok. cbv iota in other_ok.
        if_cond other_ok other_grants; [|discriminate other_ok].
        apply andb_prop in other_grants as [other_grants zeros_shape].
        apply andb_prop in other_grants as [other_grants backed].
        apply andb_prop in other_grants as [other_grants free_range].
        apply andb_prop in other_grants as [other_grants under_top].
        apply andb_prop in other_grants as [on_page above_zero].
        apply Z.eqb_eq in on_page. apply Z.ltb_lt in above_zero.
        apply Z.leb_le in under_top.
        rewrite (grant_conj_not_refusable flags m _ r2 on_page above_zero
                   under_top free_range backed) in grant_refusable.
        discriminate grant_refusable.
      + try rewrite answer_refuses. split; [exact ed_ok|].
        intros refused.
        first [ discriminate refused
              | discriminate (eq_trans (eq_sym refused) answer_refuses) ].
    - cbn [errno_ret_in existsb] in ed_ok. cbv iota in ed_ok.
      if_cond ed_ok granted; [|discriminate ed_ok].
      apply andb_prop in granted as [granted _].
      apply andb_prop in granted as [granted _].
      apply andb_prop in granted as [granted _].
      apply andb_prop in granted as [granted _].
      apply andb_prop in granted as [on_page _].
      apply Z.eqb_eq in on_page.
      pose proof (ret_in_errnos_ENOMEM_aligned ret on_page) as answer_not_errno.
      change (ret_in_errnos [ENOMEM] ret) with (errno_ret_in mmap_errnos ret)
        in answer_not_errno.
      try rewrite answer_not_errno. split; [exact ed_ok|].
      intros refused.
      first [ discriminate refused
            | discriminate (eq_trans (eq_sym refused) answer_not_errno) ]. }
  if_cond ed_ok hint_none.
  { destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, zeros, copies, reads; try discriminate ed_ok.
    cbv iota in ed_ok |- *. cbn [eff_ret].
    destruct (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)))
      eqn:reserve_refusable; try rewrite reserve_refusable in ed_ok;
      cbn [mmap_errnos_when] in ed_ok.
    - if_cond ed_ok answer_refuses.
      + if_cond ed_ok no_unmaps; [|discriminate ed_ok].
        apply w_nilb_true in no_unmaps as ->.
        try rewrite answer_refuses. split; [exact ed_ok|].
        intros _ other m2 evs2 other_ok.
        destruct other as [r2 w2 z2 u2 c2 i2]. cbn [eff_ret].
        destruct w2, z2, c2, i2; try discriminate other_ok.
        cbv iota in other_ok.
        destruct (errno_ret_in mmap_errnos r2) eqn:other_refuses; [reflexivity|].
        exfalso. try rewrite other_refuses in other_ok. cbv iota in other_ok.
        if_cond other_ok other_reserves; [|discriminate other_ok].
        apply andb_prop in other_reserves as [other_reserves unmaps_shape].
        apply andb_prop in other_reserves as [other_reserves free_range].
        apply andb_prop in other_reserves as [other_reserves under_top].
        apply andb_prop in other_reserves as [on_page above_zero].
        apply Z.eqb_eq in on_page. apply Z.ltb_lt in above_zero.
        apply Z.leb_le in under_top.
        rewrite (reserve_conj_not_refusable m _ r2 on_page above_zero
                   under_top free_range) in reserve_refusable.
        discriminate reserve_refusable.
      + try rewrite answer_refuses. split; [exact ed_ok|].
        intros refused.
        first [ discriminate refused
              | discriminate (eq_trans (eq_sym refused) answer_refuses) ].
    - cbn [errno_ret_in existsb] in ed_ok. cbv iota in ed_ok.
      if_cond ed_ok reserved; [|discriminate ed_ok].
      apply andb_prop in reserved as [reserved _].
      apply andb_prop in reserved as [reserved _].
      apply andb_prop in reserved as [reserved _].
      apply andb_prop in reserved as [on_page _].
      apply Z.eqb_eq in on_page.
      pose proof (ret_in_errnos_ENOMEM_aligned ret on_page) as answer_not_errno.
      change (ret_in_errnos [ENOMEM] ret) with (errno_ret_in mmap_errnos ret)
        in answer_not_errno.
      try rewrite answer_not_errno. split; [exact ed_ok|].
      intros refused.
      first [ discriminate refused
            | discriminate (eq_trans (eq_sym refused) answer_not_errno) ]. }
  if_cond ed_ok hint_fixed_none.
  { cbv zeta in ed_ok |- *.
    if_cond ed_ok length_wraps.
    { split; [exact ed_ok|].
      intros refused other m2 evs2 other_ok.
      apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
      apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
    if_cond ed_ok above_top; [discriminate ed_ok|].
    if_cond ed_ok addr_off_page.
    { split; [exact ed_ok|].
      intros refused other m2 evs2 other_ok.
      apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
      apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
    if_cond ed_ok addr_is_zero; [discriminate ed_ok|].
    apply negb_false_iff, Z.eqb_eq in addr_off_page.
    pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as addr_not_errno.
    change (ret_in_errnos [ENOMEM] addr) with (errno_ret_in mmap_errnos addr)
      in addr_not_errno.
    let reserve_case := fun _ =>
      destruct eff as [ret writes zeros unmaps copies reads];
      destruct writes, zeros, copies, reads; try discriminate ed_ok;
      cbv iota in ed_ok |- *;
      if_cond ed_ok installs; [|discriminate ed_ok];
      apply andb_prop in installs as [same_answer _];
      apply bv_eqb_eq in same_answer as ->;
      try rewrite addr_not_errno;
      split; [exact ed_ok|];
      intros refused;
      first [ discriminate refused
            | discriminate (eq_trans (eq_sym refused) addr_not_errno) ] in
    if_cond ed_ok contained; [reserve_case tt|];
    if_cond ed_ok free_range; [reserve_case tt|];
    if_cond ed_ok spans; [reserve_case tt|discriminate ed_ok]. }
  if_cond ed_ok fixed_rw.
  { cbv zeta in ed_ok |- *.
    if_cond ed_ok length_wraps.
    { split; [exact ed_ok|].
      intros refused other m2 evs2 other_ok.
      apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
      apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
    if_cond ed_ok above_top; [discriminate ed_ok|].
    if_cond ed_ok addr_off_page.
    { split; [exact ed_ok|].
      intros refused other m2 evs2 other_ok.
      apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
      apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
    if_cond ed_ok addr_is_zero; [discriminate ed_ok|].
    apply negb_false_iff, Z.eqb_eq in addr_off_page.
    pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as addr_not_errno.
    change (ret_in_errnos [ENOMEM] addr) with (errno_ret_in mmap_errnos addr)
      in addr_not_errno.
    if_cond ed_ok contained.
    - destruct eff as [ret writes zeros unmaps copies reads].
      destruct writes, copies, reads; try discriminate ed_ok.
      cbv iota in ed_ok |- *.
      if_cond ed_ok budget_refusal.
      + apply andb_prop in budget_refusal as [budget_refusal no_unmaps].
        apply andb_prop in budget_refusal as [listed no_zeros].
        apply w_nilb_true in no_zeros as ->. apply w_nilb_true in no_unmaps as ->.
        destruct (mmap_fixed_commit_refusable flags m addr
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:no_budget;
          [|cbn [mmap_errnos_when errno_ret_in existsb] in listed; discriminate listed].
        change (errno_ret_in mmap_errnos ret = true) in listed.
        try rewrite listed. split; [exact ed_ok|].
        intros _ other m2 evs2 other_ok.
        destruct other as [r2 w2 z2 u2 c2 i2]. cbn [eff_ret].
        destruct w2, c2, i2; try discriminate other_ok.
        cbv iota in other_ok.
        destruct (errno_ret_in mmap_errnos r2) eqn:other_refuses; [reflexivity|].
        exfalso. try rewrite other_refuses in other_ok. cbv iota in other_ok.
        destruct u2; [|discriminate other_ok]. cbv iota in other_ok.
        if_cond other_ok other_commits; [|discriminate other_ok].
        apply andb_prop in other_commits as [_ other_budget].
        unfold mmap_fixed_commit_refusable in no_budget.
        rewrite other_budget in no_budget. discriminate no_budget.
      + if_cond ed_ok destroyed_refusal.
        * apply andb_prop in destroyed_refusal as [destroyed_refusal _].
          apply andb_prop in destroyed_refusal as [destructive _].
          cbn [errno_ret_in mmap_destructive_errnos existsb] in destructive.
          discriminate destructive.
        * destruct unmaps; [|discriminate ed_ok].
          cbv iota in ed_ok |- *.
          if_cond ed_ok commits; [|discriminate ed_ok].
          apply andb_prop in commits as [commits _].
          apply andb_prop in commits as [same_answer _].
          apply bv_eqb_eq in same_answer as ->.
          try rewrite addr_not_errno. split; [exact ed_ok|].
          intros refused.
          first [ discriminate refused
                | discriminate (eq_trans (eq_sym refused) addr_not_errno) ].
    - if_cond ed_ok free_range.
      + destruct eff as [ret writes zeros unmaps copies reads].
        destruct writes, unmaps, copies, reads; try discriminate ed_ok.
        cbv iota in ed_ok |- *.
        destruct (mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)))
          eqn:no_backing; try rewrite no_backing in ed_ok;
          cbn [mmap_errnos_when] in ed_ok.
        * if_cond ed_ok answer_refuses.
          -- if_cond ed_ok no_zeros; [|discriminate ed_ok].
             apply w_nilb_true in no_zeros as ->.
             try rewrite answer_refuses. split; [exact ed_ok|].
             intros _ other m2 evs2 other_ok.
             destruct other as [r2 w2 z2 u2 c2 i2]. cbn [eff_ret].
             destruct w2, u2, c2, i2; try discriminate other_ok.
             cbv iota in other_ok.
             destruct (errno_ret_in mmap_errnos r2) eqn:other_refuses; [reflexivity|].
             exfalso. try rewrite other_refuses in other_ok. cbv iota in other_ok.
             if_cond other_ok other_grants; [|discriminate other_ok].
             apply andb_prop in other_grants as [_ other_backed].
             unfold mmap_fixed_fresh_refusable in no_backing.
             rewrite other_backed in no_backing. discriminate no_backing.
          -- try rewrite answer_refuses. split; [exact ed_ok|].
             intros refused.
             first [ discriminate refused
                   | discriminate (eq_trans (eq_sym refused) answer_refuses) ].
        * cbn [errno_ret_in existsb] in ed_ok. cbv iota in ed_ok.
          if_cond ed_ok grants; [|discriminate ed_ok].
          apply andb_prop in grants as [grants _].
          apply andb_prop in grants as [same_answer _].
          apply bv_eqb_eq in same_answer as ->.
          try rewrite addr_not_errno. split; [exact ed_ok|].
          intros refused.
          first [ discriminate refused
                | discriminate (eq_trans (eq_sym refused) addr_not_errno) ].
      + if_cond ed_ok spans; [|discriminate ed_ok].
        destruct eff as [ret writes zeros unmaps copies reads].
        destruct writes, copies, reads; try discriminate ed_ok.
        cbv iota in ed_ok |- *.
        if_cond ed_ok budget_refusal.
        * apply andb_prop in budget_refusal as [budget_refusal no_unmaps].
          apply andb_prop in budget_refusal as [listed no_zeros].
          apply w_nilb_true in no_zeros as ->. apply w_nilb_true in no_unmaps as ->.
          destruct (mmap_fixed_span_refusable flags m addr
                      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:no_budget;
            [|cbn [mmap_errnos_when errno_ret_in existsb] in listed; discriminate listed].
          change (errno_ret_in mmap_errnos ret = true) in listed.
          try rewrite listed. split; [exact ed_ok|].
          intros _ other m2 evs2 other_ok.
          destruct other as [r2 w2 z2 u2 c2 i2]. cbn [eff_ret].
          destruct w2, c2, i2; try discriminate other_ok.
          cbv iota in other_ok.
          destruct (errno_ret_in mmap_errnos r2) eqn:other_refuses; [reflexivity|].
          exfalso. try rewrite other_refuses in other_ok. cbv iota in other_ok.
          destruct u2; [|discriminate other_ok]. cbv iota in other_ok.
          if_cond other_ok other_spans; [|discriminate other_ok].
          apply andb_prop in other_spans as [_ other_budget].
          unfold mmap_fixed_span_refusable in no_budget.
          rewrite other_budget in no_budget. discriminate no_budget.
        * if_cond ed_ok destroyed_refusal.
          -- apply andb_prop in destroyed_refusal as [destroyed_refusal _].
             apply andb_prop in destroyed_refusal as [destructive _].
             cbn [errno_ret_in mmap_destructive_errnos existsb] in destructive.
             discriminate destructive.
          -- destruct unmaps; [|discriminate ed_ok].
             cbv iota in ed_ok |- *.
             if_cond ed_ok replaces; [|discriminate ed_ok].
             apply andb_prop in replaces as [replaces _].
             apply andb_prop in replaces as [same_answer _].
             apply bv_eqb_eq in same_answer as ->.
             try rewrite addr_not_errno. split; [exact ed_ok|].
             intros refused.
             first [ discriminate refused
                   | discriminate (eq_trans (eq_sym refused) addr_not_errno) ]. }
  if_cond ed_ok noreplace_none.
  { cbv zeta in ed_ok |- *.
    if_cond ed_ok length_wraps.
    { split; [exact ed_ok|].
      intros refused other m2 evs2 other_ok.
      apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
      apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
    if_cond ed_ok above_top; [discriminate ed_ok|].
    if_cond ed_ok addr_off_page.
    { split; [exact ed_ok|].
      intros refused other m2 evs2 other_ok.
      apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
      apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
    if_cond ed_ok addr_is_zero; [discriminate ed_ok|].
    apply negb_false_iff, Z.eqb_eq in addr_off_page.
    pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as addr_not_errno.
    change (ret_in_errnos [ENOMEM] addr) with (errno_ret_in mmap_errnos addr)
      in addr_not_errno.
    if_cond ed_ok free_range.
    - destruct eff as [ret writes zeros unmaps copies reads].
      destruct writes, zeros, copies, reads; try discriminate ed_ok.
      cbv iota in ed_ok |- *.
      if_cond ed_ok installs; [|discriminate ed_ok].
      apply andb_prop in installs as [same_answer _].
      apply bv_eqb_eq in same_answer as ->.
      try rewrite addr_not_errno. split; [exact ed_ok|].
      intros refused.
      first [ discriminate refused
            | discriminate (eq_trans (eq_sym refused) addr_not_errno) ].
    - apply check_ret_only_ok_iff in ed_ok as (-> & -> & ->).
      cbv iota. split.
      + rewrite eexist_not_mmap_errno, bv_eqb_refl. reflexivity.
      + intros refused.
        discriminate (eq_trans (eq_sym refused) eexist_not_mmap_errno). }
  if_cond ed_ok noreplace_rw; [|discriminate ed_ok].
  cbv zeta in ed_ok |- *.
  if_cond ed_ok length_wraps.
  { split; [exact ed_ok|].
    intros refused other m2 evs2 other_ok.
    apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
    apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
  if_cond ed_ok above_top; [discriminate ed_ok|].
  if_cond ed_ok addr_off_page.
  { split; [exact ed_ok|].
    intros refused other m2 evs2 other_ok.
    apply check_ret_only_ok_iff in ed_ok as (-> & _ & _).
    apply check_ret_only_ok_iff in other_ok as (-> & _ & _). exact refused. }
  if_cond ed_ok addr_is_zero; [discriminate ed_ok|].
  apply negb_false_iff, Z.eqb_eq in addr_off_page.
  pose proof (ret_in_errnos_ENOMEM_aligned addr addr_off_page) as addr_not_errno.
  change (ret_in_errnos [ENOMEM] addr) with (errno_ret_in mmap_errnos addr)
    in addr_not_errno.
  if_cond ed_ok free_range.
  - destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, unmaps, copies, reads; try discriminate ed_ok.
    cbv iota in ed_ok |- *.
    destruct (mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)))
      eqn:no_backing; try rewrite no_backing in ed_ok;
      cbn [mmap_errnos_when] in ed_ok.
    + if_cond ed_ok answer_refuses.
      * if_cond ed_ok no_zeros; [|discriminate ed_ok].
        apply w_nilb_true in no_zeros as ->.
        try rewrite answer_refuses. split; [exact ed_ok|].
        intros _ other m2 evs2 other_ok.
        destruct other as [r2 w2 z2 u2 c2 i2]. cbn [eff_ret].
        destruct w2, u2, c2, i2; try discriminate other_ok.
        cbv iota in other_ok.
        destruct (errno_ret_in mmap_errnos r2) eqn:other_refuses; [reflexivity|].
        exfalso. try rewrite other_refuses in other_ok. cbv iota in other_ok.
        if_cond other_ok other_grants; [|discriminate other_ok].
        apply andb_prop in other_grants as [_ other_backed].
        unfold mmap_fixed_fresh_refusable in no_backing.
        rewrite other_backed in no_backing. discriminate no_backing.
      * try rewrite answer_refuses. split; [exact ed_ok|].
        intros refused.
        first [ discriminate refused
              | discriminate (eq_trans (eq_sym refused) answer_refuses) ].
    + cbn [errno_ret_in existsb] in ed_ok. cbv iota in ed_ok.
      if_cond ed_ok grants; [|discriminate ed_ok].
      apply andb_prop in grants as [grants _].
      apply andb_prop in grants as [same_answer _].
      apply bv_eqb_eq in same_answer as ->.
      try rewrite addr_not_errno. split; [exact ed_ok|].
      intros refused.
      first [ discriminate refused
            | discriminate (eq_trans (eq_sym refused) addr_not_errno) ].
  - apply check_ret_only_ok_iff in ed_ok as (-> & -> & ->).
    cbv iota. split.
    + rewrite eexist_not_mmap_errno, bv_eqb_refl. reflexivity.
    + intros refused.
      discriminate (eq_trans (eq_sym refused) eexist_not_mmap_errno).
Qed.

Lemma check_mprotect_ed_bwd : forall addr len prot eff m m' evs,
  check_mprotect_ed addr len prot eff m = CheckOk m' evs ->
  check_mprotect addr len prot eff m = CheckOk m' evs /\ forced_mprotect addr len prot m eff.
Proof.
  intros addr len prot eff m m' evs ed_ok.
  unfold check_mprotect_ed in ed_ok. unfold forced_mprotect, check_mprotect.
  let fixed_answer := fun _ =>
    split; [assumption|];
    intros refused other m2 evs2 other_ok;
    apply check_ret_only_ok_iff in ed_ok as (-> & _ & _);
    apply check_ret_only_ok_iff in other_ok as (-> & _ & _);
    exact refused in
  if_cond ed_ok grows; [fixed_answer tt|];
  if_cond ed_ok off_page; [fixed_answer tt|];
  if_cond ed_ok empty_len; [fixed_answer tt|];
  if_cond ed_ok wraps; [fixed_answer tt|].
  if_cond ed_ok not_modeled; [discriminate ed_ok|].
  cbv zeta in ed_ok |- *.
  if_cond ed_ok protected.
  - destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, unmaps, copies, reads; try discriminate ed_ok.
    cbv iota in ed_ok |- *. cbn [eff_ret].
    if_cond ed_ok listed.
    + if_cond ed_ok no_zeros; [|discriminate ed_ok].
      apply w_nilb_true in no_zeros as ->.
      destruct (mprotect_refusable m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
        eqn:refusable; [|discriminate listed].
      change (errno_ret_in mprotect_errnos ret = true) in listed.
      rewrite listed. split; [exact ed_ok|].
      intros _ other m2 evs2 other_ok.
      destruct other as [r2 w2 z2 u2 c2 i2]; cbn [eff_ret].
      destruct w2, u2, c2, i2; try discriminate other_ok.
      cbv iota in other_ok.
      if_cond other_ok other_refused; [reflexivity|].
      if_cond other_ok other_grant; [|discriminate other_ok].
      apply andb_prop in other_grant as [other_grant _].
      apply andb_prop in other_grant as [other_budget _].
      unfold mprotect_refusable in refusable. rewrite other_budget in refusable.
      discriminate refusable.
    + if_cond ed_ok granted; [|discriminate ed_ok].
      apply andb_prop in granted as [granted zeros_match].
      apply andb_prop in granted as [budget_ok answer_zero].
      clear budget_ok zeros_match.
      unfold w_is0 in answer_zero. apply bv_eqb_eq in answer_zero as ->.
      rewrite zero_not_mprotect_errno.
      split; [exact ed_ok|].
      intros refused.
      discriminate (eq_trans (eq_sym refused) zero_not_mprotect_errno).
  - if_cond ed_ok open_range; [|discriminate ed_ok].
    destruct eff as [ret writes zeros unmaps copies reads].
    destruct writes, zeros, unmaps, copies, reads; try discriminate ed_ok.
    cbv iota in ed_ok |- *. cbn [eff_ret].
    if_cond ed_ok answer_zero; [|discriminate ed_ok].
    unfold w_is0 in answer_zero. apply bv_eqb_eq in answer_zero as ->.
    split; [exact ed_ok|].
    intros refused.
    discriminate (eq_trans (eq_sym refused) zero_not_mprotect_errno).
Qed.

(* [comment removed for export] *)
Lemma forced_of_ns_mmap : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  forced_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff.
Proof.
  intros i m eff Hno Hns Hr eff2 m2 evs2 H2.
  change (errno_ret_in mmap_errnos (eff_ret eff2)) with (ret_in_errnos mmap_errnos (eff_ret eff2)).
  rewrite <- (refusal_b_222 i m (eff_ret eff2) Hno).
  apply (nonspurious_refusal_no_grant ACFG i m eff Hns (acfg_family_off_222 i Hno)) with (m' := m2) (evs' := evs2).
  - rewrite (refusal_b_222 i m (eff_ret eff) Hno). exact Hr.
  - apply check_syscall_ok_iff. rewrite (check_syscall_mmap i eff2 m Hno). exact H2.
Qed.

Lemma ns_of_forced_mmap : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  forced_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff is_mmap forced (_ & refused & other & m_other & evs_other & spec_allows & granted).
  rewrite (refusal_b_222 i m _ is_mmap) in granted.
  rewrite (refusal_b_222 i m _ is_mmap) in refused.
  apply check_syscall_ok_iff in spec_allows.
  rewrite (check_syscall_mmap i other m is_mmap) in spec_allows.
  exact (eq_true_false_abs _ (forced refused other m_other evs_other spec_allows) granted).
Qed.

Lemma forced_of_ns_mprotect : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  forced_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) m eff.
Proof.
  intros i m eff Hno Hns Hr eff2 m2 evs2 H2.
  change (errno_ret_in mprotect_errnos (eff_ret eff2)) with (ret_in_errnos mprotect_errnos (eff_ret eff2)).
  rewrite <- (refusal_b_226 i m (eff_ret eff2) Hno).
  apply (nonspurious_refusal_no_grant ACFG i m eff Hns (acfg_family_off_226 i Hno)) with (m' := m2) (evs' := evs2).
  - rewrite (refusal_b_226 i m (eff_ret eff) Hno). exact Hr.
  - apply check_syscall_ok_iff. rewrite (check_syscall_mprotect i eff2 m Hno). exact H2.
Qed.

Lemma ns_of_forced_mprotect : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  forced_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) m eff ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff is_mprotect forced spurious.
  destruct spurious as (_ & refused & other & m_other & evs_other & spec_allows & granted).
  rewrite (refusal_b_226 i m _ is_mprotect) in refused.
  rewrite (refusal_b_226 i m _ is_mprotect) in granted.
  rewrite <- check_syscall_ok_iff, (check_syscall_mprotect i other m is_mprotect) in spec_allows.
  pose proof (forced refused other m_other evs_other spec_allows) as still_refused.
  change (ret_in_errnos mprotect_errnos (eff_ret other) = true) in still_refused.
  congruence.
Qed.

(* [comment removed for export] *)
Lemma check_mmap_ed_of_ns : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 222%Z ->
  check_syscall i eff m = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  mmap_corner_free (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 5) m eff ->
  check_mmap_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m = CheckOk m' evs.
Proof.
  intros i m eff m' evs Hno Hc Hns Hcf. rewrite (check_syscall_mmap i eff m Hno) in Hc.
  apply check_mmap_ed_fwd; [exact Hc| apply forced_of_ns_mmap; assumption| exact Hcf].
Qed.

Lemma ns_of_check_mmap_ed : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 222%Z ->
  check_mmap_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m = CheckOk m' evs ->
  check_syscall i eff m = CheckOk m' evs /\ ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff m' evs Hno H. destruct (check_mmap_ed_bwd _ _ _ _ _ _ _ _ _ _ H) as [Hc Hf].
  split; [rewrite (check_syscall_mmap i eff m Hno); exact Hc| apply ns_of_forced_mmap; assumption].
Qed.

Lemma check_mprotect_ed_of_ns : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 226%Z ->
  check_syscall i eff m = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  check_mprotect_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m = CheckOk m' evs.
Proof.
  intros i m eff m' evs Hno Hc Hns. rewrite (check_syscall_mprotect i eff m Hno) in Hc.
  apply check_mprotect_ed_fwd; [exact Hc| apply forced_of_ns_mprotect; assumption].
Qed.

Lemma ns_of_check_mprotect_ed : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 226%Z ->
  check_mprotect_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m = CheckOk m' evs ->
  check_syscall i eff m = CheckOk m' evs /\ ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff m' evs Hno H. destruct (check_mprotect_ed_bwd _ _ _ _ _ _ _ H) as [Hc Hf].
  split; [rewrite (check_syscall_mprotect i eff m Hno); exact Hc| apply ns_of_forced_mprotect; assumption].
Qed.

(* [comment removed for export] *)
Lemma mmap_corner_free_not_rw : forall addr len prot flags off m eff,
  mmap_fixed_rw_b prot flags off = false -> mmap_corner_free addr len prot flags off m eff.
Proof. intros addr len prot flags off m eff H H'. congruence. Qed.
