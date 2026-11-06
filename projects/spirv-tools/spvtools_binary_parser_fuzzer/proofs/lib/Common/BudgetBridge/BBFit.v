(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition fitl (l : list (word * word)) : Prop :=
  forall (a sz : word), In (a, sz) l -> bv_unsigned a + bv_unsigned sz <= two_pow_64.
Definition vm_fit (h : VmMaps) : Prop := fitl (vm_maps h).

Lemma fit_cons_free : forall maps (a n : word),
  fitl maps -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> region_free maps a n = true -> fitl ((a, n) :: maps).
Proof. intros maps a n H Hn _ b s [E|Hin]; [inversion E; subst; unfold two_pow_64; lia | exact (H b s Hin)]. Qed.

Lemma fit_cons : forall maps (a n : word),
  fitl maps -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> fitl ((a, n) :: maps).
Proof. intros maps a n H Hn b s [E|Hin]; [inversion E; subst; unfold two_pow_64; lia | exact (H b s Hin)]. Qed.

Lemma fit_subtract : forall maps lo hi, 0 <= lo -> lo <= hi -> hi < 2 ^ 64 -> fitl maps -> fitl (maps_subtract maps lo hi).
Proof.
  intros maps lo hi _ _ _ H b s Hin.
  destruct (maps_subtract_In maps lo hi b s Hin) as [a [sz [Hin0 Hiv]]].
  pose proof (iv_subtract_within a sz lo hi b s (H a sz Hin0) Hiv). pose proof (H a sz Hin0). lia.
Qed.

Lemma fit_filter : forall f maps, fitl maps -> fitl (List.filter f maps).
Proof. intros f maps H b s Hin. apply filter_In in Hin. exact (H b s (proj1 Hin)). Qed.

Lemma fit_cons_sub : forall maps (a n0 n : word),
  fitl maps -> bv_unsigned n <> 0 -> In (a, n0) maps -> bv_unsigned n <= bv_unsigned n0 ->
  fitl ((a, n) :: map_remove maps a).
Proof.
  intros maps a n0 n H _ Hin Hle b s [E|Hin'].
  - inversion E; subst. pose proof (H b n0 Hin). lia.
  - unfold map_remove in Hin'. apply filter_In in Hin'. exact (H b s (proj1 Hin')).
Qed.

Lemma brk_model_next_fit : forall m req r,
  brk_r_ok m req r = true -> vm_fit (m_vmmaps m) ->
  vm_fit (brk_model_next (m_vmmaps m) req r).
Proof.
  intros m req r Hok Hwf. set (h := m_vmmaps m) in *.
  unfold vm_fit, brk_model_next, brk_maps_next. cbn [vm_maps].
  destruct (Z.ltb 0 (bv_unsigned (vm_brk h))
            && Z.ltb (bv_unsigned r) (bv_unsigned (vm_brk h))) eqn:Eshrink.
  - apply andb_true_iff in Eshrink as [_ Hlt]. apply Z.ltb_lt in Hlt.
    pose proof (word_range r). pose proof (word_range (vm_brk h)).
    apply fit_subtract; try lia. exact Hwf.
  - unfold brk_grants. destruct (brk_is_grow req r (vm_brk h)) eqn:Egrow.
    + cbn [app]. unfold brk_is_grow in Egrow.
      apply andb_true_iff in Egrow as [_ Hlt]. apply Z.ltb_lt in Hlt.
      pose proof (word_range r) as Hr. pose proof (word_range (vm_brk h)) as Hb.
      assert (Hsz : bv_unsigned (r - vm_brk h)%bv = bv_unsigned r - bv_unsigned (vm_brk h)).
      { rewrite bv_sub_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
      apply fit_cons; [exact Hwf | rewrite Hsz; lia].
    + cbn [app]. exact Hwf.
Qed.

Lemma check_brk_fit : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct ci as [|? ?]; [|discriminate].
  destruct (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (vm_brk (m_vmmaps m)))
            && listNN_eqb us (brk_unmaps ret (vm_brk (m_vmmaps m)))) eqn:E;
    [|discriminate].
  injection H as <- <-.
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
  rewrite vmm_brk_next. now apply brk_model_next_fit.
Qed.
Lemma check_munmap_fit : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_munmap in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
    now apply fit_filter.
  - dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|discriminate].
Qed.
Lemma check_mprotect_fit : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_mprotect in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [discriminate|].
  dif H.
  - destruct ws, us, cs, ci; try discriminate.
    dif H.
    + destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
    + dif H; [|discriminate]. injection H as <- <-.
      unfold vm_fit. rewrite vmm_mprotect_next. cbn [vm_maps]. exact Hwf.
  - dif H; [|discriminate].
    destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hwf.
Qed.
Lemma check_mmap_fit : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_mmap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range len) as Hlenr.
  pose proof (word_range addr) as Haddrr.
  destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
  { destruct (mmap_pglen_ok_b len); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hwf. }
  destruct (negb (mmap_anon_b flags)) eqn:Eanon; [discriminate|].
  destruct (w_is0 len) eqn:Elen.
  { destruct (mmap_plain_anon_b flags); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hwf. }
  pose proof (w_is0_false len Elen) as Hlen0.
  assert (HnZ : 0 < page_round_up_Z (bv_unsigned len))
    by (apply page_round_up_pos; lia).

  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct zs; [|discriminate]. injection H as <- <-. exact Hwf. }

    difn H E; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hzs].
    apply andb_true_iff in E as [E Hbud].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply fit_cons_free.
    - exact Hwf.
    - rewrite u64 by lia. lia.
    - exact (region_free_app_r _ _ _ _ Hfree). }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct us; [|discriminate]. injection H as <- <-. exact Hwf. }

    difn H E; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hus].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply fit_cons_free.
    - exact Hwf.
    - rewrite u64 by lia. lia.
    - exact (region_free_app_r _ _ _ _ Hfree). }

  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
  { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Elive.
    - destruct ws, zs, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct us.
        * injection H as <- <-. exact Hwf.
        * difn H Eus; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
          apply fit_subtract; try (rewrite u64 by lia); try lia. exact Hwf.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps. cbn [vm_maps].
        exact Hwf.
    - difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us; [|discriminate]. injection H as <- <-. exact Hwf.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply fit_cons_free.
          -- exact Hwf.
          -- rewrite u64 by lia. lia.
          -- exact (region_free_app_r _ _ _ _ Efree).

      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us.
          -- injection H as <- <-. exact Hwf.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
             apply fit_subtract; try (rewrite u64 by lia); try lia.
             exact Hwf.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps.
          cbn [vm_maps mmap_fixed_noaccess_span_next].
          apply fit_cons_free.
          -- apply fit_subtract; try (rewrite u64 by lia); try lia.
             exact Hwf.
          -- rewrite u64 by lia. lia.
          -- apply maps_subtract_region_free. rewrite u64 by lia. lia. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {

    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
    { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Efree.
      - destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct us; [|discriminate]. injection H as <- <-. exact Hwf.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply fit_cons_free.
          * exact Hwf.
          * rewrite u64 by lia. lia.
          * exact (region_free_app_r _ _ _ _ Efree).
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. exact Hwf. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
    difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Efree.
    - destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply fit_cons_free.
        * exact Hwf.
        * rewrite u64 by lia. lia.
        * exact (region_free_app_r _ _ _ _ Efree).
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. exact Hwf. }
  difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  difn H Elive.
  - destruct ws, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    + destruct zs; [|discriminate]. destruct us.
      * injection H as <- <-. exact Hwf.
      * difn H Eus; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
        apply fit_subtract; try (rewrite u64 by lia); try lia. exact Hwf.
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps.
      rewrite vmm_fixed_rw_next. exact Hwf.
  - difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply fit_cons_free.
        -- exact Hwf.
        -- rewrite u64 by lia. lia.
        -- exact (region_free_app_r _ _ _ _ Efree).

    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. exact Hwf.
        -- difn H Eus; [|discriminate]. injection H as <- <-.
           unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
           apply fit_subtract; try (rewrite u64 by lia); try lia.
           exact Hwf.
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps.
        cbn [vm_maps mmap_fixed_rw_span_next].
        apply fit_cons_free.
        -- apply fit_subtract; try (rewrite u64 by lia); try lia.
           exact Hwf.
        -- rewrite u64 by lia. lia.
        -- apply maps_subtract_region_free. rewrite u64 by lia. lia.
Qed.
Lemma check_mremap_fit : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_mremap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range old) as Hor.
  pose proof (word_range old_size) as Hos.
  pose proof (word_range new_size) as Hns.
  difn H Eflag; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Enew; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Eold; [discriminate|].
  difn H Esrc; [discriminate|].
  difn H Eeq; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  destruct ws; [|discriminate]. destruct ci; [|discriminate].

  unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 EnewB].
  apply Z.leb_gt in EnewB.
  pose proof (w_is0_false new_size Enew0) as Hnew0.
  assert (HnewZ : 0 < page_round_up_Z (bv_unsigned new_size))
    by (apply page_round_up_pos; lia).

  apply negb_false_iff in Esrc.

  apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  apply andb_true_iff in Esrc as [Esrc Hhas].
  apply andb_true_iff in Esrc as [Hoceil _].
  apply Z.leb_le in Hoceil.
  assert (HoldZ : 0 <= page_round_up_Z (bv_unsigned old_size))
    by (apply page_round_up_Z_nonneg; lia).
  destruct (errno_ret_in mremap_errnos ret).
  { destruct zs, us, cs; try discriminate. injection H as <- <-. exact Hwf. }
  destruct (bv_eqb ret old).
  - difn H Eshrink.
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply Z.ltb_lt in Eshrink.
      unfold vm_fit. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      apply (fit_cons_sub _ _ (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))).
      * exact Hwf.
      * rewrite u64 by lia. lia.
      * apply map_has_In. exact Hhas.
      * rewrite !u64 by lia. lia.
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold vm_fit. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
      apply andb_true_iff in Egrow as [Egrow _].
      apply andb_true_iff in Egrow as [Hgceil Hgfree].
      apply Z.leb_le in Hgceil.
      apply fit_cons_free.
      * now apply fit_filter.
      * rewrite u64 by lia. lia.
      * exact (region_free_app_r _ _ _ _ Hgfree).
  - difn H Emove; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mremap_next.
    unfold mremap_maps_next. cbn [vm_maps].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [_ Hfresh].

    unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [Hfresh Hffree].
    apply andb_true_iff in Hfresh as [Hfresh Hfceil].
    apply andb_true_iff in Hfresh as [_ Hfpos].
    apply Z.leb_le in Hfceil. apply Z.ltb_lt in Hfpos.
    apply fit_cons_free.
    + now apply fit_filter.
    + rewrite u64 by lia. lia.
    + apply region_free_filter. exact (region_free_app_r _ _ _ _ Hffree).
Qed.

Definition arm_preserves_fit (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').

Lemma checked_table_preserves_fit : Forall arm_preserves_fit checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_fit).
  all: unfold arm_preserves_fit; intros i eff m m' evs H Hwf;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_fit; eassumption
    | eapply check_mmap_fit; eassumption
    | eapply check_munmap_fit; eassumption
    | eapply check_mremap_fit; eassumption
    | eapply check_mprotect_fit; eassumption
    | erewrite check_madvise_frame by eassumption; exact Hwf
    | erewrite check_read_frame by eassumption; exact Hwf
    | erewrite check_write_frame by eassumption; exact Hwf
    | erewrite check_pread64_frame by eassumption; exact Hwf
    | erewrite check_pwrite64_frame by eassumption; exact Hwf
    | erewrite check_readv_frame by eassumption; exact Hwf
    | erewrite check_writev_frame by eassumption; exact Hwf
    | erewrite check_openat_frame by eassumption; exact Hwf
    | erewrite check_close_frame by eassumption; exact Hwf
    | erewrite check_lseek_frame by eassumption; exact Hwf
    | erewrite check_ftruncate_frame by eassumption; exact Hwf
    | erewrite check_ioctl_frame by eassumption; exact Hwf
    | erewrite check_readlinkat_frame by eassumption; exact Hwf
    | erewrite check_wait4_frame by eassumption; exact Hwf
    | erewrite check_fsync_frame by eassumption; exact Hwf
    | erewrite check_getdents64_frame by eassumption; exact Hwf
    | erewrite check_flock_frame by eassumption; exact Hwf
    | erewrite check_exit_frame by eassumption; exact Hwf
    | erewrite check_set_tid_address_frame by eassumption; exact Hwf
    | erewrite check_getpid_frame by eassumption; exact Hwf
    | erewrite check_gettid_frame by eassumption; exact Hwf
    | erewrite check_setsid_frame by eassumption; exact Hwf
    | erewrite check_uname_frame by eassumption; exact Hwf
    | erewrite check_prctl_frame by eassumption; exact Hwf
    | erewrite check_prlimit64_frame by eassumption; exact Hwf
    | erewrite check_getrandom_frame by eassumption; exact Hwf
    | erewrite check_gettimeofday_frame by eassumption; exact Hwf
    | erewrite check_clock_gettime_frame by eassumption; exact Hwf
    | erewrite check_nanosleep_frame by eassumption; exact Hwf
    | erewrite check_dup_frame by eassumption; exact Hwf
    | erewrite check_dup3_frame by eassumption; exact Hwf
    | erewrite check_unlinkat_frame by eassumption; exact Hwf
    | erewrite check_faccessat_frame by eassumption; exact Hwf
    | erewrite check_faccessat2_frame by eassumption; exact Hwf
    | erewrite check_pselect6_frame by eassumption; exact Hwf
    | erewrite check_ppoll_frame by eassumption; exact Hwf
    | erewrite check_newfstatat_frame by eassumption; exact Hwf
    | erewrite check_fstat_frame by eassumption; exact Hwf
    | erewrite check_getid_frame by eassumption; exact Hwf
    | erewrite check_setid_frame by eassumption; exact Hwf
    | erewrite check_setresid_frame by eassumption; exact Hwf
    | erewrite check_getgroups_frame by eassumption; exact Hwf
    | erewrite check_setgroups_frame by eassumption; exact Hwf
    | erewrite check_socket_frame by eassumption; exact Hwf
    | erewrite check_bind_frame by eassumption; exact Hwf
    | erewrite check_listen_frame by eassumption; exact Hwf
    | erewrite check_accept4_frame by eassumption; exact Hwf
    | erewrite check_fcntl_frame by eassumption; exact Hwf
    | erewrite check_sched_setscheduler_frame by eassumption; exact Hwf
    | erewrite check_sched_getaffinity_frame by eassumption; exact Hwf
    | erewrite check_sched_yield_frame by eassumption; exact Hwf
    | erewrite check_sigaltstack_frame by eassumption; exact Hwf
    | erewrite check_rt_sigaction_frame by eassumption; exact Hwf
    | erewrite check_tkill_frame by eassumption; exact Hwf
    | erewrite check_tgkill_frame by eassumption; exact Hwf
    | erewrite check_rt_sigprocmask_frame by eassumption; exact Hwf
    | erewrite check_futex_frame by eassumption; exact Hwf
    | erewrite check_clone_frame by eassumption; exact Hwf
    | erewrite check_clone3_frame by eassumption; exact Hwf
    | erewrite check_getsockname_frame by eassumption; exact Hwf
    | erewrite check_getpeername_frame by eassumption; exact Hwf
    | erewrite check_setsockopt_frame by eassumption; exact Hwf
    | erewrite check_getsockopt_frame by eassumption; exact Hwf
    | erewrite check_shutdown_frame by eassumption; exact Hwf
    | erewrite check_sendto_frame by eassumption; exact Hwf
    | erewrite check_sendmsg_frame by eassumption; exact Hwf
    | erewrite check_socketpair_frame by eassumption; exact Hwf
    | erewrite check_recvfrom_frame by eassumption; exact Hwf
    | erewrite check_recvmsg_frame by eassumption; exact Hwf
    | erewrite check_connect_frame by eassumption; exact Hwf
    | erewrite check_timerfd_create_frame by eassumption; exact Hwf
    | erewrite check_eventfd2_frame by eassumption; exact Hwf
    | erewrite check_pipe2_frame by eassumption; exact Hwf
    | erewrite check_getcwd_frame by eassumption; exact Hwf
    | erewrite check_epoll_create1_frame by eassumption; exact Hwf
    | erewrite check_epoll_ctl_frame by eassumption; exact Hwf
    | erewrite check_epoll_pwait_frame by eassumption; exact Hwf
    | fail 1 "check_syscall_fit_vm_wf has no case for this dispatcher arm: give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves one (it writes vm_maps), and add it to the list above" ].
Qed.

Theorem check_syscall_preserves_fit : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros i eff m m' evs H Hwf. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk; [|discriminate H].
  pose proof checked_table_preserves_fit as Hall. rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hwf).
Qed.

Corollary syscall_spec_preserves_fit : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros i m eff m' evs H Hwf. eapply check_syscall_preserves_fit; [|exact Hwf].
  apply check_syscall_ok_iff. exact H.
Qed.

