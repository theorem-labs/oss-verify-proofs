(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Dispatch Mm.Mmap Mm.Mremap Mm.Mprotect.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.LimSim Require Import LimSim LimSimMm LimSimMv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope.
Set Default Proof Mode "Classic".

Lemma nwr_cons : forall (a n : word) P, bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> nwr P -> nwr ((a, n) :: P).
Proof. intros a n P H HP. constructor; [unfold phi, plo, psz; cbn [fst snd]; exact H | exact HP]. Qed.

(* [comment removed for export] *)
Lemma brk_model_next_WF : forall m req r,
  brk_r_ok m req r = true -> nwr (vm_maps (m_vmmaps m)) -> nwr (vm_maps (brk_model_next (m_vmmaps m) req r)).
Proof.
  intros m req r Hok Hwf. set (h := m_vmmaps m) in *.
  unfold brk_model_next, brk_maps_next. cbn [vm_maps].
  pose proof (word_range r). pose proof (word_range (vm_brk h)).
  destruct (Z.ltb 0 (bv_unsigned (vm_brk h)) && Z.ltb (bv_unsigned r) (bv_unsigned (vm_brk h))) eqn:Eshrink.
  - apply andb_true_iff in Eshrink as [_ Hlt]. apply Z.ltb_lt in Hlt. apply nwr_maps_subtract; try lia. exact Hwf.
  - unfold brk_grants. destruct (brk_is_grow req r (vm_brk h)) eqn:Egrow; cbn [app]; [|exact Hwf].
    unfold brk_is_grow in Egrow. apply andb_true_iff in Egrow as [Egrow Hlt]. apply Z.ltb_lt in Hlt.
    apply nwr_cons; [|exact Hwf].
    rewrite bv_sub_unsigned. rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma check_brk_WF : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> WF m -> WF m'.
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
  unfold WF. rewrite vmm_brk_next. now apply brk_model_next_WF.
Qed.

Lemma check_munmap_WF : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  WF m -> WF m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_munmap in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-.
    unfold WF. rewrite vmm_mmap_destroyed. cbn [vm_maps].
    now apply nwr_filter.
  - dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|discriminate].
Qed.

Lemma check_mprotect_WF : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  WF m -> WF m'.
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
      unfold WF. rewrite vmm_mprotect_next. cbn [vm_maps]. exact Hwf.
  - dif H; [|discriminate].
    destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hwf.
Qed.

Lemma check_mmap_WF : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  WF m -> WF m'.
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
  (* [comment removed for export] *)
  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct zs; [|discriminate]. injection H as <- <-. exact Hwf. }
    (* [comment removed for export] *)
    difn H E; [|discriminate]. injection H as <- <-.
    unfold WF. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hzs].
    apply andb_true_iff in E as [E Hbud].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply nwr_cons; [rewrite u64 by lia; lia | exact Hwf]. }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct us; [|discriminate]. injection H as <- <-. exact Hwf. }
    (* [comment removed for export] *)
    difn H E; [|discriminate]. injection H as <- <-.
    unfold WF. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hus].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply nwr_cons; [rewrite u64 by lia; lia | exact Hwf]. }
  (* [comment removed for export] *)
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
          unfold WF. rewrite vmm_mmap_destroyed. cbn [vm_maps].
          apply nwr_maps_subtract; try (rewrite u64 by lia); try lia. exact Hwf.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold WF. rewrite vmm_mmap_replacement, vmm_vmmaps. cbn [vm_maps].
        exact Hwf.
    - difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us; [|discriminate]. injection H as <- <-. exact Hwf.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold WF. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply nwr_cons; [rewrite u64 by lia; lia | exact Hwf].
      (* [comment removed for export] *)
      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us.
          -- injection H as <- <-. exact Hwf.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             unfold WF. rewrite vmm_mmap_destroyed. cbn [vm_maps].
             apply nwr_maps_subtract; try (rewrite u64 by lia); try lia.
             exact Hwf.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold WF. rewrite vmm_mmap_replacement, vmm_vmmaps.
          cbn [vm_maps mmap_fixed_noaccess_span_next].
          apply nwr_cons; [rewrite u64 by lia; lia | apply nwr_maps_subtract; try (rewrite u64 by lia); try lia; exact Hwf]. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {
    (* [comment removed for export] *)
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
          unfold WF. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply nwr_cons; [rewrite u64 by lia; lia | exact Hwf].
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
        unfold WF. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply nwr_cons; [rewrite u64 by lia; lia | exact Hwf].
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
        unfold WF. rewrite vmm_mmap_destroyed. cbn [vm_maps].
        apply nwr_maps_subtract; try (rewrite u64 by lia); try lia. exact Hwf.
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold WF. rewrite vmm_mmap_replacement, vmm_vmmaps.
      rewrite vmm_fixed_rw_next. exact Hwf.
  - difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        unfold WF. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply nwr_cons; [rewrite u64 by lia; lia | exact Hwf].
    (* [comment removed for export] *)
    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. exact Hwf.
        -- difn H Eus; [|discriminate]. injection H as <- <-.
           unfold WF. rewrite vmm_mmap_destroyed. cbn [vm_maps].
           apply nwr_maps_subtract; try (rewrite u64 by lia); try lia.
           exact Hwf.
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold WF. rewrite vmm_mmap_replacement, vmm_vmmaps.
        cbn [vm_maps mmap_fixed_rw_span_next].
        apply nwr_cons; [rewrite u64 by lia; lia | apply nwr_maps_subtract; try (rewrite u64 by lia); try lia; exact Hwf].
Qed.

Lemma check_mremap_WF : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  WF m -> WF m'.
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
  (* [comment removed for export] *)
  unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 EnewB].
  apply Z.leb_gt in EnewB.
  pose proof (w_is0_false new_size Enew0) as Hnew0.
  assert (HnewZ : 0 < page_round_up_Z (bv_unsigned new_size))
    by (apply page_round_up_pos; lia).
  (* [comment removed for export] *)
  apply negb_false_iff in Esrc.
  (* [comment removed for export] *)
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
      unfold WF. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      apply nwr_cons; [rewrite u64 by lia; lia | unfold map_remove; now apply nwr_filter].
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold WF. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
      apply andb_true_iff in Egrow as [Egrow _].
      apply andb_true_iff in Egrow as [Hgceil Hgfree].
      apply Z.leb_le in Hgceil.
      apply nwr_cons; [rewrite u64 by lia; lia | now apply nwr_filter].
  - difn H Emove; [|discriminate]. injection H as <- <-.
    unfold WF. rewrite vmm_mremap_next.
    unfold mremap_maps_next. cbn [vm_maps].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [_ Hfresh].
    (* [comment removed for export] *)
    unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [Hfresh Hffree].
    apply andb_true_iff in Hfresh as [Hfresh Hfceil].
    apply andb_true_iff in Hfresh as [_ Hfpos].
    apply Z.leb_le in Hfceil. apply Z.ltb_lt in Hfpos.
    apply nwr_cons; [rewrite u64 by lia; lia | now apply nwr_filter].
Qed.

(* [comment removed for export] *)
Definition arm_preserves_WF (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> WF m -> WF m'.

Lemma checked_table_preserves_WF : Forall arm_preserves_WF checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_WF).
  all: unfold arm_preserves_WF, WF; intros i eff m m' evs H Hwf;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_WF; eassumption
    | eapply check_mmap_WF; eassumption
    | eapply check_munmap_WF; eassumption
    | eapply check_mremap_WF; eassumption
    | eapply check_mprotect_WF; eassumption
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
    | fail 1 "checked_table_preserves_WF has no case for this dispatcher arm: give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves one (it writes vm_maps), and add it to the list above" ].
Qed.

Theorem syscall_spec_preserves_WF : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> WF m -> WF m'.
Proof.
  intros i m eff m' evs H Hwf. apply check_syscall_ok_iff in H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk; [|discriminate H].
  pose proof checked_table_preserves_WF as Hall. rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hwf).
Qed.

(* [comment removed for export] *)
Lemma materialize_WF : forall m acc m', materialize_model_accesses m acc = Some m' -> WF m -> WF m'.
Proof. intros m acc m' H Hwf. unfold WF. destruct (materialize_model_accesses_frame m acc m' H) as (_ & E & _). rewrite E. exact Hwf. Qed.

Section Run.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_cfg_WF : forall c evs c', sstep_cfg segs cfg c evs (SNext c') -> WF (cfg_model c) -> WF (cfg_model c').
Proof.
  intros c evs c' Hs. remember (SNext c') as st eqn:Est.
  destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
                 | ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
    try discriminate Est; injection Est as E; subst c'; cbn [cfg_model]; intros Hwf.
  - unfold mi_account_step in Ha. destruct (step_accesses segs ms0) as [report| |]; [|discriminate|discriminate].
    destruct (materialize_model_accesses mm (@accessed_ranges _ report)) as [m1|] eqn:Emat; [|discriminate]. injection Ha as <- <-.
    exact (materialize_WF _ _ _ Emat Hwf).
  - exact (materialize_WF _ _ _ Hmat (syscall_spec_preserves_WF _ _ _ _ _ Hsp Hwf)).
  - exact (syscall_spec_preserves_WF _ _ _ _ _ Hsp Hwf).
  - exact (syscall_spec_preserves_WF _ _ _ _ _ Hsp Hwf).
Qed.

Lemma star_cfg_WF : forall c tr c', star_cfg segs cfg c tr c' -> WF (cfg_model c) -> WF (cfg_model c').
Proof. intros c tr c' H. induction H as [c0 | c1 evs c2 tr2 c3 Hs Hstar IH]; intros Hwf; [exact Hwf|]. apply IH. exact (sstep_cfg_WF _ _ _ Hs Hwf). Qed.
End Run.

Lemma init_config_WF : forall segs pc ph sp brk0 mbase rnd lim inp, WF (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)).
Proof. intros. unfold WF. cbn. constructor. Qed.
