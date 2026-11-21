(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the WF preservation proofs follow the new checks: brk grants and cuts as page ranges, munmap and mremap via maps_subtract, place_declined_b and linux_place_is on freely placed mmap, the mprotect vDSO/vvar gate, fixed-mmap overflow, new syscall arms and the vDSO arms of sstep_cfg). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Common/LimSim/LimSimWf.v; 337 of its 510 lines of code are new or changed and 292 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/Common/LimSim/LimSimWf.v, lines 5-24, 53-490 and 508, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): no entry of the mapping ledger [vm_maps] meets the window
   [vlo, vhi) ([maps_off]), kept by every system call the specification admits and by every step
   of the run relation, from a model where the window sits inside an entry of the launch's
   vDSO/vvar pair, which is in the reserved ledger ([MmVdso.mm_vinv]).

   The whole-table walk is the model's own (Checks/NoaccessOwned.v [checked_table_preserves_na]
   and [check_syscall_preserves_sys_inv]): [check_syscall_complete_ok]
   (Checks/ExecutableSpecs.v:132) turns an outcome of [Specs.syscall_spec] into an accepted checker
   call; [lookup_ca_In] and [arm_unfold] reach the arm's checker.  Every arm that does not write
   [vm_maps] keeps [m_vmmaps] by its [check_*_frame] (Checks/VmMapsDisjoint.v and the checkers'
   modules); [check_mprotect] keeps the [vm_maps] list itself ([vmm_mprotect_next]).  The four
   writers walk their checker as [VmMapsDisjoint.check_*_preserves] does, and each new entry of
   the ledger is one of:
     - a remnant of a cut ([maps_subtract], [brk_unmap_cut]): inside an old entry
       ([VmMapsDisjoint.maps_subtract_inside]), so off the window when that entry was
       ([mo_subtract]);
     - a grant the checker tested [region_free] against [vm_reserved ++ vm_maps] (the placement
       search, [Placement.linux_place_is_admissible], Checks/Placement.v:1038; the MAP_FIXED and
       MAP_FIXED_NOREPLACE free arms, Checks/Sys/Mm/Mmap.v:202, 289; the mremap move,
       [Mremap.mremap_fresh_b]) or against [vm_reserved ++ (a cut of vm_maps)] (the mremap grow
       in place, [Mremap.mremap_inplace_room_b]) or against [vm_reserved] alone (the MAP_FIXED
       spanning arms, Checks/Sys/Mm/Mmap.v:223, 311; the mremap source, [Mremap.mremap_source_b],
       which bounds the mremap shrink): such a range misses the reserved entry holding the
       window, so it misses the window ([MmVdso.off_of_free]);
     - the brk grant, whose gate tests one page more ([MmVdso.grow_zeros_off]: [brk_grants] and
       [brk_zeros] are the same list, Sys/Mm/Mmap.v:198-215).
   [mo_step] takes a step of [Run.sstep_cfg] (Run.v:2250-2342): the first-touch accounting keeps
   [m_vmmaps] ([Run.mi_account_step_model_frame]), so does the materialization after a call
   ([State.materialize_model_accesses_frame]) and the vDSO call count
   ([State.m_vmmaps_with_vdso_bump]); the call itself is [mo_spec_ok] at the step's input. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Placement VmMapsDisjoint.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MmVdso.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MapsOff.
  Variables vlo vhi : Z.

  (** No entry of the mapping ledger meets the window. *)
  Definition maps_off (mo : Model) : Prop :=
    Forall (VdsoClean.range_off vlo vhi) (vm_maps (m_vmmaps mo)).

  (** * The ledger shapes *)

  Lemma mo_frame : forall m m', m_vmmaps m' = m_vmmaps m -> maps_off m -> maps_off m'.
  Proof. intros m m' E H. unfold maps_off in *. rewrite E. exact H. Qed.

  Lemma mo_maps_eq : forall m m', vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m) ->
    maps_off m -> maps_off m'.
  Proof. intros m m' E H. unfold maps_off in *. rewrite E. exact H. Qed.

  (** A cut leaves remnants inside the entries it came from. *)
  Lemma mo_subtract : forall l lo hi, 0 <= lo -> hi < 2 ^ 64 ->
    Forall (VdsoClean.range_off vlo vhi) l ->
    Forall (VdsoClean.range_off vlo vhi) (maps_subtract l lo hi).
  Proof.
    intros l lo hi Hlo Hhi Hl. rewrite Forall_forall in Hl |- *. intros [b s] Hin.
    destruct (maps_subtract_inside l lo hi b s Hlo Hhi Hin) as (a & sz & Hin0 & W1 & W2).
    specialize (Hl (a, sz) Hin0).
    unfold VdsoClean.range_off in Hl |- *. cbn [fst snd] in Hl |- *. lia.
  Qed.

  (** A range free against the reserved ledger misses the window. *)
  Lemma mo_off_res : forall mo (a n : word), MmVdso.mm_vinv vlo vhi mo ->
    region_free (vm_reserved (m_vmmaps mo)) a n = true -> VdsoClean.range_off vlo vhi (a, n).
  Proof.
    intros mo a n VI Hf. unfold MmVdso.mm_vinv, MmVdso.win_in in VI.
    destruct VI as [(r & Hin & Hlo & Hhi) Hinc].
    exact (MmVdso.off_of_free vlo vhi _ a n r Hf (Hinc r Hin) Hlo Hhi).
  Qed.

  (** The same against the reserved ledger and anything after it. *)
  Lemma mo_off_res_app : forall mo l (a n : word), MmVdso.mm_vinv vlo vhi mo ->
    region_free (vm_reserved (m_vmmaps mo) ++ l) a n = true -> VdsoClean.range_off vlo vhi (a, n).
  Proof.
    intros mo l a n VI Hf. unfold MmVdso.mm_vinv, MmVdso.win_in in VI.
    destruct VI as [(r & Hin & Hlo & Hhi) Hinc].
    apply (MmVdso.off_of_free vlo vhi _ a n r Hf); [| exact Hlo | exact Hhi].
    apply in_or_app. left. exact (Hinc r Hin).
  Qed.

  (** * The writers of [vm_maps], walked as [VmMapsDisjoint] walks them *)

  Lemma check_brk_preserves_mo : forall req eff m m' evs,
    check_brk req eff m = CheckOk m' evs ->
    MmVdso.mm_vinv vlo vhi m -> maps_off m -> maps_off m'.
  Proof.
    intros req [ret ws zs us cs ci] m m' evs H VI Hmo.
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
    pose proof (word_range ret) as Hr.
    unfold maps_off. rewrite vmm_brk_next.
    unfold brk_model_next. cbn [vm_maps]. unfold brk_maps_next.
    lazymatch goal with |- Forall _ (if ?b then _ else _) => destruct b eqn:Eshrink end.
    - (* a shrink: the freed pages are cut *)
      change (Forall (VdsoClean.range_off vlo vhi)
                (brk_unmap_cut (vm_maps (m_vmmaps m)) ret (vm_brk (m_vmmaps m)))).
      unfold brk_unmap_cut. cbv zeta.
      lazymatch goal with |- Forall _ (if ?b then _ else _) => destruct b eqn:Ep end.
      + change (Forall (VdsoClean.range_off vlo vhi)
                  (maps_subtract (vm_maps (m_vmmaps m)) (page_round_up_Z (bv_unsigned ret))
                     (Z.min (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m))))
                            (two_pow_64 - 1)))).
        apply mo_subtract; [apply page_round_up_Z_nonneg; lia | unfold two_pow_64; lia | exact Hmo].
      + exact Hmo.
    - (* a grow records the pages the grow gate tested ([brk_grants] is [brk_zeros]) *)
      change (Forall (VdsoClean.range_off vlo vhi)
                (brk_grants req ret (vm_brk (m_vmmaps m)) ++ vm_maps (m_vmmaps m))).
      apply Forall_app. split; [| exact Hmo].
      exact (MmVdso.grow_zeros_off vlo vhi m req ret VI E).
  Qed.

  Lemma check_munmap_preserves_mo : forall addr len eff m m' evs,
    check_munmap addr len eff m = CheckOk m' evs ->
    MmVdso.mm_vinv vlo vhi m -> maps_off m -> maps_off m'.
  Proof.
    intros addr len [ret ws zs us cs ci] m m' evs H _ Hmo.
    unfold check_munmap in H. cbv zeta in H.
    dif H; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    difn H Etask; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    dif H.
    - destruct ws, zs, cs, ci; try discriminate.
      dif H.
      + destruct us; [|discriminate]. injection H as <- <-. exact Hmo.
      + dif H; [|discriminate]. injection H as <- <-.
        pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
        apply Z.ltb_ge in Etask. unfold TASK_SIZE in Etask.
        pose proof (page_round_up_Z_ge (bv_unsigned len) ltac:(lia)) as HnZ.
        unfold maps_off. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
        cbn [vm_maps].
        apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
    - dif H; [apply check_ret_only_model in H; subst m'; exact Hmo|].
      dif H; [|discriminate].
      destruct ws, zs, cs, ci; try discriminate.
      dif H.
      + destruct us; [|discriminate]. injection H as <- <-. exact Hmo.
      + dif H; [|discriminate]. injection H as <- <-.
        apply Z.ltb_ge in Etask. unfold TASK_SIZE in Etask.
        pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
        pose proof (page_round_up_Z_ge (bv_unsigned len) ltac:(lia)) as HnZ.
        unfold maps_off. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
        cbn [vm_maps].
        apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
  Qed.

  (** [mprotect] changes [vm_noaccess] only. *)
  Lemma check_mprotect_maps : forall addr len prot eff m m' evs,
    check_mprotect addr len prot eff m = CheckOk m' evs ->
    vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m).
  Proof.
    intros addr len prot [ret ws zs us cs ci] m m' evs H.
    unfold check_mprotect in H. cbv zeta in H.
    dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
    dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
    dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
    dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
    dif H; [discriminate|].
    (* the vdso/vvar gate: a request that meets the pair is unmodeled *)
    dif H; [discriminate|].
    dif H.
    - destruct ws, us, cs, ci; try discriminate.
      dif H.
      + destruct zs; [|discriminate]. injection H as <- <-. reflexivity.
      + dif H; [|discriminate]. injection H as <- <-.
        rewrite vmm_mprotect_next. reflexivity.
    - dif H; [|discriminate].
      destruct ws, zs, us, cs, ci; try discriminate.
      dif H; [|discriminate]. injection H as <- <-. reflexivity.
  Qed.

  Lemma check_mmap_preserves_mo : forall addr len prot flags fd off eff m m' evs,
    check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
    MmVdso.mm_vinv vlo vhi m -> maps_off m -> maps_off m'.
  Proof.
    intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H VI Hmo.
    unfold check_mmap in H. cbv zeta in H.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
    pose proof (word_range len) as Hlenr.
    pose proof (word_range addr) as Haddrr.
    destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
    { apply check_ret_only_model in H; subst m'; exact Hmo. }
    destruct (negb (mmap_anon_b flags)) eqn:Eanon.
    { destruct (fd_lookup (m_fds m) (fd32 fd)); [discriminate|].
      apply check_ret_only_model in H; subst m'; exact Hmo. }
    destruct (w_is0 len) eqn:Elen.
    { destruct (mmap_plain_anon_b flags); [|discriminate].
      apply check_ret_only_model in H; subst m'; exact Hmo. }
    pose proof (w_is0_false len Elen) as Hlen0.
    assert (HnZ : 0 < page_round_up_Z (bv_unsigned len))
      by (apply page_round_up_pos; lia).
    (* the placed shapes: the grant is free against [vm_reserved ++ vm_maps] *)
    destruct (mmap_modeled_b prot flags off) eqn:Emod.
    { destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr
                  (page_round_up_Z (bv_unsigned len))) eqn:Edecl; [discriminate|].
      destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      { destruct zs; [|discriminate]. injection H as <- <-. exact Hmo. }
      difn H E; [|discriminate]. injection H as <- <-.
      unfold maps_off. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
      apply andb_true_iff in E as [E Hzs].
      apply andb_true_iff in E as [Hplace Hbud].
      destruct (linux_place_is_admissible _ _ _ _ _ HnZ
                  (page_round_up_Z_aligned (bv_unsigned len)) Hplace)
        as (Halign & Hpos & Hceil & Hfree).
      apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Hfree) | exact Hmo]. }
    destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
    { destruct (place_declined_b (m_kernel m) (m_vmmaps m) addr
                  (page_round_up_Z (bv_unsigned len))) eqn:Edecl; [discriminate|].
      destruct ws, zs, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      { destruct us; [|discriminate]. injection H as <- <-. exact Hmo. }
      difn H E; [|discriminate]. injection H as <- <-.
      unfold maps_off. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
      apply andb_true_iff in E as [Hplace Hus].
      destruct (linux_place_is_admissible _ _ _ _ _ HnZ
                  (page_round_up_Z_aligned (bv_unsigned len)) Hplace)
        as (Halign & Hpos & Hceil & Hfree).
      apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Hfree) | exact Hmo]. }
    (* MAP_FIXED, PROT_NONE *)
    destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
    { difn H Enomem; [apply check_mmap_fixed_overflow_model in H; subst m'; exact Hmo|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hmo|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Elive.
      - destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct us.
          * injection H as <- <-. exact Hmo.
          * difn H Eus; [|discriminate]. injection H as <- <-.
            unfold maps_off. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
            cbn [vm_maps].
            apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          unfold maps_off. rewrite vmm_mmap_replacement, vmm_vmmaps. cbn [vm_maps].
          exact Hmo.
      - difn H Efree.
        + destruct ws, zs, cs, ci; try discriminate.
          destruct (errno_ret_in mmap_errnos ret).
          * destruct us; [|discriminate]. injection H as <- <-. exact Hmo.
          * difn H Eok; [|discriminate]. injection H as <- <-.
            unfold maps_off. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
            apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Efree) | exact Hmo].
        (* SPANNING: the request, free against [vm_reserved], on the cut ledger *)
        + difn H Espan; [|discriminate].
          destruct ws, zs, cs, ci; try discriminate.
          destruct (errno_ret_in mmap_errnos ret).
          * destruct us.
            -- injection H as <- <-. exact Hmo.
            -- difn H Eus; [|discriminate]. injection H as <- <-.
               unfold maps_off. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
               cbn [vm_maps].
               apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
          * difn H Eok; [|discriminate]. injection H as <- <-.
            unfold maps_off. rewrite vmm_mmap_replacement, vmm_vmmaps.
            unfold mmap_fixed_noaccess_span_next. cbn [vm_maps].
            apply Forall_cons; [exact (mo_off_res m _ _ VI Espan) |].
            apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo. }
    destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
    2: {
      (* MAP_FIXED_NOREPLACE: a free range granted where [region_free] accepted, an occupied
         one refused with the model unchanged *)
      destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
      { difn H Enomem; [apply check_mmap_fixed_overflow_model in H; subst m'; exact Hmo|].
        difn H Eceil; [discriminate|].
        difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hmo|].
        difn H Epos; [discriminate|].
        apply negb_false_iff, Z.leb_le in Eceil.
        difn H Efree.
        - destruct ws, zs, cs, ci; try discriminate.
          destruct (errno_ret_in mmap_errnos ret).
          + destruct us; [|discriminate]. injection H as <- <-. exact Hmo.
          + difn H Eok; [|discriminate]. injection H as <- <-.
            unfold maps_off. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
            apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Efree) | exact Hmo].
        - destruct ws, zs, us, cs, ci; try discriminate.
          difn H Eerr; [|discriminate]. injection H as <- <-. exact Hmo. }
      destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
      difn H Enomem; [apply check_mmap_fixed_overflow_model in H; subst m'; exact Hmo|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hmo|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Efree.
      - destruct ws, us, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct zs; [|discriminate]. injection H as <- <-. exact Hmo.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          unfold maps_off. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Efree) | exact Hmo].
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. exact Hmo. }
    (* MAP_FIXED, read-write *)
    difn H Enomem; [apply check_mmap_fixed_overflow_model in H; subst m'; exact Hmo|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Elive.
    - destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct zs; [|discriminate]. destruct us.
        * injection H as <- <-. exact Hmo.
        * difn H Eus; [|discriminate]. injection H as <- <-.
          unfold maps_off. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
          cbn [vm_maps].
          apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
      + destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold maps_off. rewrite vmm_mmap_replacement, vmm_vmmaps, vmm_fixed_rw_next.
        exact Hmo.
    - difn H Efree.
      + destruct ws, us, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct zs; [|discriminate]. injection H as <- <-. exact Hmo.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold maps_off. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Efree) | exact Hmo].
      + difn H Espan; [|discriminate].
        destruct ws, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct zs; [|discriminate]. destruct us.
          -- injection H as <- <-. exact Hmo.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             unfold maps_off. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
             cbn [vm_maps].
             apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
        * destruct us; [|discriminate].
          difn H Eok; [|discriminate]. injection H as <- <-.
          unfold maps_off. rewrite vmm_mmap_replacement, vmm_vmmaps.
          unfold mmap_fixed_rw_span_next. cbn [vm_maps].
          apply Forall_cons; [exact (mo_off_res m _ _ VI Espan) |].
          apply mo_subtract; try (rewrite u64 by lia); try lia. exact Hmo.
  Qed.

  Lemma check_mremap_preserves_mo : forall old old_size new_size flags eff m m' evs,
    check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
    MmVdso.mm_vinv vlo vhi m -> maps_off m -> maps_off m'.
  Proof.
    intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H VI Hmo.
    unfold check_mremap in H. cbv zeta in H.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
    pose proof (word_range old) as Hor.
    pose proof (word_range old_size) as Hos.
    pose proof (word_range new_size) as Hns.
    difn H Eflag; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    difn H Enew; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    difn H Etask; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    difn H Eold; [discriminate|].
    difn H Esrc; [discriminate|].
    difn H Eeq; [apply check_ret_only_model in H; subst m'; exact Hmo|].
    destruct ws; [|discriminate]. destruct ci; [|discriminate].
    (* the new length is a nonzero number of pages *)
    unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 EnewB].
    apply Z.leb_gt in EnewB.
    pose proof (w_is0_false new_size Enew0) as Hnew0.
    assert (HnewZ : 0 < page_round_up_Z (bv_unsigned new_size))
      by (apply page_round_up_pos; lia).
    (* the source is free against [vm_reserved] and ends under the ceiling *)
    apply negb_false_iff in Esrc.
    apply andb_true_iff in Esrc as [Esrc _].
    unfold mremap_source_b in Esrc.
    apply andb_true_iff in Esrc as [Esrc _].
    apply andb_true_iff in Esrc as [Esrc Hhas].
    apply andb_true_iff in Esrc as [Hoceil Hsres].
    apply Z.leb_le in Hoceil.
    assert (HoldZ : 0 <= page_round_up_Z (bv_unsigned old_size))
      by (apply page_round_up_Z_nonneg; lia).
    (* what is left of the ledger once the source range is cut *)
    assert (Hcut : Forall (VdsoClean.range_off vlo vhi)
                     (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned old)
                        (bv_unsigned old
                         + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))))).
    { apply mo_subtract; [lia | rewrite u64 by lia; lia | exact Hmo]. }
    destruct (errno_ret_in mremap_errnos ret).
    { destruct zs, us, cs; try discriminate. injection H as <- <-. exact Hmo. }
    destruct (bv_eqb ret old).
    - difn H Eshrink.
      + (* shrink in place: a prefix of the source *)
        difn H Eok; [|discriminate]. injection H as <- <-.
        apply Z.ltb_lt in Eshrink.
        unfold maps_off. rewrite vmm_mremap_next.
        unfold mremap_maps_next. cbn [vm_maps].
        apply Forall_cons; [| exact Hcut].
        apply (MmVdso.off_shrink vlo vhi _ _
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))).
        * rewrite !u64 by lia. lia.
        * exact (mo_off_res m _ _ VI Hsres).
      + (* grow in place: the whole new range was tested against [vm_reserved] *)
        difn H Egrow; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold maps_off. rewrite vmm_mremap_next.
        unfold mremap_maps_next. cbn [vm_maps].
        unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
        apply andb_true_iff in Egrow as [Egrow _].
        unfold mremap_inplace_room_b in Egrow. cbv zeta in Egrow.
        apply andb_true_iff in Egrow as [Hgceil Hgfree].
        apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Hgfree) | exact Hcut].
    - (* move: a fresh destination free against [vm_reserved ++ vm_maps] *)
      difn H Emove; [|discriminate]. injection H as <- <-.
      unfold maps_off. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      apply andb_true_iff in Emove as [Emove _].
      apply andb_true_iff in Emove as [Emove _].
      apply andb_true_iff in Emove as [Emove _].
      apply andb_true_iff in Emove as [_ Hfresh].
      unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
      apply andb_true_iff in Hfresh as [Hfresh _].
      apply andb_true_iff in Hfresh as [Hfresh Hffree].
      apply Forall_cons; [exact (mo_off_res_app m _ _ _ VI Hffree) | exact Hcut].
  Qed.

  (** * The whole dispatcher *)

  Definition arm_preserves_mo (c : CheckedArm) : Prop :=
    forall i eff m m' evs,
      ca_check c i eff m = CheckOk m' evs ->
      MmVdso.mm_vinv vlo vhi m -> maps_off m -> maps_off m'.

  (** The enumeration is [NoaccessOwned.checked_table_preserves_na]'s, arm for arm. *)
  Lemma checked_table_preserves_mo : Forall arm_preserves_mo checked_table.
  Proof.
    unfold checked_table.
    repeat apply Forall_cons.
    all: try exact (Forall_nil arm_preserves_mo).
    all: unfold arm_preserves_mo; intros i eff m m' evs H VI Hmo;
         autorewrite with arm_unfold in H.
    (* Each alternative is tried in the model's form ([NoaccessOwned.checked_table_preserves_na]):
       [eapply] on the conclusion, then [eassumption] against the arm's checker hypothesis.  The
       earlier form, [exact (lemma .. H ..)] and [apply .. in H], never finished: a timed farm
       build of it ran past 600 s on [exact (check_mmap_preserves_mo .. H VI Hmo)] tried against
       another arm's checker hypothesis, the elaborator converting one checker into the other. *)
    all: first
      [ eapply check_brk_preserves_mo; eassumption
      | eapply check_mmap_preserves_mo; eassumption
      | eapply check_munmap_preserves_mo; eassumption
      | eapply check_mremap_preserves_mo; eassumption
      | (eapply (mo_maps_eq m m'); [eapply check_mprotect_maps; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_madvise_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_read_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_write_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_pread64_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_pwrite64_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_readv_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_writev_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_pwritev2_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_openat_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_close_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_lseek_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_ftruncate_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_ioctl_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_readlinkat_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_wait4_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_fsync_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getdents64_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_flock_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_exit_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_set_tid_address_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getpid_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_gettid_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_setsid_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_uname_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_prctl_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_prlimit64_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getrandom_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_gettimeofday_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_clock_gettime_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_clock_getres_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_nanosleep_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_dup_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_dup3_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_unlinkat_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_faccessat_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_faccessat2_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_pselect6_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_ppoll_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_newfstatat_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_fstat_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getid_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_setid_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_setresid_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getgroups_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_setgroups_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_socket_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_bind_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_listen_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_accept4_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_fcntl_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_sched_setscheduler_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_sched_getaffinity_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_sched_yield_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_sigaltstack_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_rt_sigaction_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_tkill_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_tgkill_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_rt_sigprocmask_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_futex_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_set_robust_list_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_clone_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_clone3_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getsockname_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getpeername_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_setsockopt_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getsockopt_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_shutdown_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_sendto_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_sendmsg_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_socketpair_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_recvfrom_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_recvmsg_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_connect_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_timerfd_create_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_eventfd2_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_pipe2_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_getcwd_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_epoll_create1_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_epoll_ctl_frame; eassumption | exact Hmo])
      | (eapply (mo_frame m m'); [eapply check_epoll_pwait_frame; eassumption | exact Hmo])
      | fail 1 "checked_table_preserves_mo has no case for this dispatcher arm: give its checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves_mo one (it writes vm_maps), and add it to the list above" ].
  Qed.

  (** Every outcome the specification admits keeps the ledger off the window. *)
  Theorem mo_spec_ok : forall i mo eff mo' evs, MmVdso.mm_vinv vlo vhi mo -> maps_off mo ->
    syscall_spec i mo (Ok eff mo' evs) -> maps_off mo'.
  Proof.
    intros i mo eff mo' evs VI Hmo Hs.
    pose proof (check_syscall_complete_ok i eff mo mo' evs Hs) as H.
    unfold check_syscall in H.
    destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
      [|discriminate H].
    pose proof checked_table_preserves_mo as Hall.
    rewrite Forall_forall in Hall.
    exact (Hall c (lookup_ca_In _ _ _ Elk) i eff mo mo' evs H VI Hmo).
  Qed.

  (** * One step of the run *)

  Theorem mo_step : forall segs cfg c evs c', sstep_cfg segs cfg c evs (SNext c') ->
    MmVdso.mm_vinv vlo vhi (cfg_model c) -> maps_off (cfg_model c) -> maps_off (cfg_model c').
  Proof.
    intros segs cfg c0 evs0 c' H. remember (SNext c') as st eqn:Est. revert Est.
    destruct H as [ms model ms' model' Hh Hp Ha
                 | ms model Hh Hp Ha
                 | ms model Hh Hp Ha Hv
                 | ms model fn n eff model' model'' evs Hh Hp Ha Hv Hn Hs Hf Hh' Hm
                 | ms model fn n eff model' evs Hh Hp Ha Hv Hn Hs Hf Hh' Hm
                 | ms model fn Hh Hp Ha Hv Hu
                 | ms model x8 eff model' model'' evs Hh Hp Hs Hsp Hh' Hm
                 | ms model x8 eff model' evs Hh Hp Hs Hsp Hh' Hm
                 | ms model x8 eff model' evs code Hh Hp Hs Hh' Hk
                 | ms model x8 eff model' evs sg Hh Hp Hs Hk
                 | ms model x8 Hh Hp Hs ];
      intros Est; try discriminate Est; injection Est as Ec; subst c';
      cbn [cfg_model]; intros VI Hmo.
    - (* a machine step: the first-touch accounting keeps the ledger *)
      destruct (mi_account_step_model_frame _ _ _ _ _ Ha) as (_ & Hvm & _).
      exact (mo_frame model model' Hvm Hmo).
    - (* a vDSO call: the call, the materialization, then the call count *)
      destruct (materialize_model_accesses_frame _ _ _ Hm) as (_ & Hvm & _).
      exact (mo_frame model'' (with_vdso_bump model'') (m_vmmaps_with_vdso_bump model'')
               (mo_frame model' model'' Hvm (mo_spec_ok _ _ _ _ _ VI Hmo Hs))).
    - (* a system call that returns *)
      destruct (materialize_model_accesses_frame _ _ _ Hm) as (_ & Hvm & _).
      exact (mo_frame model' model'' Hvm (mo_spec_ok _ _ _ _ _ VI Hmo Hs)).
    - (* exit *)
      exact (mo_spec_ok _ _ _ _ _ VI Hmo Hs).
    - (* killed *)
      exact (mo_spec_ok _ _ _ _ _ VI Hmo Hs).
  Qed.
End MapsOff.
