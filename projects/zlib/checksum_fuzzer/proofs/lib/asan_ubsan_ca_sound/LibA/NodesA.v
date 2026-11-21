(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Section Defs.
Variable NMAX : nat.

Definition minvA (mo : Model) : Prop := minv (strip mo) /\ m_vm_materialized mo = [].

Lemma minvA_minv : forall mo, minvA mo -> minv (strip mo).
Proof. intros mo [H _]; exact H. Qed.


Definition mmap_fixed_repl (flags addr n : word) (mo : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo).
Definition mmap_fixed_span_repl (flags addr n : word) (mo : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo).

Definition nslack (n : node) (mo : Model) : Prop :=
  match n with
  | NBrk req =>
      (* brk charges whole pages (brk_grow_bytes), as
         LibA/MmXfer check_brk_X and Spec/Relim *)
      robust NMAX (nonlazy_bytes mo + brk_grow_bytes (m_vmmaps mo) (Z_to_bv 64 req)) (vm_limit (m_vmmaps mo))
  | NMmap addr len prot flags =>
      let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
      (mmap_noreserve_b (Z_to_bv 64 flags) = true \/ robust NMAX (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo)))
      /\ robust NMAX (nonlazy_bytes (mmap_fixed_repl (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) mo))
                (vm_limit (m_vmmaps mo))
      /\ robust NMAX (nonlazy_bytes (mmap_fixed_span_repl (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) mo))
                (vm_limit (m_vmmaps mo))
  | NMprotect addr len prot =>
      robust NMAX (nonlazy_bytes (mprotect_model_next mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))))
             (vm_limit (m_vmmaps mo))
  | _ => True
  end.

Definition mmap_safeA_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
  mmap_safe_b addr len prot flags fd off h.

Definition nsafeA0 (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      mmap_safeA_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                   (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
      (* the decline guard, exactly as Lib/Nodes nsafe NMmap carries
         it ( #146: check_mmap answers unmodeled for a hint the model declines, in the modeled and noaccess
         arms only). A NULL hint discharges it by place_declined_b_null; a MAP_FIXED call by the arm test. *)
      /\ (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true \/
          mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
          place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 addr)
            (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = false)
  | _ => nsafe n mo
  end.

Definition nsafeA (n : node) (mo : Model) : Prop := nsafeA0 n mo /\ nslack n mo.

(* + the decline premise, as Lib/Nodes mmap_safe_no_unmodeled *)
Lemma mmap_safeA_no_unmodeled : forall addr len prot flags fd off eff m,
  (mmap_modeled_b prot flags off = true \/ mmap_noaccess_b prot flags off = true ->
   place_declined_b (m_kernel m) (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)) = false) ->
  mmap_safeA_b addr len prot flags fd off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof. intros addr len prot flags fd off eff m Hd H. apply mmap_safe_no_unmodeled; [exact Hd| exact H]. Qed.

Lemma nsafeA0_mmap_fixed_rw : forall addr len flags mo,
  mmap_fixed_rw_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  w_is0 (Z_to_bv 64 len) = false ->
  let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
  0 < addr -> addr mod page_size = 0 -> addr + nZ <= alloc_top (m_vmmaps mo) ->
  (region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true /\
   map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true)
  \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  nsafeA0 (NMmap addr len (PROT_READ + PROT_WRITE) flags) mo.
Proof.
  intros addr len flags mo FRW NZ nZ A0 AL ACE RG. cbn [nsafeA0].
  (* the decline guard is vacuous for a MAP_FIXED call: its flags core is
     MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED, which neither the modeled nor the noaccess arm accepts. *)
  split.
  2:{ assert (F1 := FRW). unfold mmap_fixed_rw_b in F1.
      apply andb_prop in F1 as [F0 _]. apply andb_prop in F0 as [_ F1]. apply Z.eqb_eq in F1.
      intros Hm. exfalso.
      destruct Hm as [Hm|Hm]; [unfold mmap_modeled_b in Hm| unfold mmap_noaccess_b in Hm];
        apply andb_prop in Hm as [Hm _]; apply andb_prop in Hm as [_ F2]; apply Z.eqb_eq in F2;
        rewrite F1 in F2; vm_compute in F2; discriminate F2. }
  unfold mmap_safeA_b, mmap_safe_b.
  pose proof (alloc_top_lt (m_vmmaps mo)) as TOP. unfold two_pow_64 in TOP.
  assert (AN : mmap_anon_b (Z_to_bv 64 flags) = true).
  { unfold mmap_fixed_rw_b in FRW. apply andb_prop in FRW as [F _]. apply andb_prop in F as [_ F]. apply Z.eqb_eq in F.
    unfold mmap_anon_b, mmap_flags_core in *. apply negb_true_iff, Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite F; reflexivity).
    rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
    rewrite Z0 in T'. discriminate. }
  rewrite AN, NZ, FRW. change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. cbn [andb].
  rewrite !orb_true_iff. right. cbn [andb]. unfold mmap_fixed_gate_b. cbv zeta.
  assert (AU : bv_unsigned (Z_to_bv 64 addr) = addr)
    by (apply unsigned_lit; pose proof (page_round_up_Z_nonneg _ (proj1 (bv_unsigned_in_range 64 (Z_to_bv 64 len)))); lia).
  rewrite AU. fold nZ.
  destruct (Z.leb_spec two_pow_64 (addr + nZ)); [reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) ACE). cbn [negb]. rewrite (proj2 (Z.eqb_eq _ _) AL). cbn [negb].
  rewrite (proj2 (Z.ltb_lt _ _) A0). cbn [negb].
  destruct RG as [[E1 E2]| E3]; [rewrite E1, E2; reflexivity| rewrite E3, orb_true_r; reflexivity].
Qed.

End Defs.

Definition nstepA (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  match n with
  | NMmap _ _ _ _ =>
      evs = [] /\
      match node_input n with
      | Some i => syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg alloc_forced_cfg i mo eff
      | None => False
      end
  | _ => nstep n mo eff mo' evs
  end.

Definition nexitA : node -> Model -> word -> Model -> Prop := nexit.

Definition fstepA (n : node) (rsp : resp) (R R' : footprint) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      fp_le R R' /\
      (prot = PROT_READ + PROT_WRITE ->
       bv_unsigned (eff_ret rsp) mod page_size = 0 ->
       rng R' (bv_unsigned (eff_ret rsp)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
  | NMunmap addr len =>
      forall b (j : nat), R b j ->
        (b + Z.of_nat j <= bv_unsigned (Z_to_bv 64 addr) \/
         bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= b) -> R' b j
  | NBrk _ | NMprotect _ _ _ => fp_le R R'
  | _ => R' = R
  end.

Lemma fstepA_id : forall n rsp R,
  match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
  fstepA n rsp R R.
Proof. intros n rsp R H; destruct n; try destruct H; reflexivity. Qed.

Lemma fstepA_rng : forall n rsp R R' lo len,
  match n with NMunmap _ _ => False | _ => True end ->
  fstepA n rsp R R' -> rng R lo len -> rng R' lo len.
Proof.
  intros n rsp R R' lo len Hn HF HR. destruct n; try destruct Hn; cbn in HF;
    try (subst R'; exact HR); try (eapply rng_fp_le; [| exact HR]); try exact HF. exact (proj1 HF).
Qed.

Lemma fstepA_munmap_rng : forall addr len rsp R R' lo l,
  fstepA (NMunmap addr len) rsp R R' -> rng R lo l ->
  (lo + l <= bv_unsigned (Z_to_bv 64 addr) \/
   bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= lo) ->
  rng R' lo l.
Proof.
  intros addr len rsp R R' lo l HF (A & B & HR) HD. split; [exact A|]. split; [exact B|].
  intros b j Hb Hj. apply HF; [apply HR; assumption| lia].
Qed.

Lemma fstepA_mmap_grant : forall addr len flags rsp R R',
  fstepA (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  bv_unsigned (eff_ret rsp) mod page_size = 0 ->
  rng R' (bv_unsigned (eff_ret rsp)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))).
Proof. intros addr len flags rsp R R' [_ H] Hal. apply H; [reflexivity| exact Hal]. Qed.


Section AtNodeA.
Variable segs : list Segment.

Definition ncov (n : node) (RNG : footprint) (ms : machine_state) : Prop :=
  match n with
  | NWrite fd bs => rng RNG (bv_unsigned (areg ms 11)) (Z.of_nat (length bs))
  | NOpen path => rng RNG (bv_unsigned (areg ms 11)) (Z.of_nat (cstr_len path))
  | NRead fd buf count => rng RNG buf count
  | _ => True
  end.

Definition at_nodeA (n : node) (RNG : footprint) (ms : machine_state) : Prop :=
  match n with
  | NWritev fd bufs =>
      ms_svc_pending ms = Some (Z_to_bv 64 66) /\
      (fd = 1 \/ fd = 2) /\
      areg ms 10 = Z_to_bv 64 fd /\
      areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
      (1 <= length bufs <= 1024)%nat /\
      Z.of_nat (length (concat bufs)) <= max_write /\
      bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE /\
      ms_rom ms = seg_rom segs /\
      rng RNG (bv_unsigned (areg ms 11)) (16 * Z.of_nat (length bufs)) /\
      exists iovs : list (word * word),
        bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
        Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                               rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs bufs
  | NMmap addr len prot flags =>
      ms_svc_pending ms = Some (Z_to_bv 64 222) /\
      areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
      areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
      areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
  | _ => at_node segs n ms /\ ncov n RNG ms
  end.

Lemma at_nodeA_at_node : forall n RNG ms,
  match n with NMmap _ _ _ _ => False | _ => True end ->
  at_nodeA n RNG ms -> at_node segs n ms.
Proof.
  intros n RNG ms Hn H. destruct n; try destruct Hn; try exact (proj1 H).
  cbn in H |- *. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & iovs & Hi & HF).
  repeat (split; [assumption|]). exists iovs. split; [exact Hi|].
  eapply Forall2_impl; [| exact HF]. cbn. intros a b (X & X2 & Y & _). auto.
Qed.

Lemma at_nodeA_pending : forall n RNG ms, at_nodeA n RNG ms -> ms_svc_pending ms <> None.
Proof.
  intros n RNG ms H.
  assert (Hx : exists x8, ms_svc_pending ms = Some x8).
  { destruct n; cbn [at_nodeA at_node] in H;
      first [ destruct H as [[[X|X] _] _]; eexists; exact X
            | destruct H as [[X _] _]; eexists; exact X
            | destruct H as [X _]; eexists; exact X ]. }
  destruct Hx as [x8 ->]. discriminate.
Qed.

End AtNodeA.


Lemma materialize_nil : forall m, materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages. cbn.
  f_equal. apply MX_mat.
Qed.

Section Kit.
Variable segs : list Segment.
Variable NMAX : nat.

Definition succ_ok (A : alw) (n : node) (mo mo_ : Model) (eff : resp) (moX : Model) (evs : list event) : Prop :=
  exists mo' moY,
    nstepA n mo (rstrip eff) mo' evs /\
    materialize_model_accesses moX (syscall_effect_accesses eff) = Some moY /\
    mrel A mo' moY.

Lemma kit_complete : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 -> m_halted mo_ = None ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None) ->
  forall evs X, sstep segs (mkCfg ms mo_) evs X ->
    exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstepA n mo rsp mo' evs /\ mrel A mo' mo_'.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hh Hok Hnu Hhalt evs X Hss.
  destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hss)
    as [(eff & moX & mo_'' & Hs & Hh' & Hmat & ->) | [(eff & moX & evs1 & Hs & Hh' & Hmat & -> & ->)
       | [(eff & moX & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & moX & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
  - apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as (mo' & moY & Hn & HmatY & MR).
    rewrite HmatY in Hmat. injection Hmat as <-.
    exists (rstrip eff), mo', moY. rewrite nret_rstrip. auto.
  - exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as (mo' & moY & Hn & HmatY & MR). congruence.
  - exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as (mo' & moY & Hn & HmatY & (SB & _)).
    pose proof (Hhalt _ _ _ Hn) as Hh0.
    pose proof (materialize_model_accesses_frame _ _ _ HmatY) as (_ & _ & _ & _ & _ & PR & _).
    pose proof (same_but_mat_halted _ _ SB) as E. unfold m_halted in *. rewrite PR in E. congruence.
  -
    exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs) as (mo' & moY & Hn & HmatY & (SB & _)).
    pose proof (Hhalt _ _ _ Hn) as Hh0.
    pose proof (materialize_model_accesses_frame _ _ _ HmatY) as (_ & _ & _ & _ & _ & PR & _).
    pose proof (same_but_mat_halted _ _ SB) as E. apply (m_killed_halted _ _ Hk').
    unfold m_halted in *. rewrite PR in E. congruence.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
Qed.

Lemma kit_sound : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 -> m_halted mo_ = None ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs ->
     exists effk moX, check_syscall (sys_input segs ms x8) effk mo_ = CheckOk moX evs /\ rstrip effk = eff) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None) ->
  (forall eff mo1 mo2 evs1 evs2, nstepA n mo eff mo1 evs1 -> nstepA n mo eff mo2 evs2 -> mo1 = mo2) ->
  forall eff mo' evs, nstepA n mo eff mo' evs ->
    exists mo_', sstep segs (mkCfg ms mo_) evs (SNext (mkCfg (nret ms eff) mo_')) /\ mrel A mo' mo_'.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hh Hok Hcpl Hhalt Hdet eff mo' evs Hn.
  destruct (Hcpl _ _ _ Hn) as (effk & moX & Hck & Hst).
  destruct (Hok _ _ _ Hck) as (mo1 & moY & Hn1 & HmatY & MR). rewrite Hst in Hn1.
  pose proof (Hdet _ _ _ _ _ Hn Hn1) as <-.
  exists moY. split; [|exact MR].
  rewrite <- Hst, nret_rstrip. unfold nret.
  assert (HhX : m_halted moX = None).
  { destruct MR as (SB & _). pose proof (Hhalt _ _ _ Hn).
    pose proof (materialize_model_accesses_frame _ _ _ HmatY) as (_ & _ & _ & _ & _ & PR & _).
    pose proof (same_but_mat_halted _ _ SB) as E. unfold m_halted in *. rewrite PR in E. congruence. }
  eapply sstep_syscall; [exact Hh| exact Hsvc| apply check_syscall_ok_iff; exact Hck| exact HhX| exact HmatY].
Qed.

Lemma kit_progress : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) ->
  exists rsp mo' evs, nstepA n mo rsp mo' evs.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hok Hnu.
  pose proof (receptive (sys_input segs ms x8) mo_) as Hr.
  destruct (syscall_spec_witness (sys_input segs ms x8) mo_) as [eff moX evs|] eqn:E.
  - apply check_syscall_ok_iff in Hr. destruct (Hok _ _ _ Hr) as (mo' & moY & Hn & _). eauto.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.

Lemma succ_ok_nil : forall A n mo mo_ eff moX mo' evs,
  nstepA n mo (rstrip eff) mo' evs ->
  syscall_effect_accesses eff = [] ->
  mrel A mo' moX ->
  succ_ok A n mo mo_ eff moX evs.
Proof.
  intros A n mo mo_ eff moX mo' evs Hn Hacc MR. exists mo', moX. split; [exact Hn|]. split; [|exact MR].
  rewrite Hacc. apply materialize_nil.
Qed.

Lemma succ_ok_acct : forall A RNG n mo mo_ eff moX mo' evs,
  nstepA n mo (rstrip eff) mo' evs ->
  m_vm_materialized mo' = [] -> same_but_mat mo' moX ->
  m_vmmaps moX = m_vmmaps mo_ -> m_vm_lazy moX = m_vm_lazy mo_ -> m_vm_materialized moX = m_vm_materialized mo_ ->
  ainv (m_vm_lazy mo_) A NMAX mo_ ->
  footprint_ok (m_vm_lazy mo_) A RNG -> Forall (acc_in RNG) (syscall_effect_accesses eff) ->
  succ_ok A n mo mo_ eff moX evs.
Proof.
  intros A RNG n mo mo_ eff moX mo' evs Hn CAN SB VM LZ MT INV FOK FA.
  assert (INVX : ainv (m_vm_lazy mo_) A NMAX moX).
  { destruct INV as [L1 L2 L3 L4 L5]. constructor; rewrite ?LZ, ?MT, ?VM; auto.
    unfold nonlazy_bytes in *. rewrite VM, LZ. exact L5. }
  destruct (account_ok (m_vm_lazy mo_) A NMAX moX (syscall_effect_accesses eff) INVX
              (accesses_ok_of_footprint _ _ _ _ FOK FA)) as (moY & HmatY & INVY & SBY).
  exists mo', moY. split; [exact Hn|]. split; [exact HmatY|].
  split; [eapply same_but_mat_trans; eauto|]. split; [exact CAN|].
  destruct INVY as [_ ND AL _ _]. auto.
Qed.

(* forced-only port: the kit over the filtered step. *)
Lemma succ_ok_halted : forall A n mo mo_ eff moX evs,
  succ_ok A n mo mo_ eff moX evs ->
  (forall eff' mo' evs', nstepA n mo eff' mo' evs' -> m_halted mo' = None) -> m_halted moX = None.
Proof.
  intros A n mo mo_ eff moX evs (mo' & moY & Hn & HmatY & MR) Hh.
  destruct MR as (SB & _). pose proof (Hh _ _ _ Hn) as Hh'.
  pose proof (materialize_model_accesses_frame _ _ _ HmatY) as (_ & _ & _ & _ & _ & PR & _).
  pose proof (same_but_mat_halted _ _ SB) as E. unfold m_halted in *. rewrite PR in E. congruence.
Qed.

Lemma kit_complete_cfg : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 -> m_halted mo_ = None ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> m_halted moX = None) ->
  forall evs X, sstep_cfg segs alloc_forced_cfg (mkCfg ms mo_) evs X ->
    exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstepA n mo rsp mo' evs /\ mrel A mo' mo_'.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hh Hok Hnu Hhalt0 evs X Hss.
  destruct (sstep_cfg_svc_inv segs alloc_forced_cfg ms mo_ x8 evs X Hsvc Hss)
    as [(eff & moX & mo_'' & Hs & Hns & Hh' & Hmat & ->) | [(eff & moX & evs1 & Hs & Hns & Hh' & Hmat & -> & ->)
       | [(eff & moX & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & moX & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
  - apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs Hns) as (mo' & moY & Hn & HmatY & MR).
    rewrite HmatY in Hmat. injection Hmat as <-.
    exists (rstrip eff), mo', moY. rewrite nret_rstrip. auto.
  - exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs Hns) as (mo' & moY & Hn & HmatY & MR). congruence.
  - exfalso. apply check_syscall_ok_iff in Hs. apply Hhalt0 in Hs. congruence.
  - exfalso. apply check_syscall_ok_iff in Hs. apply Hhalt0 in Hs. exact (m_killed_halted _ _ Hk' Hs).
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
Qed.

Lemma kit_sound_cfg : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 -> m_halted mo_ = None ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs ->
     exists effk moX, check_syscall (sys_input segs ms x8) effk mo_ = CheckOk moX evs /\ rstrip effk = eff
                      /\ ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ effk) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None) ->
  (forall eff mo1 mo2 evs1 evs2, nstepA n mo eff mo1 evs1 -> nstepA n mo eff mo2 evs2 -> mo1 = mo2) ->
  forall eff mo' evs, nstepA n mo eff mo' evs ->
    exists mo_', sstep_cfg segs alloc_forced_cfg (mkCfg ms mo_) evs (SNext (mkCfg (nret ms eff) mo_')) /\ mrel A mo' mo_'.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hh Hok Hcpl Hhalt Hdet eff mo' evs Hn.
  destruct (Hcpl _ _ _ Hn) as (effk & moX & Hck & Hst & Hns).
  destruct (Hok _ _ _ Hck Hns) as (mo1 & moY & Hn1 & HmatY & MR). rewrite Hst in Hn1.
  pose proof (Hdet _ _ _ _ _ Hn Hn1) as <-.
  exists moY. split; [|exact MR].
  rewrite <- Hst, nret_rstrip. unfold nret.
  assert (HhX : m_halted moX = None).
  { destruct MR as (SB & _). pose proof (Hhalt _ _ _ Hn).
    pose proof (materialize_model_accesses_frame _ _ _ HmatY) as (_ & _ & _ & _ & _ & PR & _).
    pose proof (same_but_mat_halted _ _ SB) as E. unfold m_halted in *. rewrite PR in E. congruence. }
  eapply sstep_cfg_syscall; [exact Hh| exact Hsvc| apply check_syscall_ok_iff; exact Hck| exact Hns| exact HhX| exact HmatY].
Qed.

Lemma kit_progress_cfg : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) ->
  exists rsp mo' evs, nstepA n mo rsp mo' evs.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hok Hnu.
  pose proof (receptive (sys_input segs ms x8) mo_) as Hr.
  destruct (syscall_spec_witness (sys_input segs ms x8) mo_) as [eff moX evs|] eqn:E.
  - destruct (nonspurious_outcome_exists alloc_forced_cfg _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    apply check_syscall_ok_iff in Hs2. destruct (Hok _ _ _ Hs2 Hns2) as (mo' & moY & Hn & _). eauto.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.

End Kit.

(** The filter reads an input through its number, its first argument (brk's request), the model's VM ledger
    (brk's old break) and which effects the spec admits: two inputs at two models that agree on those
    filter alike (forced-only port). *)
Lemma spurious_iff_X : forall cfg i1 i2 m1 m2 eff,
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 -> m_vmmaps m1 = m_vmmaps m2 ->
  (forall e, (exists m' evs, check_syscall i1 e m1 = CheckOk m' evs) <->
             (exists m' evs, check_syscall i2 e m2 = CheckOk m' evs)) ->
  spurious_refusal_cfg cfg i1 m1 eff <-> spurious_refusal_cfg cfg i2 m2 eff.
Proof.
  intros cfg i1 i2 m1 m2 eff Hno Ha0 Hvm Hc.
  assert (Hr : forall r, refusal_b i1 m1 r = refusal_b i2 m2 r).
  { intros r. unfold refusal_b, brk_refusal_b. rewrite Hno, Ha0, Hvm. reflexivity. }
  unfold spurious_refusal_cfg, injected_family_off. rewrite Hno. split.
  - intros (H1 & H2 & (eff' & m' & evs' & Hs & Hnr)). split; [exact H1|]. split; [rewrite <- Hr; exact H2|].
    apply check_syscall_ok_iff in Hs. destruct (proj1 (Hc eff') (ex_intro _ m' (ex_intro _ evs' Hs))) as (m2' & evs2 & Hs2).
    exists eff', m2', evs2. split; [apply check_syscall_ok_iff; exact Hs2| rewrite <- Hr; exact Hnr].
  - intros (H1 & H2 & (eff' & m' & evs' & Hs & Hnr)). split; [exact H1|]. split; [rewrite Hr; exact H2|].
    apply check_syscall_ok_iff in Hs. destruct (proj2 (Hc eff') (ex_intro _ m' (ex_intro _ evs' Hs))) as (m1' & evs1 & Hs1).
    exists eff', m1', evs1. split; [apply check_syscall_ok_iff; exact Hs1| rewrite Hr; exact Hnr].
Qed.


Lemma cov_one : forall RNG (a : word) (k : nat) len,
  rng RNG (bv_unsigned a) len -> Z.of_nat k <= len -> Forall (acc_in RNG) [(a, k)].
Proof.
  intros RNG a k len HR Hk. constructor; [|constructor].
  eapply rng_acc_var; [exact HR|]. lia.
Qed.

Ltac dispatch K :=
  lazymatch K with
  | 64 => rewrite check_syscall_write by (apply sysno_lit; lia)
  | 66 => rewrite check_syscall_writev by (apply sysno_lit; lia)
  | 56 => rewrite check_syscall_openat by (apply sysno_lit; lia)
  | 63 => rewrite check_syscall_read by (apply sysno_lit; lia)
  | 57 => rewrite check_syscall_close by (apply sysno_lit; lia)
  | 29 => rewrite check_syscall_ioctl by (apply sysno_lit; lia)
  | 96 => rewrite check_syscall_set_tid_address by (apply sysno_lit; lia)
  | 93 => rewrite check_syscall_exit by (apply sysno_lit; lia)
  | 94 => rewrite check_syscall_exit_group by (apply sysno_lit; lia)
  | 214 => rewrite check_syscall_brk by (apply sysno_lit; lia)
  | 222 => rewrite check_syscall_mmap by (apply sysno_lit; lia)
  | 215 => rewrite check_syscall_munmap by (apply sysno_lit; lia)
  | 226 => rewrite check_syscall_mprotect by (apply sysno_lit; lia)
  end;
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

Ltac dispatch_pure K :=
  lazymatch K with
  | 214 => rewrite check_syscall_brk by reflexivity
  | 222 => rewrite check_syscall_mmap by reflexivity
  | 215 => rewrite check_syscall_munmap by reflexivity
  | 226 => rewrite check_syscall_mprotect by reflexivity
  end; cbn [in_arg in_args nth pure_input].

Lemma cov_one_lit : forall RNG (a : Z) (k : nat) len,
  rng RNG a len -> 0 <= a < 2^64 -> Z.of_nat k <= len -> Forall (acc_in RNG) [(Z_to_bv 64 a, k)].
Proof.
  intros RNG a k len HR Ha Hk. constructor; [|constructor].
  unfold acc_in. cbn [fst snd]. rewrite unsigned_lit by lia. destruct HR as (_ & _ & H'). apply H'; lia.
Qed.

Section PerNodeA.
Variable segs : list Segment.
Variable NMAX : nat.

Definition node_factsA (A : alw) (RNG : footprint) (ms : machine_state) (mo mo_ : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> succ_ok A n mo mo_ eff moX evs) /\
  (forall eff mo' evs, nstepA n mo eff mo' evs ->
     exists effk moX, check_syscall (sys_input segs ms x8) effk mo_ = CheckOk moX evs /\ rstrip effk = eff) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) /\
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None /\ minvA mo') /\
  (forall eff mo1 mo2 evs1 evs2, nstepA n mo eff mo1 evs1 -> nstepA n mo eff mo2 evs2 -> mo1 = mo2).

(** [node_factsA] over the filtered relation (forced-only port). *)
Definition node_factsA_fo (A : alw) (RNG : footprint) (ms : machine_state) (mo mo_ : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) /\
  (forall eff mo' evs, nstepA n mo eff mo' evs ->
     exists effk moX, check_syscall (sys_input segs ms x8) effk mo_ = CheckOk moX evs /\ rstrip effk = eff
                      /\ ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ effk) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) /\
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> m_halted moX = None) /\
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None /\ minvA mo') /\
  (forall eff mo1 mo2 evs1 evs2, nstepA n mo eff mo1 evs1 -> nstepA n mo eff mo2 evs2 -> mo1 = mo2).

Lemma node_factsA_fo_of_node_factsA : forall A RNG ms mo mo_ n,
  (forall x8, ms_svc_pending ms = Some x8 -> injected_family_off alloc_forced_cfg (sys_input segs ms x8) = false) ->
  node_factsA A RNG ms mo mo_ n -> node_factsA_fo A RNG ms mo mo_ n.
Proof.
  intros A RNG ms mo mo_ n Hon (x8 & Hsvc & Hok & Hcpl & Hnu & Hpres & Hdet).
  pose proof (Hon x8 Hsvc) as Hoff.
  exists x8. split; [exact Hsvc|]. split; [|split; [|split; [|split; [|split]]]].
  - intros eff moX evs Hc _. exact (Hok _ _ _ Hc).
  - intros eff mo' evs Hn. destruct (Hcpl _ _ _ Hn) as (effk & moX & Hc & Hs).
    exists effk, moX. split; [exact Hc|]. split; [exact Hs|]. apply spurious_refusal_family_on. exact Hoff.
  - exact Hnu.
  - intros eff moX evs Hc. apply (succ_ok_halted A n mo mo_ eff moX evs (Hok _ _ _ Hc)).
    intros eff' mo' evs' Hn. exact (proj1 (Hpres _ _ _ Hn)).
  - exact Hpres.
  - exact Hdet.
Qed.

Section Common.
  Variables (A : alw) (RNG : footprint) (ms : machine_state) (mo mo_ : Model).
  Hypothesis Hh : m_halted mo = None.
  Hypothesis Hminv : minvA mo.
  Hypothesis MR : mrel A mo mo_.
  Hypothesis INV : ainv (m_vm_lazy mo) A NMAX mo_.
  Hypothesis FOK : footprint_ok (m_vm_lazy mo) A RNG.

  Let matl := m_vm_materialized mo_.
  Lemma mo__MX : mo_ = MX mo matl.
  Proof. exact (proj1 MR). Qed.
  Lemma CAN : m_vm_materialized mo = [].
  Proof. exact (proj1 (proj2 MR)). Qed.
  Lemma MINV_ : minv (strip mo_).
  Proof. rewrite mo__MX, strip_MX. exact (proj1 Hminv). Qed.
  Lemma MINV : minv (strip mo).
  Proof. exact (proj1 Hminv). Qed.
  Lemma Hh_ : m_halted mo_ = None.
  Proof. rewrite mo__MX, m_halted_MX. exact Hh. Qed.

  Lemma succ_ok_neutral : forall n eff mo' evs,
    nstepA n mo (rstrip eff) mo' evs ->
    m_vm_materialized mo' = [] -> m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo ->
    Forall (acc_in RNG) (syscall_effect_accesses eff) ->
    succ_ok A n mo mo_ eff (MX mo' matl) evs.
  Proof.
    intros n eff mo' evs Hn CAN' VM LZ FA.
    eapply (succ_ok_acct NMAX A RNG); [exact Hn| exact CAN'| apply same_but_mat_MX| | | | | |].
    - rewrite m_vmmaps_MX, VM, mo__MX, m_vmmaps_MX. reflexivity.
    - rewrite m_vm_lazy_MX, LZ, mo__MX, m_vm_lazy_MX. reflexivity.
    - rewrite m_vm_materialized_MX. reflexivity.
    - rewrite mo__MX, m_vm_lazy_MX. rewrite <- mo__MX. exact INV.
    - rewrite mo__MX, m_vm_lazy_MX. exact FOK.
    - exact FA.
  Qed.


  Lemma std_chanA : forall m fd, minv (strip m) -> (fd = 1 \/ fd = 2) ->
    fd_lookup (m_fds m) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd)) /\ w_is0 (Z_to_bv 64 fd) = false.
  Proof. intros m fd Hm Hfd. exact (std_chan (strip m) fd Hm Hfd). Qed.

  (* c2 (NEW): at check_write / check_writev gate the channel arm on
     m_channel_reader; Lib/Nodes minv carries it (minv_reader), and strip keeps it. *)
  Lemma minv_reader_stripA : forall m, minv (strip m) -> m_channel_reader m = true.
  Proof. intros m Hm. exact (minv_reader (strip m) Hm). Qed.

  Lemma write_check_specA : forall m fd bs eff,
    at_node segs (NWrite fd bs) ms -> minv (strip m) ->
    check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff m = write_check fd (areg ms 11) bs eff m.
  Proof.
    intros m fd bs eff (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Htop & Hrom & Hbs) Hm.
    pose proof max_write_lt as (W1 & W2 & W3 & W4).
    dispatch 64. unfold check_write. rewrite Ha0, Ha2, in_mem_si.
    (* c2: + the channel-reader gate, as Lib/Nodes write_check_spec *)
    destruct (std_chanA m fd Hm Hfd) as [Hlk Hw]. rewrite Hlk, Hw, (minv_reader_stripA m Hm).
    unfold modeled_rw_range. rewrite (access_okb_below (areg ms 11)) by (rewrite ?unsigned_lit by lia; lia).
    rewrite orb_true_r. cbn [negb].
    rewrite w_is0_lit by lia. replace (Z.of_nat (length bs) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold write_source. rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; lia). rewrite unsigned_lit by lia.
    rewrite <- (wa_unsigned_id (areg ms 11)).
    rewrite !(readable_bytes_bytes_in bs) by (first [eapply bytes_at_in; eassumption | lia]).
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  Qed.

  Lemma write_factsA : forall fd bs,
    at_nodeA segs (NWrite fd bs) RNG ms -> node_factsA A RNG ms mo mo_ (NWrite fd bs).
  Proof.
    intros fd bs [Hat Hcov]. exists (Z_to_bv 64 64). split; [exact (proj1 Hat)|].
    pose proof max_write_lt as (W1 & W2 & W3 & W4). pose proof Hat as (_ & _ & _ & _ & Hlen & _). cbn [ncov] in Hcov.
    split; [|split; [|split; [|split]]].
    - intros eff moX evs Hc. rewrite (write_check_specA mo_ fd bs eff Hat MINV_) in Hc.
      destruct (write_check_ok _ _ _ _ _ _ _ Hc) as [Hn Hci].
      destruct Hn as (k & Hk & Heff & -> & ->).
      rewrite mo__MX. apply succ_ok_neutral; try reflexivity.
      + cbn [nstepA nstep]. exists k. auto.
      + exact CAN.
      + unfold syscall_effect_accesses. rewrite Hci.
        destruct eff as [ret ws zs us cs ci]; cbn [rstrip] in Heff. unfold eff0 in Heff. injection Heff as E1 E2 E3 E4 E5.
        subst. cbn [eff_writes write_accesses app eff_ret].
        eapply cov_one; [exact Hcov|]. rewrite unsigned_lit by lia. lia.
    - intros eff mo' evs Hn. cbn [nstepA] in Hn. pose proof Hn as (k & Hk & -> & -> & ->).
      destruct (write_check_complete fd (areg ms 11) bs (eff0 (Z_to_bv 64 k)) mo_ mo_ _ ltac:(lia)
                  ltac:(cbn [nstep]; exists k; auto)) as (effk & Hck & Hst).
      exists effk, mo_. rewrite (write_check_specA mo_ fd bs effk Hat MINV_). auto.
    - intros eff. rewrite (write_check_specA mo_ fd bs eff Hat MINV_). apply write_check_no_unmodeled.
    - intros eff mo' evs (k & _ & _ & -> & _). auto.
    - intros eff mo1 mo2 evs1 evs2 (k1 & _ & _ & -> & _) (k2 & _ & _ & -> & _). reflexivity.
  Qed.


  Lemma read_check_specA : forall m fd buf count eff,
    at_node segs (NRead fd buf count) ms -> minv (strip m) ->
    check_syscall (sys_input segs ms (Z_to_bv 64 63)) eff m = read_check fd buf count eff m.
  Proof.
    intros m fd buf count eff (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hb & Hwr) Hm.
    pose proof Hm as (M0 & M1 & M2 & MC & MF & MK & MT & ML & MM & MS). pose proof max_write_lt as (W1 & W2 & W3 & W4).
    pose proof Hwr as (Hb0 & Hbn & _).
    dispatch 63. unfold check_read, read_check. rewrite Ha0, Ha1, Ha2, in_wmem_si.
    unfold fd32. rewrite abi_low32_small by lia.
    assert (Hok : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
    { apply access_okb_below; rewrite !unsigned_lit by lia; lia. }
    assert (Hcl : rw_count_clamp (Z_to_bv 64 count) = count).
    { rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; lia). apply unsigned_lit. lia. }
    rewrite m_fds_strip in *. rewrite m_fs_strip in *.
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [e|] eqn:Hlk; [|reflexivity].
    pose proof (MK _ _ Hlk) as HK.
    destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]; try contradiction.
    - exfalso. apply MC in Hlk. rewrite unsigned_lit in Hlk by lia. lia.
    - rewrite Hok. cbn [negb].
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
      rewrite Hcl. cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
      assert (Hlen : Z.of_nat (length bs) <= count).
      { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
        unfold word_to_nat in L. rewrite unsigned_lit in L by lia. lia. }
      unfold len_word at 1.
      destruct (read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length bs)))) eqn:E.
      2:{ exfalso. refine (read_bytes_map_wr_at segs (ms_mem ms) buf count _ Hwr _ E). rewrite unsigned_lit by lia. lia. }
      destruct bs; reflexivity.
    - rewrite Hok. reflexivity.
  Qed.

  Lemma read_check_ok_iffA : forall m fd buf count eff mo' evs,
    minv (strip m) ->
    read_check fd buf count eff m = CheckOk mo' evs <-> nstep (NRead fd buf count) m eff mo' evs.
  Proof.
    intros m fd buf count eff mo' evs (_ & _ & _ & _ & MF & MK & _). unfold read_check. cbn [nstep].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
    2:{ rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
    pose proof (MK _ _ Hlk) as HK.
    destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]; try (split; [discriminate| tauto]).
    - destruct (fs_lookup (m_fs m) p) as [data|]. 2:{ split; [discriminate|tauto]. }
      cbv zeta. destruct (file_read data off (Z_to_bv 64 count)) as [|b bs'] eqn:Ebs.
      + rewrite check_ret_only_ok_iff. cbn [delivered_writes]. change (len_word (@nil byte)) with (Z_to_bv 64 0). tauto.
      + cbn [delivered_writes]. destruct eff as [ret ws zs us cs ci]. split.
        * intros H. destruct ws as [|[a bs''] [|? ?]]; try discriminate. destruct zs; [|discriminate]. destruct us; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (bv_eqb a (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
          destruct (listN_eqb bs'' (b :: bs')) eqn:E2; [|discriminate].
          destruct (bv_eqb ret (len_word (b :: bs'))) eqn:E3; [|discriminate].
          cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3.
          subst. repeat split; reflexivity.
        * intros (-> & Heff & ->). inversion Heff; subst. rewrite !bv_eqb_refl, listN_eqb_refl. reflexivity.
    - rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
  Qed.

  Lemma nstep_read_MX : forall fd buf count m mat eff moX evs,
    nstep (NRead fd buf count) (MX m mat) eff moX evs ->
    exists mo', nstep (NRead fd buf count) m eff mo' evs /\ moX = MX mo' mat.
  Proof.
    intros fd buf count m mat eff moX evs Hn. cbn [nstep] in Hn. rewrite m_fds_MX, m_fs_MX in Hn. destruct Hn as [Hevs H]. cbn [nstep].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]|]; try contradiction;
      try (destruct H as [He ->]; exists m; repeat split; assumption).
    destruct (fs_lookup (m_fs m) p) as [data|]; [|contradiction]. destruct H as [He ->].
    eexists. split; [split; [exact Hevs|]; split; [exact He| reflexivity] |]. rewrite with_fds_MX. reflexivity.
  Qed.

  Lemma nstep_read_MX' : forall fd buf count m mat eff mo' evs,
    nstep (NRead fd buf count) m eff mo' evs -> nstep (NRead fd buf count) (MX m mat) eff (MX mo' mat) evs.
  Proof.
    intros fd buf count m mat eff mo' evs Hn. cbn [nstep] in Hn. destruct Hn as [Hevs H]. cbn [nstep]. rewrite m_fds_MX, m_fs_MX.
    split; [exact Hevs|].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]|]; try contradiction;
      try (destruct H as [He ->]; auto).
    destruct (fs_lookup (m_fs m) p) as [data|]; [|contradiction]. destruct H as [He ->].
    rewrite with_fds_MX. auto.
  Qed.

  Lemma nstep_read_strip : forall fd buf count m eff mo' evs,
    nstep (NRead fd buf count) m eff mo' evs -> nstep (NRead fd buf count) (strip m) eff (strip mo') evs.
  Proof.
    intros fd buf count m eff mo' evs Hn. cbn [nstep] in Hn. destruct Hn as [Hevs H]. cbn [nstep]. rewrite m_fds_strip, m_fs_strip.
    split; [exact Hevs|].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]|]; try contradiction;
      try (destruct H as [He ->]; auto).
    destruct (fs_lookup (m_fs m) p) as [data|]; [|contradiction]. destruct H as [He ->].
    rewrite strip_with_fds. auto.
  Qed.

  Lemma nstep_read_shape : forall fd buf count m eff mo' evs,
    nstep (NRead fd buf count) m eff mo' evs ->
    m_vm_materialized mo' = m_vm_materialized m /\ m_vmmaps mo' = m_vmmaps m /\ m_vm_lazy mo' = m_vm_lazy m /\
    m_halted mo' = m_halted m /\ strip mo' = strip m \/ exists x, mo' = with_fds x m.
  Proof.
    intros fd buf count m eff mo' evs Hn. cbn [nstep] in Hn. destruct Hn as [_ H].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]|]; try contradiction;
      try (destruct H as [_ ->]; left; repeat split; reflexivity).
    destruct (fs_lookup (m_fs m) p) as [data|]; [|contradiction]. destruct H as [_ ->]. right. eexists; reflexivity.
  Qed.

  Lemma read_factsA : forall fd buf count,
    at_nodeA segs (NRead fd buf count) RNG ms -> node_factsA A RNG ms mo mo_ (NRead fd buf count).
  Proof.
    intros fd buf count [Hat Hcov]. exists (Z_to_bv 64 63). split; [exact (proj1 Hat)|].
    pose proof Hat as (_ & Hfd & _ & _ & _ & Hc & Hb & _). cbn [ncov] in Hcov. pose proof max_write_lt as (T1 & T2 & T3 & T4); pose proof TASK_SIZE_val as T5.
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite (read_check_specA mo_ fd buf count eff Hat MINV_) in HC.
      apply (read_check_ok_iffA mo_) in HC; [| exact MINV_].
      pose proof (read_nstep_strip _ _ _ _ _ _ _ HC) as Hst.
      rewrite mo__MX in HC. destruct (nstep_read_MX _ _ _ _ _ _ _ _ HC) as (mo' & Hn & ->).
      apply succ_ok_neutral.
      + rewrite Hst. exact Hn.
      + destruct (nstep_read_shape _ _ _ _ _ _ _ Hn) as [(E & _)|(x & ->)]; [rewrite E; exact CAN| cbn; exact CAN].
      + destruct (nstep_read_shape _ _ _ _ _ _ _ Hn) as [(_ & E & _)|(x & ->)]; [exact E| reflexivity].
      + destruct (nstep_read_shape _ _ _ _ _ _ _ Hn) as [(_ & _ & E & _)|(x & ->)]; [exact E| reflexivity].
      +
        pose proof Hat as (_ & _ & _ & _ & _ & _ & _ & Hwr). pose proof Hwr as (Hb0 & Hbn & _).
        cbn [nstep] in Hn. destruct Hn as [_ H]. rewrite <- Hst.
        destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]|]; try contradiction;
          try (destruct H as [-> _]; constructor).
        destruct (fs_lookup (m_fs mo) p) as [data|]; [|contradiction]. destruct H as [-> _].
        pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. unfold word_to_nat in L. rewrite unsigned_lit in L by lia.
        unfold delivered_writes. destruct (file_read data off (Z_to_bv 64 count)) as [|b bs'] eqn:Ebs; [constructor|].
        unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app rstrip write_accesses length].
        eapply cov_one_lit; [exact Hcov| lia | cbn [length] in L; lia].
    - intros eff mo' evs Hn. cbn [nstepA] in Hn. pose proof (read_nstep_strip _ _ _ _ _ _ _ Hn) as Hst.
      exists eff, (MX mo' matl). split; [|exact Hst].
      rewrite (read_check_specA mo_ fd buf count eff Hat MINV_). apply (read_check_ok_iffA mo_); [exact MINV_|].
      rewrite mo__MX. apply nstep_read_MX'. exact Hn.
    - intros eff. rewrite (read_check_specA mo_ fd buf count eff Hat MINV_). apply read_check_no_unmodeled.
    - intros eff mo' evs Hn. cbn [nstepA] in Hn.
      destruct (read_pres fd buf count (strip mo) eff (strip mo') evs MINV Hh (nstep_read_strip _ _ _ _ _ _ _ Hn)) as [Hh' Hm'].
      split; [exact Hh'|]. split; [exact Hm'|].
      destruct (nstep_read_shape _ _ _ _ _ _ _ Hn) as [(E & _)|(x & ->)]; [rewrite E; exact CAN| cbn; exact CAN].
    - intros eff mo1 mo2 evs1 evs2 [_ H1] [_ H2].
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw| |sid sd st|ctx|fam|aid af]|]; try contradiction;
        try (destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity).
      destruct (fs_lookup (m_fs mo) p) as [data|]; [|contradiction]. destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
  Qed.


  Lemma open_result_MX : forall m mat ent eff moX,
    open_result (MX m mat) ent eff moX <-> exists mo', open_result m ent eff mo' /\ moX = MX mo' mat.
  Proof.
    intros m mat ent eff moX. unfold open_result. rewrite m_fds_MX, with_fds_MX. split.
    - intros [(e & He & Heff & ->) | (Hl & Heff & ->)].
      + exists m. split; [left; eauto| reflexivity].
      + eexists. split; [right; eauto| reflexivity].
    - intros (mo' & [(e & He & Heff & ->) | (Hl & Heff & ->)] & ->); [left; eauto | right; auto].
  Qed.

  Lemma open_result_strip : forall m ent eff mo',
    open_result m ent eff mo' -> open_result (strip m) ent eff (strip mo').
  Proof.
    intros m ent eff mo' [(e & He & Heff & ->) | (Hl & Heff & ->)]; unfold open_result; rewrite m_fds_strip; [left; eauto|].
    right. rewrite strip_with_fds. auto.
  Qed.

  Lemma nstep_open_MX : forall path m mat eff moX evs,
    nstep (NOpen path) (MX m mat) eff moX evs <-> exists mo', nstep (NOpen path) m eff mo' evs /\ moX = MX mo' mat.
  Proof.
    intros path m mat eff moX evs. cbn [nstep]. rewrite m_fs_MX.
    destruct (path_max <=? length path)%nat.
    { split; [intros [He [Hf ->]]; exists m; auto | intros (mo' & [He [Hf ->]] & ->); auto]. }
    destruct path as [|c path'].
    { split; [intros [He [Hf ->]]; exists m; auto | intros (mo' & [He [Hf ->]] & ->); auto]. }
    destruct (path_is_dirref (c :: path')).
    { rewrite open_result_MX. split; [intros [He (mo' & Ho & ->)]; eauto | intros (mo' & [He Ho] & ->); eauto]. }
    destruct (fs_lookup (m_fs m) (c :: path')).
    - rewrite open_result_MX. split; [intros [He (mo' & Ho & ->)]; eauto | intros (mo' & [He Ho] & ->); eauto].
    - split; [intros [He [Hf ->]]; exists m; auto | intros (mo' & [He [Hf ->]] & ->); auto].
  Qed.

  Lemma nstep_open_strip : forall path m eff mo' evs,
    nstep (NOpen path) m eff mo' evs -> nstep (NOpen path) (strip m) eff (strip mo') evs.
  Proof.
    intros path m eff mo' evs. cbn [nstep]. rewrite m_fs_strip. intros [He H]. split; [exact He|].
    destruct (path_max <=? length path)%nat. { destruct H as [Hf ->]; auto. }
    destruct path as [|c path']. { destruct H as [Hf ->]; auto. }
    destruct (path_is_dirref (c :: path')). { apply open_result_strip. exact H. }
    destruct (fs_lookup (m_fs m) (c :: path')); [apply open_result_strip; exact H|]. destruct H as [Hf ->]; auto.
  Qed.

  Lemma nstep_open_shape : forall path m eff mo' evs,
    nstep (NOpen path) m eff mo' evs -> mo' = m \/ exists x, mo' = with_fds x m.
  Proof.
    intros path m eff mo' evs [_ H].
    assert (Hor : forall ent, open_result m ent eff mo' -> mo' = m \/ exists x, mo' = with_fds x m).
    { intros ent [(e & _ & _ & ->) | (_ & _ & ->)]; [left; reflexivity| right; eexists; reflexivity]. }
    destruct (path_max <=? length path)%nat. { destruct H as [_ ->]; auto. }
    destruct path as [|c path']. { destruct H as [_ ->]; auto. }
    destruct (path_is_dirref (c :: path')). { exact (Hor _ H). }
    destruct (fs_lookup (m_fs m) (c :: path')); [exact (Hor _ H)|]. destruct H as [_ ->]; auto.
  Qed.

  Lemma det_of_checker : forall (r : check_result) (P : Model -> list event -> Prop) mo1 mo2 evs1 evs2,
    (forall mo' evs, r = CheckOk mo' evs <-> P mo' evs) -> P mo1 evs1 -> P mo2 evs2 -> mo1 = mo2.
  Proof. intros r P mo1 mo2 evs1 evs2 H H1 H2. apply H in H1. apply H in H2. rewrite H1 in H2. congruence. Qed.

  Lemma open_factsA : forall path,
    at_nodeA segs (NOpen path) RNG ms -> node_factsA A RNG ms mo mo_ (NOpen path).
  Proof.
    intros path [Hat Hcov]. exists (Z_to_bv 64 56). split; [exact (proj1 Hat)|]. cbn [ncov] in Hcov.
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite (open_check_spec segs ms mo_ path eff Hat) in HC.
      rewrite open_check_eq in HC. apply check_copyins_after_ok_iff in HC as [Hci Hb].
      rewrite clear_rstrip in Hb. apply open_body_ok_iff in Hb.
      rewrite mo__MX in Hb. apply nstep_open_MX in Hb as (mo' & Hn & ->).
      apply succ_ok_neutral.
      + exact Hn.
      + destruct (nstep_open_shape _ _ _ _ _ Hn) as [-> | (x & ->)]; [exact CAN| cbn; exact CAN].
      + destruct (nstep_open_shape _ _ _ _ _ Hn) as [-> | (x & ->)]; reflexivity.
      + destruct (nstep_open_shape _ _ _ _ _ Hn) as [-> | (x & ->)]; reflexivity.
      + unfold syscall_effect_accesses. rewrite Hci.
        assert (Hw : eff_writes eff = []).
        { pose proof (open_nstep_strip _ _ _ _ _ Hn) as Hs.
          destruct eff as [r ws zs us cs ci]. cbn [rstrip] in Hs |- *. cbn [eff_writes].
          cbn [nstep rstrip] in Hn. destruct Hn as [_ H].
          assert (Hor : forall ent m', open_result mo ent (mkEffectU r ws zs us cs []) m' -> ws = []).
          { intros ent m' [(e & _ & E & _) | (_ & E & _)]; unfold efferr, eff0 in E; injection E; intros; assumption. }
          destruct (path_max <=? length path)%nat. { destruct H as [E _]. unfold efferr, eff0 in E. injection E; intros; assumption. }
          destruct path as [|c path']. { destruct H as [E _]. unfold efferr, eff0 in E. injection E; intros; assumption. }
          destruct (path_is_dirref (c :: path')). { exact (Hor _ _ H). }
          destruct (fs_lookup (m_fs mo) (c :: path')); [exact (Hor _ _ H)|]. destruct H as [E _]. unfold efferr, eff0 in E. injection E; intros; assumption. }
        rewrite Hw. cbn [write_accesses app]. unfold open_ci. rewrite app_nil_r.
        eapply cov_one; [exact Hcov| lia].
    - intros eff mo' evs Hn. cbn [nstepA] in Hn.
      destruct (open_check_complete (areg ms 11) path eff (MX mo matl) (MX mo' matl) evs) as (effk & Hck & Hst).
      { apply nstep_open_MX. eauto. }
      exists effk, (MX mo' matl). rewrite (open_check_spec segs ms mo_ path effk Hat), mo__MX. auto.
    - intros eff. rewrite (open_check_spec segs ms mo_ path eff Hat). apply open_check_no_unmodeled.
    - intros eff mo' evs Hn. cbn [nstepA] in Hn.
      destruct (open_pres path (strip mo) eff (strip mo') evs MINV Hh (nstep_open_strip _ _ _ _ _ Hn)) as [Hh' Hm'].
      split; [exact Hh'|]. split; [exact Hm'|].
      destruct (nstep_open_shape _ _ _ _ _ Hn) as [-> | (x & ->)]; [exact CAN| cbn; exact CAN].
    - intros eff mo1 mo2 evs1 evs2 H1 H2. eapply (det_of_checker (open_body path eff mo)); [intros; apply open_body_ok_iff| exact H1| exact H2].
  Qed.


  Lemma check_ret_only_accesses : forall eff r m evs m' evs',
    check_ret_only eff r m evs = CheckOk m' evs' -> syscall_effect_accesses eff = [].
  Proof.
    intros eff r m evs m' evs' H. apply check_ret_only_ok_iff in H as (-> & _). reflexivity.
  Qed.

  Lemma close_factsA : forall fd,
    at_nodeA segs (NClose fd) RNG ms -> node_factsA A RNG ms mo mo_ (NClose fd).
  Proof.
    intros fd [[Hsvc [Hfd Ha0]] _]. exists (Z_to_bv 64 57). split; [exact Hsvc|].
    assert (Hchk : forall m eff, check_syscall (sys_input segs ms (Z_to_bv 64 57)) eff m =
              match fd_lookup (m_fds m) (Z_to_bv 64 fd) with
              | None => check_ret_only eff (errno_ret EBADF) m []
              | Some _ => check_ret_only eff (Z_to_bv 64 0) (with_fds (fd_remove (m_fds m) (Z_to_bv 64 fd)) m) []
              end).
    { intros m eff. dispatch 57. unfold check_close. rewrite Ha0. unfold fd32. rewrite abi_low32_small by lia. reflexivity. }
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite Hchk, mo__MX, m_fds_MX, with_fds_MX in HC.
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk;
        (pose proof (check_ret_only_accesses _ _ _ _ _ _ HC) as Hacc; apply check_ret_only_ok_iff in HC as (-> & -> & ->)).
      + eapply succ_ok_nil; [| exact Hacc |].
        * cbn [nstepA nstep rstrip]. split; [reflexivity|]. split; [lia|]. rewrite Hlk. unfold eff0. auto.
        * split; [apply same_but_mat_MX|]. split; [cbn; exact CAN|]. cbn. rewrite <- (m_vm_materialized_MX mo matl), <- mo__MX.
          destruct INV as [_ ND AL _ _]. auto.
      + eapply succ_ok_nil; [| exact Hacc |].
        * cbn [nstepA nstep rstrip]. split; [reflexivity|]. split; [lia|]. rewrite Hlk. unfold efferr, eff0. auto.
        * rewrite <- mo__MX. exact MR.
    - intros eff mo' evs Hn. cbn [nstepA nstep] in Hn. destruct Hn as (-> & _ & H).
      exists eff. rewrite Hchk, mo__MX, m_fds_MX, with_fds_MX.
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct H as [-> ->].
      + exists (MX (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) matl). split; [apply check_ret_only_ok_iff; auto| reflexivity].
      + exists (MX mo matl). split; [apply check_ret_only_ok_iff; auto| reflexivity].
    - intros eff. rewrite Hchk. destruct (fd_lookup _ _); apply check_ret_only_no_unmodeled.
    - intros eff mo' evs Hn. cbn [nstepA] in Hn.
      assert (Hn' : nstep (NClose fd) (strip mo) eff (strip mo') evs).
      { cbn [nstep] in Hn |- *. rewrite m_fds_strip. destruct Hn as (He & Hr & H). split; [exact He|]. split; [exact Hr|].
        destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct H as [-> ->]; [rewrite strip_with_fds|]; auto. }
      destruct (close_pres fd (strip mo) eff (strip mo') evs MINV Hh Hn') as [Hh' Hm'].
      split; [exact Hh'|]. split; [exact Hm'|].
      cbn [nstep] in Hn. destruct Hn as (_ & _ & H). destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct H as [_ ->]; [cbn|]; exact CAN.
    - intros eff mo1 mo2 evs1 evs2 Hn1 Hn2. cbn [nstepA nstep] in Hn1, Hn2.
      destruct Hn1 as (_ & _ & H1). destruct Hn2 as (_ & _ & H2).
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity.
  Qed.

  Lemma ioctl_factsA : forall fd req,
    at_nodeA segs (NIoctl fd req) RNG ms -> node_factsA A RNG ms mo mo_ (NIoctl fd req).
  Proof.
    intros fd req [(Hsvc & Hfd & Hreq & Ha0 & Ha1) _]. exists (Z_to_bv 64 29). split; [exact Hsvc|].
    assert (Hchk : forall m eff, minv (strip m) ->
              check_syscall (sys_input segs ms (Z_to_bv 64 29)) eff m = check_ret_only eff (errno_ret ENOTTY) m []).
    { intros m eff Hm. dispatch 29. unfold check_ioctl. rewrite Ha0, Ha1. subst req.
      unfold fd32, cmd32. rewrite !abi_low32_small by lia.
      destruct Hm as (M0 & M1 & M2 & _).
      assert (Hl : exists c, fd_lookup (m_fds (strip m)) (Z_to_bv 64 fd) = Some (FdChannel c)).
      { assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
      destruct Hl as [c Hc]. change (m_fds (strip m)) with (m_fds m) in Hc. rewrite Hc. reflexivity. }
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite (Hchk _ _ MINV_) in HC.
      pose proof (check_ret_only_accesses _ _ _ _ _ _ HC) as Hacc. apply check_ret_only_ok_iff in HC as (-> & -> & ->).
      eapply succ_ok_nil; [| exact Hacc | exact MR]. cbn [nstepA nstep rstrip]. unfold efferr, eff0. auto.
    - intros eff mo' evs Hn. cbn [nstepA nstep] in Hn. destruct Hn as (-> & -> & ->).
      exists (efferr ENOTTY), mo_. rewrite (Hchk _ _ MINV_). split; [apply check_ret_only_ok_iff; auto| reflexivity].
    - intros eff. rewrite (Hchk _ _ MINV_). apply check_ret_only_no_unmodeled.
    - intros eff mo' evs Hn. cbn [nstepA nstep] in Hn. destruct Hn as (_ & _ & ->). split; [exact Hh| exact Hminv].
    - intros eff mo1 mo2 evs1 evs2 (_ & _ & ->) (_ & _ & ->). reflexivity.
  Qed.

  Lemma set_tid_factsA :
    at_nodeA segs NSetTid RNG ms -> node_factsA A RNG ms mo mo_ NSetTid.
  Proof.
    intros [Hsvc _]. exists (Z_to_bv 64 96). split; [exact Hsvc|].
    assert (Hchk : forall m eff, check_syscall (sys_input segs ms (Z_to_bv 64 96)) eff m = check_set_tid_address eff m).
    { intros m eff. dispatch 96. reflexivity. }
    assert (Hiff : forall m (eff : resp) mo' evs, check_set_tid_address eff m = CheckOk mo' evs <-> nstep NSetTid m eff mo' evs).
    { intros m [ret ws zs us cs ci] mo' evs. unfold check_set_tid_address. cbn [nstep]. unfold eff0. split.
      + intros H. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (m_tid m) as [t0|].
        * destruct (bv_eqb ret t0) eqn:E; [|discriminate]. apply bv_eqb_eq in E. inversion H; subst.
          split; [reflexivity|]. exists t0. auto.
        * destruct ((0 <? bv_unsigned ret) && (bv_unsigned ret <? PID_MAX_ENVELOPE)) eqn:E; [|discriminate].
          inversion H; subst. apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
          split; [reflexivity|]. exists ret. auto.
      + intros (-> & t & Heff & Ht). inversion Heff; subst. destruct (m_tid m) as [t0|].
        * destruct Ht as [-> ->]. rewrite bv_eqb_refl. reflexivity.
        * destruct Ht as [[H1 H2] ->]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity. }
    assert (HMX : forall eff moX evs, nstep NSetTid (MX mo matl) eff moX evs ->
              exists mo', nstep NSetTid mo eff mo' evs /\ moX = MX mo' matl /\ (mo' = mo \/ exists t, mo' = with_tid t mo)).
    { intros eff moX evs Hn. cbn [nstep] in Hn. rewrite m_tid_MX in Hn. destruct Hn as (He & t & Heff & Ht).
      destruct (m_tid mo) as [t0|] eqn:Et.
      + destruct Ht as [Htt ->]. exists mo. split; [| auto]. cbn [nstep]. rewrite Et. eauto 6.
      + destruct Ht as [Hr ->]. exists (with_tid t mo). rewrite with_tid_MX. split; [| split; [reflexivity| right; eauto]]. cbn [nstep]. rewrite Et. eauto 6. }
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite Hchk, mo__MX in HC. apply Hiff in HC.
      assert (Hacc : syscall_effect_accesses eff = [] /\ rstrip eff = eff).
      { cbn [nstep] in HC. destruct HC as (_ & t & -> & _). split; reflexivity. }
      destruct Hacc as [Hacc Hst].
      destruct (HMX _ _ _ HC) as (mo' & Hn & -> & Hsh).
      eapply succ_ok_nil; [rewrite Hst; exact Hn| exact Hacc|].
      split; [apply same_but_mat_MX|]. split; [destruct Hsh as [-> | (t & ->)]; [|cbn]; exact CAN|].
      rewrite m_vm_materialized_MX. destruct INV as [_ ND AL _ _]. unfold matl. auto.
    - intros eff mo' evs Hn. cbn [nstepA] in Hn. exists eff, (MX mo' matl). split; [| cbn [nstep] in Hn; destruct Hn as (_ & t & -> & _); reflexivity].
      rewrite Hchk, mo__MX. apply Hiff. cbn [nstep] in Hn |- *. rewrite m_tid_MX.
      destruct Hn as (He & t & Heff & Ht). split; [exact He|]. exists t. split; [exact Heff|].
      destruct (m_tid mo); destruct Ht as [X ->]; [|rewrite with_tid_MX]; auto.
    - intros [ret ws zs us cs ci]. rewrite Hchk. unfold check_set_tid_address.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (m_tid mo_); [destruct (bv_eqb _ _); discriminate| destruct (_ && _); discriminate].
    - intros eff mo' evs Hn. cbn [nstepA nstep] in Hn. destruct Hn as (_ & t & _ & Ht).
      destruct (m_tid mo); destruct Ht as [_ ->].
      + split; [exact Hh|]. exact Hminv.
      + split; [exact Hh|]. split; [rewrite strip_with_tid; exact MINV| cbn; exact CAN].
    - intros eff mo1 mo2 evs1 evs2 H1 H2. eapply (det_of_checker (check_set_tid_address eff mo)); [intros; apply Hiff| exact H1| exact H2].
  Qed.


  Lemma iov_array_cov : forall a k,
    rng RNG a (16 * Z.of_nat k) -> Forall (acc_in RNG) (iov_array_accesses a k).
  Proof.
    intros a k. revert a. induction k as [|k IH]; intros a HR; cbn [iov_array_accesses]; [constructor|].
    constructor.
    - unfold acc_in, wa. cbn [fst snd]. pose proof (rng_bounds _ _ _ HR).
      rewrite unsigned_lit by lia. destruct HR as (_ & _ & H'). apply H'; lia.
    - apply IH. eapply rng_sub; [exact HR| lia | lia].
  Qed.

  Lemma iov_prefix_cov : forall iovs bufs,
    Forall2 (fun (iov : word * word) (bs : list byte) =>
               snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
               bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
               rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs bufs ->
    Z.of_nat (length (concat bufs)) < 2^64 ->
    forall k, Forall (acc_in RNG) (iov_prefix_accesses iovs k).
  Proof.
    intros iovs bufs HF. induction HF as [| [base len] bs iovs bufs (Hl & Hts & Hb & HR) HF IH]; intros Htot k.
    - destruct k; constructor.
    - cbn [concat] in Htot. rewrite length_app in Htot. cbn [fst snd] in *.
      destruct k as [|k']; cbn [iov_prefix_accesses]; [constructor|].
      subst len. rewrite word_to_nat_bounded_eq_min, word_to_nat_of_nat by lia.
      destruct (Nat.eqb_spec (Nat.min (length bs) (S k')) 0) as [E|E].
      + apply IH. lia.
      + constructor; [| apply IH; lia]. eapply rng_acc_var; [exact HR|]. lia.
  Qed.

  Lemma writev_check_specA : forall m fd iovs bufs eff,
    at_node segs (NWritev fd bufs) ms -> minv (strip m) ->
    bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) ->
    Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                           bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
                           bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
    check_syscall (sys_input segs ms (Z_to_bv 64 66)) eff m = writev_check fd (areg ms 11) iovs bufs eff m.
  Proof.
    intros m fd iovs bufs eff (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Harr & Hrom & _) Hm Hiov Hbufs.
    pose proof max_write_lt as (W1 & W2 & W3 & W4). pose proof MAX_RW_COUNT_val. pose proof IOV_MAX_val.
    destruct (iovs_ok_of_at segs _ _ _ Hrom Hbufs) as [Hok HL].
    pose proof (Forall2_length Hbufs) as Hleq.
    pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
    dispatch 66. unfold check_writev. rewrite Ha0, Ha2, in_mem_si.
    (* c2: + the channel-reader gate, as Lib/Nodes writev_check_spec *)
    destruct (std_chanA m fd Hm Hfd) as [Hlk Hw]. rewrite Hlk, Hw, (minv_reader_stripA m Hm).
    unfold iovcnt32. rewrite abi_low32_small by lia. rewrite <- Hleq.
    rewrite <- (wa_unsigned_id (areg ms 11)).
    destruct (import_iovecs_bytes_in iovs (ms_read_byte ms) (bv_unsigned (areg ms 11))) as [-> ->];
      [eapply bytes_at_in; eassumption | exact HL | lia | lia |].
    cbv zeta. unfold writev_gathered. rewrite cap_iovecs_id by lia. rewrite Htotal.
    rewrite (gather_prefix_full _ _ _ (gather_iovecs_ok _ _ _ Hok)).
    unfold writev_check. cbv zeta. rewrite wa_unsigned.
    2:{ pose proof (bv_unsigned_in_range 64 (areg ms 11)). unfold bv_modulus in *. lia. }
    destruct (Nat.eqb_spec (length (concat bufs)) 0) as [E|E].
    - replace (Z.of_nat (length (concat bufs)) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
    - replace (Z.of_nat (length (concat bufs)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold len_word. replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat (length (concat bufs))))) with false.
      2:{ symmetry. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia. }
      reflexivity.
  Qed.

  Lemma writev_check_accesses : forall fd iov iovs bufs eff m mo' evs,
    writev_check fd iov iovs bufs eff m = CheckOk mo' evs ->
    eff_writes eff = [] /\
    exists k, eff_copyins eff = iov_array_accesses (bv_unsigned iov) (length iovs) ++ iov_prefix_accesses iovs k.
  Proof.
    intros fd iov iovs bufs eff m mo' evs H. unfold writev_check in H. cbv zeta in H.
    destruct (length (concat bufs) =? 0)%nat.
    - apply check_ret_only_copyins_ok_iff in H as (-> & _ & _). cbn. split; [reflexivity|].
      exists 0%nat. destruct iovs as [|[? ?] ?]; cbn; rewrite ?app_nil_r; reflexivity.
    - destruct eff as [ret ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct us; [|discriminate]. destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret) && _ && _)%bool; [|discriminate].
      destruct (access_ranges_eqb ci _) eqn:Eb; [|discriminate].
      apply access_ranges_eqb_eq in Eb. cbn. split; [reflexivity|]. eauto.
  Qed.

  Lemma writev_factsA : forall fd bufs,
    at_nodeA segs (NWritev fd bufs) RNG ms -> node_factsA A RNG ms mo mo_ (NWritev fd bufs).
  Proof.
    intros fd bufs HatA. pose proof (at_nodeA_at_node segs (NWritev fd bufs) RNG ms I HatA) as Hat.
    destruct HatA as (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Harr & Hrom & Hcov & iovs & Hiov & HF).
    assert (Hbufs : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                                          bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE /\
                                          bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs).
    { eapply Forall2_impl; [| exact HF]. cbn. intros a b (X & X2 & Y & _). auto. }
    pose proof (Forall2_length HF) as Hleq. pose proof max_write_lt as (W1 & W2 & W3 & W4).
    exists (Z_to_bv 64 66). split; [exact Hsvc|].
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite (writev_check_specA mo_ fd iovs bufs eff Hat MINV_ Hiov Hbufs) in HC.
      pose proof (writev_check_accesses _ _ _ _ _ _ _ _ HC) as (Hw & k & Hci).
      apply writev_check_ok in HC. pose proof HC as [-> HC']. rewrite mo__MX. apply succ_ok_neutral; try reflexivity.
      + cbn [nstepA nstep]. split; [reflexivity| exact HC'].
      + exact CAN.
      + unfold syscall_effect_accesses. rewrite Hci, Hw. cbn [write_accesses]. rewrite app_nil_r.
        apply Forall_app. split.
        * apply iov_array_cov. rewrite Hleq. exact Hcov.
        * eapply iov_prefix_cov; [exact HF| lia].
    - intros eff mo' evs Hn. cbn [nstepA] in Hn. pose proof Hn as [-> _].
      destruct (writev_check_complete fd (areg ms 11) iovs bufs eff mo_ mo_ evs ltac:(lia)) as (effk & Hck & Hst).
      { cbn [nstep] in Hn |- *. split; [reflexivity| exact (proj2 Hn)]. }
      exists effk, mo_. rewrite (writev_check_specA mo_ fd iovs bufs effk Hat MINV_ Hiov Hbufs). auto.
    - intros eff. rewrite (writev_check_specA mo_ fd iovs bufs eff Hat MINV_ Hiov Hbufs). apply writev_check_no_unmodeled.
    - intros eff mo' evs [-> _]. auto.
    - intros eff mo1 mo2 evs1 evs2 [-> _] [-> _]. reflexivity.
  Qed.


  Ltac crush_ok H :=
    repeat (cbv zeta beta iota in H;
            lazymatch type of H with
            | CheckReject = CheckOk _ _ => discriminate H
            | CheckUnmodeled = CheckOk _ _ => discriminate H
            | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_ok_iff in H as (H & ? & ?)
            | (match ?x with _ => _ end) = _ => destruct x
            end);
    repeat match goal with
           | E : mkEffectU _ _ _ _ _ _ = mkEffectU _ _ _ _ _ _ |- _ => injection E; clear E; intros; subst
           | E : CheckOk _ _ = CheckOk _ _ |- _ => injection E; clear E; intros; subst
           end.

  Definition eff_quiet (eff : resp) (evs : list event) : Prop :=
    syscall_effect_accesses eff = [] /\ rstrip eff = eff /\ evs = [].

  Lemma check_brk_quiet : forall req eff m m' evs, check_brk req eff m = CheckOk m' evs -> eff_quiet eff evs.
  Proof. intros req [r ws zs us cs ci] m m' evs H. unfold check_brk in H. crush_ok H; repeat split; reflexivity. Qed.

  Lemma check_munmap_quiet : forall a l eff m m' evs, check_munmap a l eff m = CheckOk m' evs -> eff_quiet eff evs.
  Proof. intros a l [r ws zs us cs ci] m m' evs H. unfold check_munmap in H. crush_ok H; repeat split; reflexivity. Qed.

  Lemma check_mprotect_quiet : forall a l pr eff m m' evs, check_mprotect a l pr eff m = CheckOk m' evs -> eff_quiet eff evs.
  Proof. intros a l pr [r ws zs us cs ci] m m' evs H. unfold check_mprotect in H. crush_ok H; repeat split; reflexivity. Qed.

  Lemma check_mmap_quiet : forall a l pr fl fd off eff m m' evs,
    check_mmap a l pr fl fd off eff m = CheckOk m' evs -> eff_quiet eff evs.
  (* c2: + check_mmap_fixed_overflow, as Lib/Nodes check_mmap_shape *)
  Proof. intros a l pr fl fd off [r ws zs us cs ci] m m' evs H. unfold check_mmap, check_mmap_fixed_overflow in H. crush_ok H; repeat split; reflexivity. Qed.

  Lemma m_vmmaps_with_mmap_destroyedA : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
  Proof. reflexivity. Qed.
  Ltac init_sp_solve :=
    rewrite ?vmmaps_with_mmap_replacement, ?vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_destroyedA,
            ?m_vmmaps_with_vmmaps; try reflexivity.
  Lemma check_brk_init_sp : forall req eff m m' evs,
    check_brk req eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. intros req eff m m' evs H. pose proof (check_brk_shape _ _ _ _ _ H) as [(_ & _ & _ & _ & _ & _ & E & _) _]. exact E. Qed.
  Lemma check_munmap_init_sp : forall a l eff m m' evs,
    check_munmap a l eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. intros a l eff m m' evs H. pose proof (check_munmap_shape _ _ _ _ _ _ H) as [(_ & _ & _ & _ & _ & _ & E & _) _]. exact E. Qed.
  Lemma check_mprotect_init_sp : forall a l pr eff m m' evs,
    check_mprotect a l pr eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. intros a l pr eff m m' evs H. pose proof (check_mprotect_shape _ _ _ _ _ _ _ H) as [(_ & _ & _ & _ & _ & _ & E & _) _]. exact E. Qed.
  Lemma check_mmap_init_sp : forall a l pr fl fd off eff m m' evs,
    check_mmap a l pr fl fd off eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof.
    (* c2: + check_mmap_fixed_overflow, as Lib/Nodes check_mmap_shape *)
    intros a l pr fl fd off [r ws zs us cs ci] m m' evs H. unfold check_mmap, check_mmap_fixed_overflow in H. crush_ok H; init_sp_solve.
  Qed.

  Lemma mm_succ_ok : forall n eff m f evs,
    nstepA n mo (rstrip eff) m evs ->
    syscall_effect_accesses eff = [] ->
    m_vm_materialized m = List.filter f (m_vm_materialized mo) ->
    succ_ok A n mo mo_ eff (MX m (List.filter f matl)) evs.
  Proof.
    intros n eff m f evs Hn Hacc Hm. eapply succ_ok_nil; [exact Hn| exact Hacc|].
    split; [apply same_but_mat_MX|]. split; [rewrite Hm, CAN; reflexivity|].
    rewrite m_vm_materialized_MX. destruct INV as [_ ND AL _ _]. split; [apply NoDup_filter; exact ND|].
    intros p Hp. apply AL. apply (incl_filter f matl p Hp).
  Qed.

  (* c2 (NEW): at Lib/Nodes vm_only also pins m_kernel and
     vm_mmap_base, so vm_only_with_vmmaps takes the mmap base too. minv reads neither: this is minv_vm_only proof
     for a with_vmmaps update that keeps vm_init_sp. *)
  Lemma minv_with_vmmapsA : forall h m, vm_init_sp h = vm_init_sp (m_vmmaps m) -> minv m -> minv (with_vmmaps h m).
  Proof.
    intros h m Hsp Hm.
    assert (Hf : m_fd (with_vmmaps h m) = m_fd m) by reflexivity.
    assert (Hs : m_fsys (with_vmmaps h m) = m_fsys m) by reflexivity.
    assert (Hp : m_proc (with_vmmaps h m) = m_proc m) by reflexivity.
    assert (Hsp2 : vm_init_sp (m_vmmaps (with_vmmaps h m)) = vm_init_sp (m_vmmaps m))
      by (rewrite m_vmmaps_with_vmmaps; exact Hsp).
    pose proof Hm as (_ & _ & _ & _ & _ & _ & _ & ML & MM & _).
    assert (L1 : m_vm_lazy (with_vmmaps h m) = []) by exact ML.
    assert (L2 : m_vm_materialized (with_vmmaps h m) = []) by exact MM.
    unfold minv in *. unfold m_fds, m_fs, m_tid, m_channel_reader in *. rewrite Hf, Hs, Hp, Hsp2. rewrite L1, L2. tauto.
  Qed.

  Lemma minvA_mm_post : forall m f,
    strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
    m_vm_materialized m = List.filter f (m_vm_materialized mo) ->
    vm_init_sp (m_vmmaps m) = vm_init_sp (m_vmmaps mo) ->
    m_halted m = None /\ minvA m.
  Proof.
    intros m f S Hm Hsp. split; [| split].
    - rewrite <- (m_halted_strip m), S. cbn. exact Hh.
    - (* c2: minv_with_vmmapsA in place of minv_vm_only + vm_only_with_vmmaps *)
      rewrite S. apply minv_with_vmmapsA; [rewrite Hsp; reflexivity| exact MINV].
    - rewrite Hm, CAN. reflexivity.
  Qed.

  Lemma LEN : (length matl <= NMAX)%nat.
  Proof. pose proof (ainv_len _ _ _ _ INV) as L. exact L. Qed.

  Lemma mm_factsA : forall n x8 (chk : resp -> Model -> check_result),
    ms_svc_pending ms = Some x8 ->
    (forall eff m, check_syscall (sys_input segs ms x8) eff m = chk eff m) ->
    (forall eff m' evs, nstepA n mo eff m' evs <-> chk eff mo = CheckOk m' evs) ->
    (forall eff, relX mo matl (chk eff (MX mo matl)) (chk eff mo)) ->
    (forall eff m m' evs, chk eff m = CheckOk m' evs -> eff_quiet eff evs) ->
    (forall eff m m' evs, chk eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m)) ->
    (forall eff, chk eff mo_ <> CheckUnmodeled) ->
    node_factsA A RNG ms mo mo_ n.
  Proof.
    intros n x8 chk Hsvc Hchk Hiff Hx Hq Hsp Hnu. exists x8. split; [exact Hsvc|].
    split; [|split; [|split; [|split]]].
    - intros eff moX evs HC. rewrite Hchk, mo__MX in HC.
      pose proof (Hx eff) as R. rewrite HC in R. apply relX_ok_l in R as (m & f & Hc & S & -> & Hm).
      pose proof (Hq _ _ _ _ Hc) as (Hacc & Hst & ->).
      apply mm_succ_ok; [| exact Hacc| exact Hm]. rewrite Hst. apply Hiff. exact Hc.
    - intros eff m' evs Hn. apply Hiff in Hn. pose proof (Hq _ _ _ _ Hn) as (Hacc & Hst & ->).
      pose proof (Hx eff) as R. rewrite Hn in R. apply relX_ok_r in R as (S & f & Hc & Hm).
      exists eff, (MX m' (List.filter f matl)). rewrite Hchk, mo__MX. auto.
    - intros eff. rewrite Hchk. apply Hnu.
    - intros eff m' evs Hn. apply Hiff in Hn.
      pose proof (Hx eff) as R. rewrite Hn in R. apply relX_ok_r in R as (S & f & Hc & Hm).
      eapply minvA_mm_post; [eassumption| eassumption| exact (Hsp _ _ _ _ Hn)].
    - intros eff mo1 mo2 evs1 evs2 H1 H2. apply Hiff in H1. apply Hiff in H2. rewrite H1 in H2. congruence.
  Qed.

  (* forced-only port: the allocation nodes over the filtered relation. *)
  Lemma spurious_mm_iff : forall x8 (chk : resp -> Model -> check_result) (i : SyscallInput),
    (forall eff m, check_syscall (sys_input segs ms x8) eff m = chk eff m) ->
    (forall eff m, check_syscall i eff m = chk eff m) ->
    in_sysno (sys_input segs ms x8) = in_sysno i -> in_arg (sys_input segs ms x8) 0 = in_arg i 0 ->
    (forall eff, relX mo matl (chk eff (MX mo matl)) (chk eff mo)) ->
    forall eff, spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ eff <->
                spurious_refusal_cfg alloc_forced_cfg i mo eff.
  Proof.
    intros x8 chk i Hchk Hchki Hno Ha0 Hx eff.
    apply spurious_iff_X; [exact Hno| exact Ha0| rewrite mo__MX, m_vmmaps_MX; reflexivity|].
    intros e. rewrite Hchk, Hchki, mo__MX. split; intros (m' & evs & H).
    - pose proof (Hx e) as R. rewrite H in R. apply relX_ok_l in R as (m & f & Hc & _ & _ & _).
      exists m, evs. exact Hc.
    - pose proof (Hx e) as R. rewrite H in R. apply relX_ok_r in R as (_ & f & Hc & _).
      exists (MX m' (List.filter f matl)), evs. exact Hc.
  Qed.

  Lemma mm_factsA_fo : forall n x8 (chk : resp -> Model -> check_result) (i : SyscallInput),
    ms_svc_pending ms = Some x8 ->
    (forall eff m, check_syscall (sys_input segs ms x8) eff m = chk eff m) ->
    (forall eff m' evs, nstepA n mo eff m' evs <->
       chk eff mo = CheckOk m' evs /\ ~ spurious_refusal_cfg alloc_forced_cfg i mo eff) ->
    (forall eff, spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) mo_ eff <->
                 spurious_refusal_cfg alloc_forced_cfg i mo eff) ->
    (forall eff, relX mo matl (chk eff (MX mo matl)) (chk eff mo)) ->
    (forall eff m m' evs, chk eff m = CheckOk m' evs -> eff_quiet eff evs) ->
    (forall eff m m' evs, chk eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m)) ->
    (forall eff, chk eff mo_ <> CheckUnmodeled) ->
    node_factsA_fo A RNG ms mo mo_ n.
  Proof.
    intros n x8 chk i Hsvc Hchk Hiff Hspi Hx Hq Hsp Hnu.
    assert (Hpres : forall eff m' evs, nstepA n mo eff m' evs -> m_halted m' = None /\ minvA m').
    { intros eff m' evs Hn. apply Hiff in Hn as [Hn _].
      pose proof (Hx eff) as R. rewrite Hn in R. apply relX_ok_r in R as (S & f & Hc & Hm).
      eapply minvA_mm_post; [eassumption| eassumption| exact (Hsp _ _ _ _ Hn)]. }
    exists x8. split; [exact Hsvc|]. split; [|split; [|split; [|split; [|split]]]].
    - intros eff moX evs HC Hns. rewrite Hchk, mo__MX in HC.
      pose proof (Hx eff) as R. rewrite HC in R. apply relX_ok_l in R as (m & f & Hc & S & -> & Hm).
      pose proof (Hq _ _ _ _ Hc) as (Hacc & Hst & ->).
      apply mm_succ_ok; [| exact Hacc| exact Hm]. rewrite Hst. apply Hiff. split; [exact Hc|].
      intros Hs. apply Hns. apply (proj2 (Hspi eff)). exact Hs.
    - intros eff m' evs Hn. apply Hiff in Hn as [Hn Hns]. pose proof (Hq _ _ _ _ Hn) as (Hacc & Hst & ->).
      pose proof (Hx eff) as R. rewrite Hn in R. apply relX_ok_r in R as (S & f & Hc & Hm).
      exists eff, (MX m' (List.filter f matl)). split; [rewrite Hchk, mo__MX; exact Hc|]. split; [exact Hst|].
      intros Hs. apply Hns. apply (proj1 (Hspi eff)). exact Hs.
    - intros eff. rewrite Hchk. apply Hnu.
    - intros eff moX evs HC. rewrite Hchk, mo__MX in HC.
      pose proof (Hx eff) as R. rewrite HC in R. apply relX_ok_l in R as (m & f & Hc & S & -> & Hm).
      rewrite m_halted_MX. exact (proj1 (minvA_mm_post m f S Hm (Hsp _ _ _ _ Hc))).
    - exact Hpres.
    - intros eff mo1 mo2 evs1 evs2 H1 H2. apply Hiff in H1 as [H1 _]. apply Hiff in H2 as [H2 _].
      rewrite H1 in H2. congruence.
  Qed.

  Lemma brk_factsA : forall req,
    at_nodeA segs (NBrk req) RNG ms -> nsafeA NMAX (NBrk req) mo -> node_factsA_fo A RNG ms mo mo_ (NBrk req).
  Proof.
    intros req [[Hsvc Ha0] _] [_ Hsl]. cbn [nslack] in Hsl.
    assert (Hchk : forall eff m, check_syscall (sys_input segs ms (Z_to_bv 64 214)) eff m = check_brk (Z_to_bv 64 req) eff m).
    { intros eff m. dispatch 214. rewrite Ha0. reflexivity. }
    assert (Hx : forall eff, relX mo matl (check_brk (Z_to_bv 64 req) eff (MX mo matl)) (check_brk (Z_to_bv 64 req) eff mo)).
    { intros eff. apply (check_brk_X NMAX); [exact CAN| apply LEN| exact Hsl]. }
    apply (mm_factsA_fo (NBrk req) (Z_to_bv 64 214) (fun eff m => check_brk (Z_to_bv 64 req) eff m)
             (pure_input 214 [Z_to_bv 64 req]) Hsvc Hchk).
    - intros eff m' evs. cbn [nstepA]. rewrite nstep_brk_iff. tauto.
    - apply (spurious_mm_iff (Z_to_bv 64 214) (fun eff m => check_brk (Z_to_bv 64 req) eff m)); [exact Hchk| | reflexivity| | exact Hx].
      + intros eff m. dispatch_pure 214. reflexivity.
      + rewrite in_a0_si, Ha0. reflexivity.
    - exact Hx.
    - intros eff m m' evs. apply check_brk_quiet.
    - intros eff m m' evs. apply check_brk_init_sp.
    - intros [r ws zs us cs ci]. unfold check_brk. destruct ws; [|discriminate]. destruct cs; [|discriminate].
      destruct ci; [|discriminate]. destruct (_ && _); discriminate.
  Qed.

  Lemma nstepA_mmap_iff : forall addr len prot flags m eff m' evs,
    nstepA (NMmap addr len prot flags) m eff m' evs <->
    check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff m = CheckOk m' evs
    /\ ~ spurious_refusal_cfg alloc_forced_cfg
           (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                            Z_to_bv 64 (-1); Z_to_bv 64 0]) m eff.
  Proof.
    intros. cbn [nstepA node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 222.
    split; [tauto|]. intros [H Hns]. split; [| split; [exact H| exact Hns]].
    destruct (check_mmap_quiet _ _ _ _ _ _ _ _ _ _ H) as (_ & _ & ->). reflexivity.
  Qed.

  Lemma mmap_factsA : forall addr len prot flags,
    at_nodeA segs (NMmap addr len prot flags) RNG ms -> nsafeA NMAX (NMmap addr len prot flags) mo ->
    node_factsA_fo A RNG ms mo mo_ (NMmap addr len prot flags).
  Proof.
    intros addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) [Hsafe Hsl]. cbn [nslack] in Hsl. cbv zeta in Hsl. cbn [nsafeA0] in Hsafe.
    destruct Hsl as (Hsl1 & Hsl2 & Hsl3).
    set (chk := fun eff m => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                         (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff m).
    assert (Hchk : forall eff m, check_syscall (sys_input segs ms (Z_to_bv 64 222)) eff m = chk eff m).
    { intros eff m. subst chk. dispatch 222. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }
    assert (Hx : forall eff, relX mo matl (chk eff (MX mo matl)) (chk eff mo)).
    { intros eff. subst chk. apply (check_mmap_X NMAX); [exact CAN| apply LEN| exact Hsl1| exact Hsl2| exact Hsl3]. }
    apply (mm_factsA_fo (NMmap addr len prot flags) (Z_to_bv 64 222) chk
             (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                              Z_to_bv 64 (-1); Z_to_bv 64 0]) Hsvc Hchk).
    - intros eff m' evs. apply nstepA_mmap_iff.
    - apply (spurious_mm_iff (Z_to_bv 64 222) chk); [exact Hchk| | reflexivity| | exact Hx].
      + intros eff m. subst chk. dispatch_pure 222. reflexivity.
      + rewrite in_a0_si, Ha0. reflexivity.
    - exact Hx.
    - intros eff m m' evs. apply check_mmap_quiet.
    - intros eff m m' evs. apply check_mmap_init_sp.
    - (* nsafeA0 NMmap is safe_b /\ the decline guard; MX keeps kernel and maps *)
      intros eff. apply mmap_safeA_no_unmodeled; rewrite mo__MX.
      + rewrite m_kernel_MX, m_vmmaps_MX. exact (proj2 Hsafe).
      + rewrite m_vmmaps_MX. exact (proj1 Hsafe).
  Qed.

  Lemma munmap_factsA : forall addr len,
    at_nodeA segs (NMunmap addr len) RNG ms -> nsafeA NMAX (NMunmap addr len) mo ->
    node_factsA_fo A RNG ms mo mo_ (NMunmap addr len).
  Proof.
    intros addr len [(Hsvc & Ha0 & Ha1) _] [Hsafe _].
    assert (Hchk : forall eff m, check_syscall (sys_input segs ms (Z_to_bv 64 215)) eff m
                                 = check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff m).
    { intros eff m. dispatch 215. rewrite Ha0, Ha1. reflexivity. }
    assert (Hx : forall eff, relX mo matl (check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff (MX mo matl))
                                          (check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo)).
    { intros eff. apply check_munmap_X. }
    apply (mm_factsA_fo (NMunmap addr len) (Z_to_bv 64 215) (fun eff m => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff m)
             (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) Hsvc Hchk).
    - intros eff m' evs. cbn [nstepA]. apply nstep_munmap_iff.
    - apply (spurious_mm_iff (Z_to_bv 64 215) (fun eff m => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff m));
        [exact Hchk| | reflexivity| | exact Hx].
      + intros eff m. dispatch_pure 215. reflexivity.
      + rewrite in_a0_si, Ha0. reflexivity.
    - exact Hx.
    - intros eff m m' evs. apply check_munmap_quiet.
    - intros eff m m' evs. apply check_munmap_init_sp.
    - intros eff. apply munmap_safe_no_unmodeled. rewrite mo__MX, m_vmmaps_MX. exact Hsafe.
  Qed.

  Lemma mprotect_factsA : forall addr len prot,
    at_nodeA segs (NMprotect addr len prot) RNG ms -> nsafeA NMAX (NMprotect addr len prot) mo ->
    node_factsA_fo A RNG ms mo mo_ (NMprotect addr len prot).
  Proof.
    intros addr len prot [(Hsvc & Ha0 & Ha1 & Ha2) _] [Hsafe Hsl]. cbn [nslack] in Hsl.
    assert (Hchk : forall eff m, check_syscall (sys_input segs ms (Z_to_bv 64 226)) eff m
                                 = check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff m).
    { intros eff m. dispatch 226. rewrite Ha0, Ha1, Ha2. reflexivity. }
    assert (Hx : forall eff, relX mo matl (check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff (MX mo matl))
                                          (check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo)).
    { intros eff. apply (check_mprotect_X NMAX); [exact CAN| apply LEN| exact Hsl]. }
    apply (mm_factsA_fo (NMprotect addr len prot) (Z_to_bv 64 226)
             (fun eff m => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff m)
             (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) Hsvc Hchk).
    - intros eff m' evs. cbn [nstepA]. apply nstep_mprotect_iff.
    - apply (spurious_mm_iff (Z_to_bv 64 226)
               (fun eff m => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff m));
        [exact Hchk| | reflexivity| | exact Hx].
      + intros eff m. dispatch_pure 226. reflexivity.
      + rewrite in_a0_si, Ha0. reflexivity.
    - exact Hx.
    - intros eff m m' evs. apply check_mprotect_quiet.
    - intros eff m m' evs. apply check_mprotect_init_sp.
    - (* Lib/Nodes nsafe NMprotect is safe_b /\ the vDSO
         conjunct, and mprotect_safe_no_unmodeled takes both; MX keeps kernel and maps *)
      cbn [nsafeA0 nsafe] in Hsafe.
      intros eff. apply mprotect_safe_no_unmodeled; rewrite mo__MX.
      + rewrite m_vmmaps_MX. exact (proj1 Hsafe).
      + rewrite m_kernel_MX, m_vmmaps_MX. exact (proj2 Hsafe).
  Qed.


  Lemma nonalloc_factsA_fo : forall n,
    match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NExit _ => False | _ => True end ->
    at_nodeA segs n RNG ms -> node_factsA A RNG ms mo mo_ n -> node_factsA_fo A RNG ms mo mo_ n.
  Proof.
    intros n Hn Hat Hf. apply node_factsA_fo_of_node_factsA; [| exact Hf].
    intros x8 Hsvc. apply (nonalloc_family_on segs n ms x8 Hn); [| exact Hsvc].
    apply (at_nodeA_at_node segs n RNG ms); [destruct n; first [exact I | destruct Hn] | exact Hat].
  Qed.

  Lemma all_factsA : forall n,
    match n with NExit _ => False | _ => True end ->
    at_nodeA segs n RNG ms -> nsafeA NMAX n mo -> node_factsA_fo A RNG ms mo mo_ n.
  Proof.
    intros n Hne Hat Hsafe. destruct n; try contradiction.
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply write_factsA; assumption].
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply writev_factsA; assumption].
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply open_factsA; assumption].
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply read_factsA; assumption].
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply close_factsA; assumption].
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply ioctl_factsA; assumption].
    - refine (nonalloc_factsA_fo _ _ Hat _); [exact I | apply set_tid_factsA; assumption].
    - apply brk_factsA; assumption.
    - apply mmap_factsA; assumption.
    - apply munmap_factsA; assumption.
    - apply mprotect_factsA; assumption.
  Qed.
End Common.
End PerNodeA.


Theorem nodesA_sound : forall segs NMAX,
  node_soundA node segs (at_nodeA segs) nstepA nexitA minvA (nsafeA NMAX) NMAX.
Proof.
  intros segs NMAX. constructor.
  - intros n RNG ms Hat. eapply at_nodeA_pending. exact Hat.
  - intros n RNG A ms mo mo_ evs X Hat Hh Hminv Hsafe FOK MR INV Hss.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + destruct (exit_node_facts_fo segs ms mo_ c (proj1 Hat) Hh_) as [Hc _]. destruct (Hc _ _ Hss) as [-> ->].
      right. exists (exit_code c), (with_halted (exit_code c) mo), (with_halted (exit_code c) mo_).
      split; [reflexivity|]. split; [split; reflexivity|]. split; [| reflexivity].
      rewrite (mrel_fs _ _ _ MR). reflexivity.
    + destruct (all_factsA segs NMAX A RNG ms mo mo_ Hh Hminv MR INV FOK n Hne Hat Hsafe)
        as (x8 & Hsvc & Hok & Hcpl & Hnu & Hh0 & Hpres & Hdet).
      left. eapply kit_complete_cfg; eauto.
  - intros n RNG A ms mo mo_ rsp mo' evs Hat Hh Hminv Hsafe FOK MR INV Hn.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct Hn]).
    destruct (all_factsA segs NMAX A RNG ms mo mo_ Hh Hminv MR INV FOK n Hne Hat Hsafe)
      as (x8 & Hsvc & Hok & Hcpl & Hnu & Hh0 & Hpres & Hdet).
    destruct (Hpres _ _ _ Hn) as [Hh' Hm']. split; [exact Hh'|]. split; [exact Hm'|].
    eapply kit_sound_cfg; eauto. intros eff mo1 evs0 Hn1. exact (proj1 (Hpres _ _ _ Hn1)).
  - intros n RNG A ms mo mo_ code mo' Hat Hh Hminv Hsafe MR HX.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    destruct n as [| | | | | | |c| | | |]; try contradiction. cbn [nexitA nexit] in HX. destruct HX as [-> ->].
    split; [reflexivity|]. exists (with_halted (exit_code c) mo_). split; [| reflexivity].
    pose proof (proj2 (exit_node_facts_fo segs ms mo_ c (proj1 Hat) Hh_)) as Hss.
    rewrite (mrel_fs _ _ _ MR) in Hss. exact Hss.
  - intros n RNG A ms mo mo_ Hat Hh Hminv Hsafe FOK MR INV.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. split; reflexivity.
    + destruct (all_factsA segs NMAX A RNG ms mo mo_ Hh Hminv MR INV FOK n Hne Hat Hsafe)
        as (x8 & Hsvc & Hok & Hcpl & Hnu & Hh0 & Hpres & Hdet).
      left. eapply kit_progress_cfg; eauto.
Qed.



Lemma minvA_std_fds : forall mo,
  m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))] ->
  m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi ->
  (* c2 (statement change, APPENDED): Lib/Nodes minv ends with
     m_channel_reader mo = true (minv_init takes it from in_channel_reader inp). *)
  m_channel_reader mo = true ->
  minvA mo.
Proof.
  intros mo Hfds Hmat [Hsp1 Hsp2] Hrd. split; [| exact Hmat]. unfold minv.
  rewrite m_fds_strip, m_tid_strip, Hfds.
  change (m_vm_lazy (strip mo)) with (@nil (word * word)).
  change (m_vm_materialized (strip mo)) with (@nil word).
  change (m_vmmaps (strip mo)) with (m_vmmaps mo).
  cbn [fd_lookup].
  repeat split; try reflexivity; try (intros; discriminate); try exact Hsp1; try exact Hsp2; try exact Hrd.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
  - injection H as <-. vm_compute. reflexivity.
  - injection H as <-. vm_compute. reflexivity.
Qed.

Definition canon (mo : Model) : Model := MX mo [].

Lemma mrel_canon : forall (A : alw) mo,
  List.NoDup (m_vm_materialized mo) -> (forall p, List.In p (m_vm_materialized mo) -> A p) ->
  mrel A (canon mo) mo.
Proof.
  intros A mo ND AL. split; [| split; [reflexivity| auto]].
  unfold same_but_mat, canon. rewrite m_vm_lazy_MX.
  change (with_vm_backing (m_vm_lazy mo) (m_vm_materialized mo) (MX mo [])) with (MX (MX mo []) (m_vm_materialized mo)).
  rewrite MX_MX, MX_mat. reflexivity.
Qed.
