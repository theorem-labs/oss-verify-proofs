(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA ModelX MmXfer.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Defs.
Variable NMAX : nat.

Definition fd_inv (mo : Model) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
  (forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
  (forall k e, fd_lookup (m_fds mo) k = Some e ->
     match e with FdChannel _ | FdFile _ _ | FdDir => True | _ => False end).

Definition spwin (mo : Model) : Prop :=
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi.

Definition minvA (mo : Model) : Prop := spwin mo /\ m_vm_materialized mo = [].

Lemma minvA_intro : forall mo, spwin mo -> m_vm_materialized mo = [] -> minvA mo.
Proof. intros mo H1 H2. split; assumption. Qed.
Lemma minvA_spwin : forall mo, minvA mo -> spwin mo.
Proof. intros mo [H _]; exact H. Qed.

Lemma minv_strip_fd_inv : forall mo, minv (strip mo) -> fd_inv mo.
Proof.
  intros mo (M0 & M1 & M2 & MC & MF & MK & _). rewrite m_fds_strip, m_fs_strip in *.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF| exact MK].
Qed.
Lemma minv_strip_spwin : forall mo, minv (strip mo) -> spwin mo.
Proof. intros mo (_ & _ & _ & _ & _ & _ & _ & _ & _ & MS). exact MS. Qed.
Lemma minv_strip_intro : forall mo, fd_inv mo -> spwin mo -> minv (strip mo).
Proof.
  intros mo (M0 & M1 & M2 & MC & MF & MK) [Hsp1 Hsp2]. unfold minv.
  rewrite m_fds_strip, m_fs_strip, m_tid_strip.
  change (m_vm_lazy (strip mo)) with (@nil (word * word)).
  change (m_vm_materialized (strip mo)) with (@nil word).
  change (m_vmmaps (strip mo)) with (m_vmmaps mo).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF|]. split; [exact MK|].
  split. { intros t H. injection H as <-. vm_compute. split; reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsp1| exact Hsp2].
Qed.

Lemma minvA_minv : forall mo, minvA mo -> fd_inv mo -> minv (strip mo).
Proof. intros mo [H _] F. exact (minv_strip_intro mo F H). Qed.

Lemma fd_inv_MX : forall m mat, fd_inv (MX m mat) <-> fd_inv m.
Proof. intros m mat. unfold fd_inv. rewrite m_fds_MX, m_fs_MX. tauto. Qed.
Lemma fd_inv_ext : forall m m', m_fds m' = m_fds m -> m_fs m' = m_fs m -> fd_inv m -> fd_inv m'.
Proof. intros m m' E1 E2. unfold fd_inv. rewrite E1, E2. exact (fun H => H). Qed.

Definition std_fds : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Lemma fd_inv_tab3 : forall mo (e : option FdEntry),
  m_fds mo = match e with Some x => (Z_to_bv 64 3, x) :: std_fds | None => std_fds end ->
  match e with None | Some FdDir => True | Some (FdFile p _) => fs_lookup (m_fs mo) p <> None | Some _ => False end ->
  fd_inv mo.
Proof.
  intros mo e Hfds He. unfold fd_inv. rewrite Hfds.
  assert (L3 : forall k x, fd_lookup ((Z_to_bv 64 3, x) :: std_fds) k =
                          if bv_eqb (Z_to_bv 64 3) k then Some x else fd_lookup std_fds k) by (intros; reflexivity).
  assert (LS : forall k, fd_lookup std_fds k =
            if bv_eqb (Z_to_bv 64 0) k then Some (FdChannel (Z_to_bv 64 0)) else
            if bv_eqb (Z_to_bv 64 1) k then Some (FdChannel (Z_to_bv 64 1)) else
            if bv_eqb (Z_to_bv 64 2) k then Some (FdChannel (Z_to_bv 64 2)) else None) by (intros; reflexivity).
  assert (STD : forall k y, fd_lookup std_fds k = Some y ->
            (k = Z_to_bv 64 0 \/ k = Z_to_bv 64 1 \/ k = Z_to_bv 64 2) /\ exists c, y = FdChannel c).
  { intros k y H. rewrite LS in H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. injection H as <-. split; [auto| eexists; reflexivity]. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. injection H as <-. split; [auto| eexists; reflexivity]. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. injection H as <-. split; [auto| eexists; reflexivity]. }
    discriminate H. }
  assert (K3 : forall k, (k = Z_to_bv 64 0 \/ k = Z_to_bv 64 1 \/ k = Z_to_bv 64 2) -> bv_unsigned k < 3).
  { intros k [->|[->| ->]]; vm_compute; reflexivity. }
  destruct e as [x|].
  - assert (N3 : forall k, bv_eqb (Z_to_bv 64 3) k = true -> fd_lookup std_fds k = None).
    { intros k E. apply bv_eqb_eq in E. subst k. reflexivity. }
    split. { rewrite L3. reflexivity. } split. { rewrite L3. reflexivity. } split. { rewrite L3. reflexivity. }
    split.
    { intros k c H. rewrite L3 in H. destruct (bv_eqb (Z_to_bv 64 3) k) eqn:E.
      - injection H as ->. destruct He.
      - apply K3. exact (proj1 (STD k _ H)). }
    split.
    { intros k p off H. rewrite L3 in H. destruct (bv_eqb (Z_to_bv 64 3) k) eqn:E.
      - injection H as ->. exact He.
      - destruct (STD k _ H) as [_ [c Hc]]. discriminate Hc. }
    intros k y H. rewrite L3 in H. destruct (bv_eqb (Z_to_bv 64 3) k) eqn:E.
    + injection H as <-. destruct x; first [exact I| destruct He].
    + destruct (STD k _ H) as [_ [c ->]]. exact I.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split. { intros k c H. apply K3. exact (proj1 (STD k _ H)). }
    split. { intros k p off H. destruct (STD k _ H) as [_ [c Hc]]. discriminate Hc. }
    intros k y H. destruct (STD k _ H) as [_ [c ->]]. exact I.
Qed.
Lemma fd_inv_chan3 : forall mo, m_fds mo = std_fds -> fd_inv mo.
Proof. intros mo H. apply (fd_inv_tab3 mo None H I). Qed.
Lemma fd_inv_file3 : forall mo p off, m_fds mo = (Z_to_bv 64 3, FdFile p off) :: std_fds ->
  fs_lookup (m_fs mo) p <> None -> fd_inv mo.
Proof. intros mo p off H Hp. apply (fd_inv_tab3 mo (Some (FdFile p off)) H Hp). Qed.
Lemma fd_inv_dir3 : forall mo, m_fds mo = (Z_to_bv 64 3, FdDir) :: std_fds -> fd_inv mo.
Proof. intros mo H. apply (fd_inv_tab3 mo (Some FdDir) H I). Qed.

Definition mmap_fixed_repl (flags addr n : word) (mo : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo).
Definition mmap_fixed_span_repl (flags addr n : word) (mo : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo).

Definition nslack (n : node) (mo : Model) : Prop :=
  match n with
  | NBrk req =>
      robust NMAX (nonlazy_bytes mo + bv_unsigned (bv_sub (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)))) (vm_limit (m_vmmaps mo))
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
  | NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ => fd_inv mo /\ nsafe n mo
  | _ => nsafe n mo
  end.

Definition nsafeA (n : node) (mo : Model) : Prop := nsafeA0 n mo /\ nslack n mo.

Lemma mmap_safeA_no_unmodeled : forall addr len prot flags fd off eff m,
  mmap_safeA_b addr len prot flags fd off (m_vmmaps m) = true ->
  check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof. intros. apply mmap_safe_no_unmodeled. exact H. Qed.

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
  intros addr len flags mo FRW NZ nZ A0 AL ACE RG. cbn [nsafeA0]. unfold mmap_safeA_b, mmap_safe_b.
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
      | Some i => syscall_spec i mo (Ok eff mo' evs) /\ ~ spurious_refusal_cfg fcfg i mo eff
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
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> m_halted moX = None) ->
  forall evs X, sstep_cfg segs fcfg (mkCfg ms mo_) evs X ->
    exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstepA n mo rsp mo' evs /\ mrel A mo' mo_'.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hh Hok Hnu Hckh evs X Hss.
  destruct (sstep_cfg_svc_inv segs _ _ _ _ _ Hsvc Hss)
    as [(eff & moX & mo_'' & Hs & Hns & Hh' & Hmat & ->) | [(eff & moX & evs1 & Hs & Hns & Hh' & Hmat & -> & ->)
       | [(eff & moX & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & moX & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
  - apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs Hns) as (mo' & moY & Hn & HmatY & MR).
    rewrite HmatY in Hmat. injection Hmat as <-.
    exists (rstrip eff), mo', moY. rewrite nret_rstrip. auto.
  - exfalso. apply check_syscall_ok_iff in Hs. destruct (Hok _ _ _ Hs Hns) as (mo' & moY & Hn & HmatY & MR). congruence.
  - exfalso. apply check_syscall_ok_iff in Hs. apply Hckh in Hs. congruence.
  - exfalso. apply check_syscall_ok_iff in Hs. apply Hckh in Hs. exact (m_killed_halted _ _ Hk' Hs).
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
Qed.

Lemma kit_sound : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 -> m_halted mo_ = None ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs ->
     exists effk moX, check_syscall (sys_input segs ms x8) effk mo_ = CheckOk moX evs /\
       ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ effk /\ rstrip effk = eff) ->
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None) ->

  (forall eff mo1 mo2 evs1 evs2, nstepA n mo eff mo1 evs1 -> nstepA n mo eff mo2 evs2 -> mo1 = mo2) ->
  forall eff mo' evs, nstepA n mo eff mo' evs ->
    exists mo_', sstep_cfg segs fcfg (mkCfg ms mo_) evs (SNext (mkCfg (nret ms eff) mo_')) /\ mrel A mo' mo_'.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hh Hok Hcpl Hhalt Hdet eff mo' evs Hn.
  destruct (Hcpl _ _ _ Hn) as (effk & moX & Hck & Hns & Hst).
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

Lemma kit_progress : forall A n ms mo mo_ x8,
  ms_svc_pending ms = Some x8 ->
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) ->
  exists rsp mo' evs, nstepA n mo rsp mo' evs.
Proof.
  intros A n ms mo mo_ x8 Hsvc Hok Hnu.
  pose proof (receptive (sys_input segs ms x8) mo_) as Hr.
  destruct (syscall_spec_witness (sys_input segs ms x8) mo_) as [eff moX evs|] eqn:E.
  - destruct (classic (spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff)) as [Hsp|Hns].
    + destruct Hsp as (_ & _ & eff' & moX' & evs' & Hs' & Hr').
      apply check_syscall_ok_iff in Hs'.
      destruct (Hok _ _ _ Hs' (fcfg_nonref_nonspur _ _ _ Hr')) as (mo' & moY & Hn & _). eauto.
    + apply check_syscall_ok_iff in Hr. destruct (Hok _ _ _ Hr Hns) as (mo' & moY & Hn & _). eauto.
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

End Kit.

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
  | 233 => rewrite check_syscall_madvise by (apply sysno_lit; lia)
  end;
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

Ltac dispatch_pure K :=
  lazymatch K with
  | 214 => rewrite check_syscall_brk by reflexivity
  | 222 => rewrite check_syscall_mmap by reflexivity
  | 215 => rewrite check_syscall_munmap by reflexivity
  | 226 => rewrite check_syscall_mprotect by reflexivity
  | 233 => rewrite check_syscall_madvise by reflexivity
  end; cbn [in_arg in_args nth pure_input].

Lemma cov_one_lit : forall RNG (a : Z) (k : nat) len,
  rng RNG a len -> 0 <= a < 2^64 -> Z.of_nat k <= len -> Forall (acc_in RNG) [(Z_to_bv 64 a, k)].
Proof.
  intros RNG a k len HR Ha Hk. constructor; [|constructor].
  unfold acc_in. cbn [fst snd]. rewrite unsigned_lit by lia. destruct HR as (_ & _ & H'). apply H'; lia.
Qed.

Lemma spurious_relX : forall cfg i mo mat eff,
  (forall e, relX mo mat (check_syscall i e (MX mo mat)) (check_syscall i e mo)) ->
  spurious_refusal_cfg cfg i (MX mo mat) eff <-> spurious_refusal_cfg cfg i mo eff.
Proof.
  intros cfg i mo mat eff HX.
  assert (Hr : forall r, refusal_b i (MX mo mat) r = refusal_b i mo r).
  { intros r. unfold refusal_b, brk_refusal_b. rewrite m_vmmaps_MX. reflexivity. }
  unfold spurious_refusal_cfg. rewrite (Hr (eff_ret eff)). split.
  - intros (Hoff & Hrf & eff' & m' & evs' & Hs & Hr'). split; [exact Hoff|]. split; [exact Hrf|].
    apply check_syscall_ok_iff in Hs. pose proof (HX eff') as R. rewrite Hs in R.
    apply relX_ok_l in R as (m & f & Hc & _). exists eff', m, evs'. rewrite <- Hr.
    split; [apply check_syscall_ok_iff; exact Hc| exact Hr'].
  - intros (Hoff & Hrf & eff' & m' & evs' & Hs & Hr'). split; [exact Hoff|]. split; [exact Hrf|].
    apply check_syscall_ok_iff in Hs. pose proof (HX eff') as R. rewrite Hs in R.
    apply relX_ok_r in R as (_ & f & Hc & _). exists eff', (MX m' (List.filter f mat)), evs'. rewrite Hr.
    split; [apply check_syscall_ok_iff; exact Hc| exact Hr'].
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

Definition node_factsA_cfg (A : alw) (RNG : footprint) (ms : machine_state) (mo mo_ : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs ->
     ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff -> succ_ok A n mo mo_ eff moX evs) /\
  (forall eff mo' evs, nstepA n mo eff mo' evs ->
     exists effk moX, check_syscall (sys_input segs ms x8) effk mo_ = CheckOk moX evs /\
       ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ effk /\ rstrip effk = eff) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo_ <> CheckUnmodeled) /\
  (forall eff moX evs, check_syscall (sys_input segs ms x8) eff mo_ = CheckOk moX evs -> m_halted moX = None) /\
  (forall eff mo' evs, nstepA n mo eff mo' evs -> m_halted mo' = None /\ minvA mo') /\
  (forall eff mo1 mo2 evs1 evs2, nstepA n mo eff mo1 evs1 -> nstepA n mo eff mo2 evs2 -> mo1 = mo2).

Lemma factsA_cfg_of_plain : forall A RNG ms mo mo_ n,
  (forall x8, ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos) ->
  node_factsA A RNG ms mo mo_ n -> node_factsA_cfg A RNG ms mo mo_ n.
Proof.
  intros A RNG ms mo mo_ n Hna (x8 & Hsvc & Hok & Hcpl & Hnu & Hpres & Hdet).
  assert (Hns : forall eff, ~ spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff).
  { intros eff. apply fcfg_nonalloc_nonspur. exact (Hna x8 Hsvc). }
  exists x8. split; [exact Hsvc|]. split; [intros eff moX evs Hc _; exact (Hok _ _ _ Hc)|].
  split; [intros eff mo' evs Hn; destruct (Hcpl _ _ _ Hn) as (effk & moX & Hck & Hst); exists effk, moX; auto|].
  split; [exact Hnu|]. split; [|split; [exact Hpres| exact Hdet]].
  intros eff moX evs Hc. destruct (Hok _ _ _ Hc) as (mo' & moY & Hn & HmatY & (SB & _)).
  pose proof (proj1 (Hpres _ _ _ Hn)).
  pose proof (materialize_model_accesses_frame _ _ _ HmatY) as (_ & _ & _ & _ & _ & PR & _).
  pose proof (same_but_mat_halted _ _ SB) as E. unfold m_halted in *. rewrite PR in E. congruence.
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
  Lemma SPW : spwin mo.
  Proof. exact (proj1 Hminv). Qed.
  Lemma Hh_ : m_halted mo_ = None.
  Proof. rewrite mo__MX, m_halted_MX. exact Hh. Qed.

  Lemma minvA_same_vm : forall m, m_vmmaps m = m_vmmaps mo -> m_vm_materialized m = [] -> minvA m.
  Proof. intros m VM CAN'. split; [| exact CAN']. unfold spwin. rewrite VM. exact SPW. Qed.

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

  Section FdNodes.
  Hypothesis FDI : fd_inv mo.
  Lemma MINV : minv (strip mo).
  Proof. exact (minv_strip_intro mo FDI SPW). Qed.
  Lemma MINV_ : minv (strip mo_).
  Proof. rewrite mo__MX, strip_MX. exact MINV. Qed.

  Lemma std_chanA : forall m fd, minv (strip m) -> (fd = 1 \/ fd = 2) ->
    fd_lookup (m_fds m) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd)) /\ w_is0 (Z_to_bv 64 fd) = false.
  Proof. intros m fd Hm Hfd. exact (std_chan (strip m) fd Hm Hfd). Qed.

  Lemma write_check_specA : forall m fd bs eff,
    at_node segs (NWrite fd bs) ms -> minv (strip m) ->
    check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff m = write_check fd (areg ms 11) bs eff m.
  Proof.
    intros m fd bs eff (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Htop & Hrom & Hbs) Hm.
    pose proof max_write_lt as (W1 & W2 & W3 & W4).
    dispatch 64. unfold check_write. rewrite Ha0, Ha2, in_mem_si.
    destruct (std_chanA m fd Hm Hfd) as [Hlk Hw]. rewrite Hlk, Hw.
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
    destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]; try contradiction.
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
    destruct e as [ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]; try (split; [discriminate| tauto]).
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
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]|]; try contradiction;
      try (destruct H as [He ->]; exists m; repeat split; assumption).
    destruct (fs_lookup (m_fs m) p) as [data|]; [|contradiction]. destruct H as [He ->].
    eexists. split; [split; [exact Hevs|]; split; [exact He| reflexivity] |]. rewrite with_fds_MX. reflexivity.
  Qed.

  Lemma nstep_read_MX' : forall fd buf count m mat eff mo' evs,
    nstep (NRead fd buf count) m eff mo' evs -> nstep (NRead fd buf count) (MX m mat) eff (MX mo' mat) evs.
  Proof.
    intros fd buf count m mat eff mo' evs Hn. cbn [nstep] in Hn. destruct Hn as [Hevs H]. cbn [nstep]. rewrite m_fds_MX, m_fs_MX.
    split; [exact Hevs|].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]|]; try contradiction;
      try (destruct H as [He ->]; auto).
    destruct (fs_lookup (m_fs m) p) as [data|]; [|contradiction]. destruct H as [He ->].
    rewrite with_fds_MX. auto.
  Qed.

  Lemma nstep_read_strip : forall fd buf count m eff mo' evs,
    nstep (NRead fd buf count) m eff mo' evs -> nstep (NRead fd buf count) (strip m) eff (strip mo') evs.
  Proof.
    intros fd buf count m eff mo' evs Hn. cbn [nstep] in Hn. destruct Hn as [Hevs H]. cbn [nstep]. rewrite m_fds_strip, m_fs_strip.
    split; [exact Hevs|].
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]|]; try contradiction;
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
    destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]|]; try contradiction;
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
        destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]|]; try contradiction;
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
      split; [exact Hh'|]. split; [exact (minv_strip_spwin _ Hm')|].
      destruct (nstep_read_shape _ _ _ _ _ _ _ Hn) as [(E & _)|(x & ->)]; [rewrite E; exact CAN| cbn; exact CAN].
    - intros eff mo1 mo2 evs1 evs2 [_ H1] [_ H2].
      destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|dnr dnw|]|]; try contradiction;
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
      unfold open_check in HC. apply check_copyins_after_ok_iff in HC as [Hci Hb].
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
      split; [exact Hh'|]. split; [exact (minv_strip_spwin _ Hm')|].
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
      split; [exact Hh'|]. split; [exact (minv_strip_spwin _ Hm')|].
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
      + split; [exact Hh|]. apply minvA_same_vm; [reflexivity| cbn; exact CAN].
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
    destruct (std_chanA m fd Hm Hfd) as [Hlk Hw]. rewrite Hlk, Hw.
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
  End FdNodes.

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

  Lemma check_madvise_quiet : forall a l eff m m' evs, check_madvise a l (Z_to_bv 64 4) eff m = CheckOk m' evs -> eff_quiet eff evs.
  Proof. intros a l [r ws zs us cs ci] m m' evs H. unfold check_madvise in H. crush_ok H; repeat split; reflexivity. Qed.

  Lemma check_mprotect_quiet : forall a l pr eff m m' evs, check_mprotect a l pr eff m = CheckOk m' evs -> eff_quiet eff evs.
  Proof. intros a l pr [r ws zs us cs ci] m m' evs H. unfold check_mprotect in H. crush_ok H; repeat split; reflexivity. Qed.

  Lemma check_mmap_quiet : forall a l pr fl fd off eff m m' evs,
    check_mmap a l pr fl fd off eff m = CheckOk m' evs -> eff_quiet eff evs.
  Proof. intros a l pr fl fd off [r ws zs us cs ci] m m' evs H. unfold check_mmap in H. crush_ok H; repeat split; reflexivity. Qed.

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
  Lemma check_madvise_init_sp : forall a l eff m m' evs,
    check_madvise a l (Z_to_bv 64 4) eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. intros a l eff m m' evs H. pose proof (check_madvise_shape _ _ _ _ _ _ H) as [(_ & _ & _ & _ & _ & _ & E & _) _]. exact E. Qed.
  Lemma check_mprotect_init_sp : forall a l pr eff m m' evs,
    check_mprotect a l pr eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof. intros a l pr eff m m' evs H. pose proof (check_mprotect_shape _ _ _ _ _ _ _ H) as [(_ & _ & _ & _ & _ & _ & E & _) _]. exact E. Qed.
  Lemma check_mmap_init_sp : forall a l pr fl fd off eff m m' evs,
    check_mmap a l pr fl fd off eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
  Proof.
    intros a l pr fl fd off [r ws zs us cs ci] m m' evs H. unfold check_mmap in H. crush_ok H; init_sp_solve.
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

  Lemma minvA_mm_post : forall m f,
    strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
    m_vm_materialized m = List.filter f (m_vm_materialized mo) ->
    vm_init_sp (m_vmmaps m) = vm_init_sp (m_vmmaps mo) ->
    m_halted m = None /\ minvA m.
  Proof.
    intros m f S Hm Hsp. split; [| split].
    - rewrite <- (m_halted_strip m), S. cbn. exact Hh.
    - unfold spwin. rewrite Hsp. exact SPW.
    - rewrite Hm, CAN. reflexivity.
  Qed.

  Lemma LEN : (length matl <= NMAX)%nat.
  Proof. pose proof (ainv_len _ _ _ _ INV) as L. exact L. Qed.

  Lemma mm_factsA : forall n i x8 (chk : resp -> Model -> check_result),
    ms_svc_pending ms = Some x8 ->
    in_sysno i = x8 -> in_arg i 0 = in_arg (sys_input segs ms x8) 0 ->
    (forall eff m, check_syscall (sys_input segs ms x8) eff m = chk eff m) ->
    (forall eff m, check_syscall i eff m = chk eff m) ->
    (forall eff m' evs, nstepA n mo eff m' evs <-> chk eff mo = CheckOk m' evs /\ ~ spurious_refusal_cfg fcfg i mo eff) ->
    (forall eff, relX mo matl (chk eff (MX mo matl)) (chk eff mo)) ->
    (forall eff m m' evs, chk eff m = CheckOk m' evs -> eff_quiet eff evs) ->
    (forall eff m m' evs, chk eff m = CheckOk m' evs -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m)) ->
    (forall eff, chk eff mo_ <> CheckUnmodeled) ->
    node_factsA_cfg A RNG ms mo mo_ n.
  Proof.
    intros n i x8 chk Hsvc Hno H0 Hchk Hchki Hiff Hx Hq Hsp Hnu.
    assert (HS : forall eff, spurious_refusal_cfg fcfg (sys_input segs ms x8) mo_ eff <-> spurious_refusal_cfg fcfg i mo eff).
    { intros eff. rewrite mo__MX, spurious_relX by (intros e; rewrite !Hchk; apply Hx).
      apply spurious_input_iff; [exact (eq_sym Hno) | exact (eq_sym H0) | intros e; rewrite Hchk, Hchki; reflexivity]. }
    exists x8. split; [exact Hsvc|].
    split; [|split; [|split; [|split; [|split]]]].
    - intros eff moX evs HC Hns. rewrite Hchk, mo__MX in HC.
      pose proof (Hx eff) as R. rewrite HC in R. apply relX_ok_l in R as (m & f & Hc & S & -> & Hm).
      pose proof (Hq _ _ _ _ Hc) as (Hacc & Hst & ->).
      apply mm_succ_ok; [| exact Hacc| exact Hm]. rewrite Hst. apply Hiff. split; [exact Hc|].
      intros Hs. apply Hns, HS, Hs.
    - intros eff m' evs Hn. apply Hiff in Hn as [Hn Hns]. pose proof (Hq _ _ _ _ Hn) as (Hacc & Hst & ->).
      pose proof (Hx eff) as R. rewrite Hn in R. apply relX_ok_r in R as (S & f & Hc & Hm).
      exists eff, (MX m' (List.filter f matl)). split; [rewrite Hchk, mo__MX; exact Hc|].
      split; [intros Hs; apply Hns, HS, Hs | exact Hst].
    - intros eff. rewrite Hchk. apply Hnu.
    - intros eff moX evs HC. rewrite Hchk, mo__MX in HC.
      pose proof (Hx eff) as R. rewrite HC in R. apply relX_ok_l in R as (m & f & Hc & S & -> & Hm).
      rewrite m_halted_MX. exact (proj1 (minvA_mm_post m f S Hm (Hsp _ _ _ _ Hc))).
    - intros eff m' evs Hn. apply Hiff in Hn as [Hn _].
      pose proof (Hx eff) as R. rewrite Hn in R. apply relX_ok_r in R as (S & f & Hc & Hm).
      eapply minvA_mm_post; [eassumption| eassumption| exact (Hsp _ _ _ _ Hn)].
    - intros eff mo1 mo2 evs1 evs2 H1 H2. apply Hiff in H1 as [H1 _]. apply Hiff in H2 as [H2 _].
      rewrite H1 in H2. congruence.
  Qed.

  Lemma brk_factsA : forall req,
    at_nodeA segs (NBrk req) RNG ms -> nsafeA NMAX (NBrk req) mo -> node_factsA_cfg A RNG ms mo mo_ (NBrk req).
  Proof.
    intros req [[Hsvc Ha0] _] [_ Hsl]. cbn [nslack] in Hsl.
    apply (mm_factsA (NBrk req) (pure_input 214 [Z_to_bv 64 req]) (Z_to_bv 64 214)
             (fun eff m => check_brk (Z_to_bv 64 req) eff m) Hsvc); [reflexivity | rewrite in_a0_si, Ha0; reflexivity | | | | | | | ].
    - intros eff m. dispatch 214. rewrite Ha0. reflexivity.
    - intros eff m. dispatch_pure 214. reflexivity.
    - intros eff m' evs. cbn [nstepA]. apply nstep_brk_iff.
    - intros eff. apply (check_brk_X NMAX); [exact CAN| apply LEN| exact Hsl].
    - intros eff m m' evs. apply check_brk_quiet.
    - intros eff m m' evs. apply check_brk_init_sp.
    - intros [r ws zs us cs ci]. unfold check_brk. destruct ws; [|discriminate]. destruct cs; [|discriminate].
      destruct ci; [|discriminate]. destruct (_ && _); discriminate.
  Qed.

  Lemma nstepA_mmap_iff : forall addr len prot flags m eff m' evs,
    nstepA (NMmap addr len prot flags) m eff m' evs <->
    (check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff m = CheckOk m' evs /\
     ~ spurious_refusal_cfg fcfg
         (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
         m eff).
  Proof.
    intros. cbn [nstepA node_input]. rewrite <- check_syscall_ok_iff. dispatch_pure 222.
    split; [tauto|]. intros [H Hns]. split; [| auto].
    destruct (check_mmap_quiet _ _ _ _ _ _ _ _ _ _ H) as (_ & _ & ->). reflexivity.
  Qed.

  Lemma mmap_factsA : forall addr len prot flags,
    at_nodeA segs (NMmap addr len prot flags) RNG ms -> nsafeA NMAX (NMmap addr len prot flags) mo ->
    node_factsA_cfg A RNG ms mo mo_ (NMmap addr len prot flags).
  Proof.
    intros addr len prot flags (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5) [Hsafe Hsl]. cbn [nslack] in Hsl. cbv zeta in Hsl. cbn [nsafeA0] in Hsafe.
    destruct Hsl as (Hsl1 & Hsl2 & Hsl3).
    apply (mm_factsA (NMmap addr len prot flags)
             (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
             (Z_to_bv 64 222)
             (fun eff m => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                      (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff m) Hsvc);
      [reflexivity | rewrite in_a0_si, Ha0; reflexivity | | | | | | | ].
    - intros eff m. dispatch 222. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
    - intros eff m. dispatch_pure 222. reflexivity.
    - intros eff m' evs. apply nstepA_mmap_iff.
    - intros eff. apply (check_mmap_X NMAX); [exact CAN| apply LEN| exact Hsl1| exact Hsl2| exact Hsl3].
    - intros eff m m' evs. apply check_mmap_quiet.
    - intros eff m m' evs. apply check_mmap_init_sp.
    - intros eff. apply mmap_safeA_no_unmodeled. rewrite mo__MX, m_vmmaps_MX. exact Hsafe.
  Qed.

  Lemma munmap_factsA : forall addr len,
    at_nodeA segs (NMunmap addr len) RNG ms -> nsafeA NMAX (NMunmap addr len) mo ->
    node_factsA_cfg A RNG ms mo mo_ (NMunmap addr len).
  Proof.
    intros addr len [(Hsvc & Ha0 & Ha1) _] [Hsafe _].
    apply (mm_factsA (NMunmap addr len) (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) (Z_to_bv 64 215)
             (fun eff m => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff m) Hsvc);
      [reflexivity | rewrite in_a0_si, Ha0; reflexivity | | | | | | | ].
    - intros eff m. dispatch 215. rewrite Ha0, Ha1. reflexivity.
    - intros eff m. dispatch_pure 215. reflexivity.
    - intros eff m' evs. cbn [nstepA]. rewrite nstep_munmap_iff.
      pose proof (fcfg_nonalloc_nonspur (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo eff
                    (nonalloc_lit 215 ltac:(lia) eq_refl)). tauto.
    - intros eff. apply check_munmap_X.
    - intros eff m m' evs. apply check_munmap_quiet.
    - intros eff m m' evs. apply check_munmap_init_sp.
    - intros eff. apply munmap_safe_no_unmodeled. rewrite mo__MX, m_vmmaps_MX. exact Hsafe.
  Qed.

  Lemma mprotect_factsA : forall addr len prot,
    at_nodeA segs (NMprotect addr len prot) RNG ms -> nsafeA NMAX (NMprotect addr len prot) mo ->
    node_factsA_cfg A RNG ms mo mo_ (NMprotect addr len prot).
  Proof.
    intros addr len prot [(Hsvc & Ha0 & Ha1 & Ha2) _] [Hsafe Hsl]. cbn [nslack] in Hsl.
    apply (mm_factsA (NMprotect addr len prot) (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
             (Z_to_bv 64 226)
             (fun eff m => check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff m) Hsvc);
      [reflexivity | rewrite in_a0_si, Ha0; reflexivity | | | | | | | ].
    - intros eff m. dispatch 226. rewrite Ha0, Ha1, Ha2. reflexivity.
    - intros eff m. dispatch_pure 226. reflexivity.
    - intros eff m' evs. cbn [nstepA]. apply nstep_mprotect_iff.
    - intros eff. apply (check_mprotect_X NMAX); [exact CAN| apply LEN| exact Hsl].
    - intros eff m m' evs. apply check_mprotect_quiet.
    - intros eff m m' evs. apply check_mprotect_init_sp.
    - intros eff. apply mprotect_safe_no_unmodeled. rewrite mo__MX, m_vmmaps_MX. exact Hsafe.
  Qed.

  Lemma madvise_factsA : forall addr len,
    at_nodeA segs (NMadvise addr len) RNG ms -> nsafeA NMAX (NMadvise addr len) mo ->
    node_factsA_cfg A RNG ms mo mo_ (NMadvise addr len).
  Proof.
    intros addr len [(Hsvc & Ha0 & Ha1 & Ha2) _] [Hsafe _].
    apply (mm_factsA (NMadvise addr len) (pure_input 233 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 4]) (Z_to_bv 64 233)
             (fun eff m => check_madvise (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 4) eff m) Hsvc);
      [reflexivity | rewrite in_a0_si, Ha0; reflexivity | | | | | | | ].
    - intros eff m. dispatch 233. rewrite Ha0, Ha1, Ha2. reflexivity.
    - intros eff m. dispatch_pure 233. reflexivity.
    - intros eff m' evs. cbn [nstepA]. rewrite nstep_madvise_iff.
      pose proof (fcfg_nonalloc_nonspur (pure_input 233 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 4]) mo eff
                    (nonalloc_lit 233 ltac:(lia) eq_refl)). tauto.
    - intros eff. apply check_madvise_X.
    - intros eff m m' evs. apply check_madvise_quiet.
    - intros eff m m' evs. apply check_madvise_init_sp.
    - intros eff. apply madvise_safe_no_unmodeled. rewrite mo__MX, m_vmmaps_MX. exact Hsafe.
  Qed.

  Lemma all_factsA : forall n,
    match n with NExit _ => False | _ => True end ->
    at_nodeA segs n RNG ms -> nsafeA NMAX n mo -> node_factsA_cfg A RNG ms mo mo_ n.
  Proof.
    intros n Hne Hat Hsafe. destruct n; try contradiction.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 64 (proj1 (proj1 Hat))); [lia|reflexivity]|].
      apply (write_factsA (proj1 (proj1 Hsafe))); assumption.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 66 (proj1 Hat)); [lia|reflexivity]|].
      apply (writev_factsA (proj1 (proj1 Hsafe))); assumption.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 56 (proj1 (proj1 Hat))); [lia|reflexivity]|].
      apply (open_factsA (proj1 (proj1 Hsafe))); assumption.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 63 (proj1 (proj1 Hat))); [lia|reflexivity]|].
      apply (read_factsA (proj1 (proj1 Hsafe))); assumption.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 57 (proj1 (proj1 Hat))); [lia|reflexivity]|].
      apply (close_factsA (proj1 (proj1 Hsafe))); assumption.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 29 (proj1 (proj1 Hat))); [lia|reflexivity]|].
      apply (ioctl_factsA (proj1 (proj1 Hsafe))); assumption.
    - apply factsA_cfg_of_plain; [apply (pending_nonalloc ms 96 (proj1 Hat)); [lia|reflexivity]|].
      apply set_tid_factsA; assumption.
    - apply brk_factsA; assumption.
    - apply mmap_factsA; assumption.
    - apply munmap_factsA; assumption.
    - apply mprotect_factsA; assumption.
    - apply madvise_factsA; assumption.
  Qed.
End Common.
End PerNodeA.

Theorem nodesA_sound : forall segs NMAX,
  node_soundA node segs (at_nodeA segs) nstepA nexitA minvA (nsafeA NMAX) NMAX.
Proof.
  intros segs NMAX. constructor.
  -   intros n RNG ms Hat. eapply at_nodeA_pending. exact Hat.
  -
    intros n RNG A ms mo mo_ evs X Hat Hh Hminv Hsafe FOK MR INV Hss.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + destruct (exit_node_facts segs ms mo_ c (proj1 Hat) Hh_) as [Hc _].
      destruct (Hc _ _ (sstep_cfg_sub segs fcfg _ _ _ Hss)) as [-> ->].
      right. exists (exit_code c), (with_halted (exit_code c) mo), (with_halted (exit_code c) mo_).
      split; [reflexivity|]. split; [split; reflexivity|]. split; [| reflexivity].
      rewrite (mrel_fs _ _ _ MR). reflexivity.
    + destruct (all_factsA segs NMAX A RNG ms mo mo_ Hh Hminv MR INV FOK n Hne Hat Hsafe)
        as (x8 & Hsvc & Hok & Hcpl & Hnu & Hckh & Hpres & Hdet).
      left. eapply kit_complete; [exact Hsvc| exact Hh_| exact Hok| exact Hnu| exact Hckh| exact Hss].
  -
    intros n RNG A ms mo mo_ rsp mo' evs Hat Hh Hminv Hsafe FOK MR INV Hn.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    assert (Hne : match n with NExit _ => False | _ => True end) by (destruct n; first [exact I | destruct Hn]).
    destruct (all_factsA segs NMAX A RNG ms mo mo_ Hh Hminv MR INV FOK n Hne Hat Hsafe)
      as (x8 & Hsvc & Hok & Hcpl & Hnu & Hckh & Hpres & Hdet).
    destruct (Hpres _ _ _ Hn) as [Hh' Hm']. split; [exact Hh'|]. split; [exact Hm'|].
    eapply kit_sound; eauto. intros eff mo1 evs0 Hn1. exact (proj1 (Hpres _ _ _ Hn1)).
  -
    intros n RNG A ms mo mo_ code mo' Hat Hh Hminv Hsafe MR HX.
    assert (Hh_ : m_halted mo_ = None) by (rewrite (mrel_halted _ _ _ MR); exact Hh).
    destruct n as [| | | | | | |c| | | | |]; try contradiction. cbn [nexitA nexit] in HX. destruct HX as [-> ->].
    split; [reflexivity|]. exists (with_halted (exit_code c) mo_). split; [| reflexivity].
    pose proof (proj2 (exit_node_facts segs ms mo_ c (proj1 Hat) Hh_)) as Hss.
    rewrite (mrel_fs _ _ _ MR) in Hss. apply (sstep_fcfg_of_sstep segs); [|exact Hss].
    destruct (proj1 (proj1 Hat)) as [Hp|Hp];
      [exact (step_nonspur_nonalloc segs ms mo_ _ Hp (nonalloc_lit 93 ltac:(lia) eq_refl))
      |exact (step_nonspur_nonalloc segs ms mo_ _ Hp (nonalloc_lit 94 ltac:(lia) eq_refl))].
  -
    intros n RNG A ms mo mo_ Hat Hh Hminv Hsafe FOK MR INV.
    assert (Hcase : (exists c, n = NExit c) \/ match n with NExit _ => False | _ => True end).
    { destruct n; first [left; eexists; reflexivity | right; exact I]. }
    destruct Hcase as [[c ->] | Hne].
    + right. eexists _, _. split; reflexivity.
    + destruct (all_factsA segs NMAX A RNG ms mo mo_ Hh Hminv MR INV FOK n Hne Hat Hsafe)
        as (x8 & Hsvc & Hok & Hcpl & Hnu & Hckh & Hpres & Hdet).
      left. eapply kit_progress; eauto.
Qed.

Lemma minvA_std_fds : forall mo,
  m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))] ->
  m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi ->
  minvA mo.
Proof. intros mo _ Hmat Hsp. split; [exact Hsp| exact Hmat]. Qed.

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
