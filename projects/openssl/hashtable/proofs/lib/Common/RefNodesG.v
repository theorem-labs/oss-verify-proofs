(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts ModelAmb RefNodes ExistsRun RefNodesEx PhaseG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma gg_of_rz_ex : forall mode Q K c c',
  (realizes segs c' K -> realizes segs c K) ->
  reach segs c c' ->
  GG segs mode Q K c' -> GG segs mode Q K c.
Proof.
  intros [|] Q K c c' Hrz Hex Hc.
  - apply gg_of_rz. apply Hrz. exact Hc.
  - eapply gg_reach; [exact Hex | exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_set_tid : forall mode Q regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     GG segs mode Q K (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model))) ->
  GG segs mode Q K (mkCfg (mkst regs pc mem rom) model).
Proof.
  intros [|] Q regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  - apply gg_of_rz. apply (rz_set_tid segs regs pc mem rom model K w HF HE Hh Hlazy H17 Htid).
    intros tid Ht. exact (Hk tid Ht).
  - eapply gg_reach; [eapply ex_set_tid_1; eassumption | apply Hk; apply one_tid_ok].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_read_dir : forall mode Q regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  GG segs mode Q K (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) ->
  GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros mode Q regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir.
  apply gg_of_rz_ex.
  - intros Hc. eapply rz_read_dir; eassumption.
  - eapply ex_read_dir; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma gg_openat_toolong : forall mode Q bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    GG segs mode Q K (mkCfg (post (errno_ret ENAMETOOLONG)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q bs K Hrd Hnz Hc. cbv beta delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), Hp. apply check_copyins_after_ret_only.
  Qed.

  Lemma gg_openat_empty : forall mode Q K,
    path_at segs regs mem [] ->
    GG segs mode Q K (mkCfg (post (errno_ret ENOENT)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q K Hp Hc. cbv beta delta [post] in *.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem [] Hp).
    apply check_copyins_after_ret_only.
  Qed.

  Lemma gg_openat_absent : forall mode Q p K,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = None ->
    GG segs mode Q K (mkCfg (post (errno_ret ENOENT)) model) ->
    GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q p K Hp Hne Hns Hnd Hfs Hc. cbv beta delta [post] in *.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
    rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma gg_openat_dirref : forall mode Q p KA KB,
    path_at segs regs mem p -> path_is_dirref p = true ->
    (mode = true -> forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    GG segs mode Q KB (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) ->
    GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q p KA KB Hp Hd HA HB. cbv beta delta [post fds] in *.
    assert (Hne : path_eqb p [] = false).
    { destruct p; [|reflexivity]. cbv in Hd. discriminate Hd. }
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    apply (gg_alt2 segs mode Q _ {e : Z | In e openat_errnos} unit
             (open_nx (epend regs pc mem (seg_rom segs) (getr regs 17)) model
                (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)) KA KB
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
    - eapply node_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree].
      + intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem _ Hp).
        rewrite Hne, (path_is_dirref_no_slash _ Hd), Hd. apply check_copyins_after_open_result.
      + intros fd. rewrite with_fds_halted'. exact Hh.
      + intros fd. rewrite with_fds_lazy. exact Hlazy.
    - intros Hm [e He]. cbn [open_nx]. rewrite adv_set_epend. apply (HA Hm). exact He.
    - intros []. cbn [open_nx]. rewrite adv_set_epend. exact HB.
  Qed.

  Lemma gg_openat_dot : forall mode Q KA KB,
    path_at segs regs mem dot_path ->
    (mode = true -> forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    GG segs mode Q KB (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) ->
    GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof. intros mode Q KA KB Hp HA HB. exact (gg_openat_dirref mode Q dot_path KA KB Hp eq_refl HA HB). Qed.

  (* [comment removed for export] *)
  Lemma gg_openat_file : forall mode Q p d KA KB,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (mode = true -> forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    GG segs mode Q KB (mkCfg (post (alloc_fd fds))
                             (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) ->
    GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q p d KA KB Hp Hne Hns Hnd Hfs HA HB. cbv beta delta [post fds] in *.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    apply (gg_alt2 segs mode Q _ {e : Z | In e openat_errnos} unit
             (open_nx (epend regs pc mem (seg_rom segs) (getr regs 17)) model
                (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)) KA KB
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
    - eapply node_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree].
      + intros eff. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
        rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_open_result.
      + intros fd. rewrite with_fds_halted'. exact Hh.
      + intros fd. rewrite with_fds_lazy. exact Hlazy.
    - intros Hm [e He]. cbn [open_nx]. rewrite adv_set_epend. apply (HA Hm). exact He.
    - intros []. cbn [open_nx]. rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_brk_query : forall mode Q regs (pc : word) mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  GG segs mode Q K (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem (seg_rom segs)) model) ->
  GG segs mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros mode Q regs pc mem model w K HF HE Hh Hlazy H17 H10.
  apply gg_of_rz_ex.
  - intros Hc. eapply rz_brk_query; eassumption.
  - eapply ex_brk_query; eassumption.
Qed.

(* [comment removed for export] *)
Lemma gg_brk_grow : forall mode Q regs (pc : word) mem model w (d : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (mode = true -> realizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  GG segs mode Q KB
     (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                  (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
            (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                           (vm_noaccess h) (vm_start_brk h)
                           (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) ->
  GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w d KA KB HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB.
  - apply gg_of_rz. exact (rz_brk_grow segs regs pc mem model w d KA KB HF HE Hh Hlazy H17 Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm (HA eq_refl) HB).
  - eapply gg_reach; [| exact HB]. exact (ex_brk_grow segs regs pc mem model w d HF HE Hh Hlazy H17 Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm).
Qed.

(* [comment removed for export] *)
Lemma gg_brk_grow_kept : forall mode Q regs (pc : word) mem model w (d : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  GG segs mode Q KA (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) ->
  (mode = true ->
   realizes segs
     (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                  (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
            (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                           (vm_noaccess h) (vm_start_brk h)
                           (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB) ->
  GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w d KA KB HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB.
  - apply gg_of_rz. exact (rz_brk_grow segs regs pc mem model w d KA KB HF HE Hh Hlazy H17 Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA (HB eq_refl)).
  - eapply gg_reach; [| exact HA].
    pose proof (u64_range b) as Hbr. subst b h.
    apply (ex_brk_grow_keep segs regs pc mem model w (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d)) HF HE Hh Hlazy H17 H10);
      rewrite u64_lit by lia; [lia | exact Hs | lia].
Qed.

(* [comment removed for export] *)
Lemma gg_brk_grow_blocked : forall mode Q regs (pc : word) mem model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  GG segs mode Q KA (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) ->
  GG segs mode Q KA (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros mode Q regs pc mem model w req KA HF HE Hh Hlazy H17 h b H10 Hpos Hs Hb Hblk.
  apply gg_of_rz_ex.
  - intros Hc. eapply rz_brk_grow_blocked; eassumption.
  - eapply ex_brk_grow_keep; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_mmap_anon_nogrant : forall mode Q regs (pc : word) mem model w (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall a, grant_ok (getr regs 10) model a (page_round_up_Z len) = false) ->
  (forall e, In e mmap_errnos ->
     GG segs mode Q KA (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model)) ->
  GG segs mode Q KA (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hng HA.
  - apply gg_of_rz. apply (rz_mmap_anon_nogrant segs regs pc mem model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hng).
    intros e He. exact (HA e He).
  - eapply gg_reach; [exact (ex_mmap_anon_enomem segs regs pc mem model w len HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15)
                     | apply HA; apply ENOMEM_in_mmap_errnos].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_mmap_noaccess : forall mode Q regs (pc : word) mem model w (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na (getr regs 10) model a n = true) ->
  (mode = true -> forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  (forall a, grant_ok_na (getr regs 10) model a n = true ->
     GG segs mode Q KB (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                    (unfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                             (noaccess_model a (Z_to_bv 64 n) model))) ->
  GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Hex HA HB.
  - apply gg_of_rz. exact (rz_mmap_noaccess segs regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hex (HA eq_refl) HB).
  - destruct Hex as [a Ha]. eapply gg_reach; [| exact (HB a Ha)].
    exact (ex_mmap_noaccess segs regs pc mem model w len a HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Ha).
Qed.

(* [comment removed for export] *)
Lemma gg_mmap_noaccess_err : forall mode Q regs (pc : word) mem model w (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na (getr regs 10) model a n = true) ->
  (forall e, In e mmap_errnos ->
     GG segs mode Q KA (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model)) ->
  (mode = true -> forall a, grant_ok_na (getr regs 10) model a n = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (unfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (noaccess_model a (Z_to_bv 64 n) model)) KB) ->
  GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Hex HA HB.
  - apply gg_of_rz. exact (rz_mmap_noaccess segs regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hex
                             (fun e He => HA e He) (HB eq_refl)).
  - eapply gg_reach; [| exact (HA ENOMEM ENOMEM_in_mmap_errnos)].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hargs : mmap_noaccess_args_ok ms).
    { unfold mmap_noaccess_args_ok, ms.
      rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
      rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
      intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
    pose proof (mmap_noaccess_check segs ms (getr regs 17) model (mkEffectU (errno_ret ENOMEM) [] [] [] [] [])
                  ltac:(rewrite H17; apply u64_lit; lia) Hargs) as Hchk.
    cbv zeta iota beta in Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Hchk.
    unfold ms in Hchk. rewrite <- (adv_ret_epend regs pc mem (seg_rom segs) (getr regs 17)).
    eapply reach_ecall_check; [exact Hh | exact Hlazy | exact HF | exact HE | exact Hchk | exact Hh | exact Hlazy].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_mmap_fixed_noaccess : forall mode Q regs (pc : word) mem model w (addr : word) (len : Z) KA KB KC,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (mode = true -> forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  GG segs mode Q KB (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                           (fixed_noaccess_model addr n model)) ->
  (mode = true -> forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                          (fixed_destroyed_model addr n model)) KC) ->
  GG segs mode Q (t_alt3 KA KB KC) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w addr len KA KB KC HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc HA HB HC.
  - apply gg_of_rz. exact (rz_mmap_fixed_noaccess segs regs pc mem model w addr len KA KB KC HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Hce
                             H12 H13 H14 H15 Hrf Hmc (HA eq_refl) HB (HC eq_refl)).
  - eapply gg_reach; [| exact HB].
    exact (ex_mmap_fixed_noaccess segs regs pc mem model w addr len HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 Hrf Hmc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gg_mprotect : forall mode Q regs (pc : word) mem model w (addr : word) (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  (mode = true -> forall e, In e mprotect_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  GG segs mode Q KB (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) (seg_rom segs))
                           (mprotect_model addr n model)) ->
  GG segs mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros [|] Q regs pc mem model w addr len KA KB HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HA HB.
  - apply gg_of_rz. exact (rz_mprotect segs regs pc mem model w addr len KA KB HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 Hna Hma Hbud (HA eq_refl) HB).
  - eapply gg_reach; [| exact HB].
    exact (ex_mprotect segs regs pc mem model w addr len HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 Hna Hma Hbud).
Qed.

(* [comment removed for export] *)
Lemma gg_mprotect_blocked : forall mode Q regs (pc : word) mem model w (addr : word) (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = false ->
  (forall e, In e mprotect_errnos ->
     GG segs mode Q KA (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model)) ->
  GG segs mode Q KA (mkCfg (mkst regs pc mem (seg_rom segs)) model).
Proof.
  intros mode Q regs pc mem model w addr len KA HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HA.
  destruct mode.
  - apply gg_of_rz. apply (rz_mprotect_blocked segs regs pc mem model w addr len KA HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 Hna Hma Hbud).
    intros e He. exact (HA e He).
  - eapply gg_reach; [| exact (HA ENOMEM ENOMEM_in_mprotect_errnos)].
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
    pose proof (mprotect_check segs ms (getr regs 17) model (mkEffectU (errno_ret ENOMEM) [] [] [] [] []) addr len Hno
                  ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                  ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                  ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
    cbv zeta iota beta in Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos) in Hchk.
    unfold ms in Hchk. rewrite <- (adv_ret_epend regs pc mem (seg_rom segs) (getr regs 17)).
    eapply reach_ecall_check; [exact Hh | exact Hlazy | exact HF | exact HE | exact Hchk | exact Hh | exact Hlazy].
Qed.

End WithSegs.
