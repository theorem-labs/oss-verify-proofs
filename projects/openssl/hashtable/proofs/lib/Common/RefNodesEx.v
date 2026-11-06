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
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts ModelAmb RefNodes ExistsRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reach_ecall : forall regs pc mem rom model w,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  reach segs (mkCfg (mkst regs pc mem rom) model) (mkCfg (epend regs pc mem rom (getr regs 17)) model).
Proof.
  intros regs pc mem rom model w Hh Hlazy HF HE.
  apply (reach_instr segs); [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma reach_of_node : forall c (I : Type) (nx : I -> config) (i : I),
  node_ok segs c I (fun _ => []) nx -> reach segs c (nx i).
Proof. intros c I nx i [Hc _]. apply reach_step. apply Hc. Qed.

(* [comment removed for export] *)
Lemma reach_ecall_node : forall regs pc mem rom model w (I : Type) (nx : I -> config) (i : I),
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  node_ok segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) I (fun _ => []) nx ->
  reach segs (mkCfg (mkst regs pc mem rom) model) (nx i).
Proof.
  intros regs pc mem rom model w I nx i Hh Hlazy HF HE Hn.
  eapply reach_trans; [eapply reach_ecall; eassumption | eapply reach_of_node; exact Hn].
Qed.

(* [comment removed for export] *)
Lemma reach_ecall_check : forall regs pc mem rom model w eff m',
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model = CheckOk m' [] ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  reach segs (mkCfg (mkst regs pc mem rom) model)
             (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17)) eff)) m').
Proof.
  intros regs pc mem rom model w eff m' Hh Hlazy HF HE Hc Hh' Hlazy'.
  eapply reach_trans; [eapply reach_ecall; eassumption |].
  apply reach_step. apply (sstep_of_check segs _ model (getr regs 17)); [exact Hh | reflexivity | exact Hc | exact Hh' | exact Hlazy'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ex_set_tid : forall regs (pc : word) mem rom model w tid,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
  reach segs (mkCfg (mkst regs pc mem rom) model)
             (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)).
Proof.
  intros regs pc mem rom model w tid HF HE Hh Hlazy H17 Htid Hr.
  rewrite <- (adv_set_epend regs pc mem rom (getr regs 17) tid).
  apply (reach_ecall_node regs pc mem rom model w tid_I
           (fun i => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem rom (getr regs 17)) (proj1_sig i)))
                           (with_tid (proj1_sig i) model))
           (exist _ tid Hr) Hh Hlazy HF HE).
  eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid].
Qed.

(* [comment removed for export] *)
Lemma ex_set_tid_1 : forall regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  reach segs (mkCfg (mkst regs pc mem rom) model)
             (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 1)) (v_addi pc 4) mem rom) (with_tid (Z_to_bv 64 1) model)).
Proof. intros. eapply ex_set_tid; try eassumption. apply one_tid_ok. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ex_close : forall regs (pc : word) mem model w fd e,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                    (with_fds (fd_remove (m_fds model) fd) model)).
Proof.
  intros regs pc mem model w fd e HF HE Hh Hlazy H17 Hfd Hfd32 Hlk.
  rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
  apply (reach_ecall_node regs pc mem (seg_rom segs) model w unit
           (fun _ => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem (seg_rom segs) (getr regs 17)) (Z_to_bv 64 0)))
                           (with_fds (fd_remove (m_fds model) fd) model)) tt Hh Hlazy HF HE).
  eapply node_ret_only; [exact Hh | reflexivity | | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy].
  intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
  unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ex_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  access_okb (getr regs 11) cnt = true ->
  let bs := file_read data off (getr regs 12) in
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                          (wbytes mem (getr regs 11) bs) (seg_rom segs))
                    (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)).
Proof.
  intros regs pc mem model w fd p off data cnt HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Haok bs.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(fold ms; rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Haok)) as [Hchk _].
  unfold ms in Hchk. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  subst bs. revert Hchk.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hchk.
  assert (Hsucc : mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (wbytes mem (getr regs 11) bs) (seg_rom segs)
                  = advance_past_svc (apply_effect ms (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []))).
  { destruct bs as [|b bsr]; cbn [delivered_writes]; unfold ms.
    - rewrite adv_ret_epend. reflexivity.
    - rewrite adv_write1_epend. reflexivity. }
  rewrite Hsucc. unfold ms.
  eapply reach_ecall_check; [exact Hh | exact Hlazy | exact HF | exact HE | | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy].
  apply (proj2 (Hchk _ _ _)). repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ex_read_dir : forall regs (pc : word) mem model w fd,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model).
Proof.
  intros regs pc mem model w fd HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir.
  rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
  apply (reach_ecall_node regs pc mem (seg_rom segs) model w unit
           (fun _ => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem (seg_rom segs) (getr regs 17)) (errno_ret EISDIR))) model)
           tt Hh Hlazy HF HE).
  eapply node_ret_only; [exact Hh | reflexivity | | exact Hh | exact Hlazy].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite Hdir. reflexivity.
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

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  (* [comment removed for export] *)
  Lemma ex_openat_absent : forall p,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = None ->
    reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (mkCfg (post (errno_ret ENOENT)) model).
  Proof.
    intros p Hp Hne Hns Hnd Hfs. cbv beta delta [post].
    rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
    apply (reach_ecall_node regs pc mem (seg_rom segs) model w unit
             (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOENT))) model) tt Hh Hlazy HF HE).
    eapply node_ret_only_copyins; [exact Hh | reflexivity | | exact Hh | exact Hlazy].
    intros eff. cbv delta [ms].
    rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
    rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma ex_openat_file : forall p d,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d ->
    reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
               (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)).
  Proof.
    intros p d Hp Hne Hns Hnd Hfs. cbv beta delta [post fds].
    rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
    apply (reach_ecall_node regs pc mem (seg_rom segs) model w (open_I model)
             (open_nx ms model (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
             (inr tt) Hh Hlazy HF HE).
    eapply node_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree].
    - intros eff. cbv delta [ms].
      rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
      rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_open_result.
    - intros fd. rewrite with_fds_halted'. exact Hh.
    - intros fd. rewrite with_fds_lazy. exact Hlazy.
  Qed.

  (* [comment removed for export] *)
  Lemma ex_openat_file_err : forall p d e,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d -> In e openat_errnos ->
    reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (mkCfg (post (errno_ret e)) model).
  Proof.
    intros p d e Hp Hne Hns Hnd Hfs He. cbv beta delta [post fds].
    rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
    apply (reach_ecall_node regs pc mem (seg_rom segs) model w (open_I model)
             (open_nx ms model (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
             (inl (exist _ e He)) Hh Hlazy HF HE).
    eapply node_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree].
    - intros eff. cbv delta [ms].
      rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
      rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_open_result.
    - intros fd. rewrite with_fds_halted'. exact Hh.
    - intros fd. rewrite with_fds_lazy. exact Hlazy.
  Qed.

  (* [comment removed for export] *)
  Lemma ex_openat_dirref : forall p,
    path_at segs regs mem p -> path_is_dirref p = true ->
    reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
               (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)).
  Proof.
    intros p Hp Hd. cbv beta delta [post fds].
    assert (Hne : path_eqb p [] = false).
    { destruct p; [|reflexivity]. cbv in Hd. discriminate Hd. }
    rewrite <- (adv_set_epend regs pc mem (seg_rom segs) (getr regs 17)).
    apply (reach_ecall_node regs pc mem (seg_rom segs) model w (open_I model)
             (open_nx ms model (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model))
             (inr tt) Hh Hlazy HF HE).
    eapply node_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree].
    - intros eff. cbv delta [ms].
      rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
      rewrite Hne, (path_is_dirref_no_slash _ Hd), Hd. apply check_copyins_after_open_result.
    - intros fd. rewrite with_fds_halted'. exact Hh.
    - intros fd. rewrite with_fds_lazy. exact Hlazy.
  Qed.
End Openat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ex_brk_query : forall regs (pc : word) mem model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem (seg_rom segs)) model).
Proof.
  intros regs pc mem model w HF HE Hh Hlazy H17 H10.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_refl. }
  pose proof (reach_ecall_node regs pc mem (seg_rom segs) model w _ _ (exist _ _ Hq) Hh Hlazy HF HE
                (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno)) as Hr.
  cbn [proj1_sig] in Hr.
  rewrite H0, brk_zeros_query, brk_unmaps_keep, (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta in Hr.
  unfold ms in Hr. rewrite adv_ret_epend in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma ex_brk_grow : forall regs (pc : word) mem model w (d : Z),
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
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                          (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
                    (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                   (vm_noaccess h) (vm_start_brk h)
                                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)).
Proof.
  intros regs pc mem model w d HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req).
  { rewrite H0. apply (proj2 (brk_r_ok_grow_cases model req req ltac:(lia) ltac:(fold h; lia)
                                ltac:(fold h; fold b; lia))). right. split; [reflexivity | exact Hadm]. }
  pose proof (reach_ecall_node regs pc mem (seg_rom segs) model w _ _ (exist _ _ Hgrow) Hh Hlazy HF HE
                (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno)) as Hr.
  cbn [proj1_sig] in Hr. fold h in Hr.
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite H0 in Hr. fold b in Hr. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) in Hr by lia.
  unfold brk_page_range in Hr.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hr by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned req)) in Hr
    by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hr.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in Hr by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  rewrite Hureq in Hr. replace (bv_unsigned b + d - bv_unsigned b)%Z with d in Hr by lia.
  unfold req, b, h in Hr. rewrite (brk_model_grow_eq model d) in Hr by assumption.
  unfold ms in Hr. rewrite adv_zeros1_epend in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma ex_brk_grow_keep : forall regs (pc : word) mem model w (req : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model).
Proof.
  intros regs pc mem model w req HF HE Hh Hlazy H17 h b H10 Hpos Hs Hb.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b).
  { rewrite H0. apply (proj2 (brk_r_ok_grow_cases model req b Hpos Hs Hb)). left. reflexivity. }
  pose proof (reach_ecall_node regs pc mem (seg_rom segs) model w _ _ (exist _ _ Hkeep) Hh Hlazy HF HE
                (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno)) as Hr.
  cbn [proj1_sig] in Hr. fold h in Hr. fold b in Hr.
  rewrite brk_zeros_keep, brk_unmaps_keep in Hr. unfold b, h in Hr. rewrite brk_model_keep in Hr.
  unfold ms in Hr. rewrite adv_ret_epend in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ex_mmap_anon : forall regs (pc : word) mem model w (len : Z) (a : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  grant_ok (getr regs 10) model a n = true ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                    (mmap_model a (Z_to_bv 64 n) model)).
Proof.
  intros regs pc mem model w len a HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Ha.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply reach_trans; [eapply reach_ecall; eassumption |]. fold ms.
  pose proof (reach_syscall segs ms model (getr regs 17) _ _ _ Hh eq_refl
                (mmap_succ_ok segs ms (getr regs 17) model a ltac:(rewrite H17; apply u64_lit; lia) Hargs
                   ltac:(rewrite H0, Hu1; exact Ha))
                ltac:(rewrite mmap_model_halted; exact Hh)
                (materialize_model_accesses_no_lazy _ _ (eq_trans (mmap_model_lazy _ _ _) Hlazy))) as Hr.
  rewrite Hpr in Hr. unfold ms, epend in Hr. rewrite adv_mmap_grant in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma ex_mmap_anon_enomem : forall regs (pc : word) mem model w (len : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem (seg_rom segs)) model).
Proof.
  intros regs pc mem model w len HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  eapply reach_trans; [eapply reach_ecall; eassumption |]. fold ms.
  pose proof (reach_syscall segs ms model (getr regs 17) _ _ _ Hh eq_refl
                (mmap_fail_ok segs ms (getr regs 17) model ENOMEM ltac:(rewrite H17; apply u64_lit; lia) Hargs
                   ENOMEM_in_mmap_errnos)
                Hh (materialize_model_accesses_no_lazy _ _ Hlazy)) as Hr.
  rewrite apply_effect_no_write in Hr. unfold ms in Hr. rewrite adv_set_epend in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ex_mmap_noaccess : forall regs (pc : word) mem model w (len : Z) (a : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  grant_ok_na (getr regs 10) model a n = true ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                    (noaccess_model a (Z_to_bv 64 n) model)).
Proof.
  intros regs pc mem model w len a HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Ha.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  pose proof (mmap_noaccess_check segs ms (getr regs 17) model (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []) Hno Hargs) as Hchk.
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  rewrite Hu1, H0 in Hchk. cbv zeta iota beta in Hchk. fold n in Hchk.
  assert (Hn0 : (0 <= n)%Z) by (unfold n; apply page_round_up_Z_nonneg; lia).
  rewrite (grant_na_not_errno _ model a n Hn0 Ha), Ha in Hchk. cbn [andb] in Hchk.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl) in Hchk.
  unfold ms in Hchk. rewrite <- (adv_unmaps1_epend regs pc mem (seg_rom segs) (getr regs 17)).
  eapply reach_ecall_check; [exact Hh | exact Hlazy | exact HF | exact HE | exact Hchk
                            | unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh
                            | unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ex_mmap_fixed_noaccess : forall regs (pc : word) mem model w (addr : word) (len : Z),
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
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                    (fixed_noaccess_model addr n model)).
Proof.
  intros regs pc mem model w addr len HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. pose proof stack_max_size_val as Hsms.
  unfold two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  pose proof (mmap_fixed_check segs ms (getr regs 17) model (mkEffectU addr [] [] [(addr, n)] [] []) addr len Hno Hargs
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hrf Hmc) as Hchk.
  cbv zeta iota beta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  rewrite Haddr_ne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl) in Hchk. cbn [andb] in Hchk.
  unfold ms in Hchk. rewrite <- (adv_unmaps1_epend regs pc mem (seg_rom segs) (getr regs 17)).
  eapply reach_ecall_check; [exact Hh | exact Hlazy | exact HF | exact HE | exact Hchk
                            | unfold fixed_noaccess_model; rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh
                            | unfold fixed_noaccess_model; apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ex_mprotect : forall regs (pc : word) mem model w (addr : word) (len : Z),
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
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) (seg_rom segs))
                    (mprotect_model addr n model)).
Proof.
  intros regs pc mem model w addr len HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (mprotect_check segs ms (getr regs 17) model (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []) addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta iota beta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false in Hchk. cbv iota in Hchk.
  unfold w_is0 in Hchk. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl) in Hchk. cbn [andb] in Hchk.
  unfold ms in Hchk. rewrite <- (adv_zeros1_epend regs pc mem (seg_rom segs) (getr regs 17)).
  eapply reach_ecall_check; [exact Hh | exact Hlazy | exact HF | exact HE | exact Hchk
                            | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh
                            | unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ex_munmap : forall regs (pc : word) mem model w (a : word) (len : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  reach segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
             (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                          (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                    (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)).
Proof.
  intros regs pc mem model w a len HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a).
    unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply reach_trans; [eapply reach_ecall; eassumption |]. fold ms.
  pose proof (reach_syscall segs ms model (getr regs 17) _ _ _ Hh eq_refl
                (munmap_ok segs ms (getr regs 17) model ltac:(rewrite H17; apply u64_lit; lia) Hargs)
                ltac:(rewrite munmap_model_halted; exact Hh)
                (materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy))) as Hr.
  unfold munmap_eff in Hr. rewrite H0, Hpr in Hr. unfold ms in Hr. rewrite adv_unmaps1_epend in Hr. exact Hr.
Qed.

End WithSegs.
