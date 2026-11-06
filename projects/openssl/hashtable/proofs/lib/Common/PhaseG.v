(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts ModelAmb RefNodes ExistsRun
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section G.
  Variable segs : list Segment.

  Definition GG (mode : bool) (Q : config -> Prop) (T : TSet) (c : config) : Prop :=
    if mode then realizes segs c T else exists c', reach segs c c' /\ Q c'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma gg_true : forall Q T c, GG true Q T c <-> realizes segs c T.
  Proof. intros. unfold GG. tauto. Qed.

  Lemma gg_false : forall Q T c, GG false Q T c <-> exists c', reach segs c c' /\ Q c'.
  Proof. intros. unfold GG. tauto. Qed.

  Lemma gg_of_rz : forall Q T c, realizes segs c T -> GG true Q T c.
  Proof. intros Q T c H. exact H. Qed.

  Lemma rz_of_gg : forall Q T c, GG true Q T c -> realizes segs c T.
  Proof. intros Q T c H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma gg_here : forall Q T c, Q c -> GG false Q T c.
  Proof. intros Q T c H. exists c. split; [apply reach_refl | exact H]. Qed.

  Lemma gg_here_mode : forall mode Q T c, mode = false -> Q c -> GG mode Q T c.
  Proof. intros mode Q T c -> H. apply gg_here. exact H. Qed.

  (* [comment removed for export] *)
  Lemma gg_shape_any : forall Q T T' c, GG false Q T c -> GG false Q T' c.
  Proof. intros Q T T' c H. exact H. Qed.

  Lemma gg_reach : forall Q T c c', reach segs c c' -> GG false Q T c' -> GG false Q T c.
  Proof.
    intros Q T c c' Hr (c'' & Hr' & HQ). exists c''. split; [eapply reach_trans; eassumption | exact HQ].
  Qed.

  Lemma gg_mono : forall mode (Q Q' : config -> Prop) T c,
    (forall x, Q x -> Q' x) -> GG mode Q T c -> GG mode Q' T c.
  Proof.
    intros [|] Q Q' T c HQ H; [exact H|].
    destruct H as (c' & Hr & Hq). exists c'. split; [exact Hr | apply HQ, Hq].
  Qed.

  Lemma gg_conseq : forall mode Q T T' c, GG mode Q T c -> t_eq T T' -> GG mode Q T' c.
  Proof. intros [|] Q T T' c H Heq; [exact (rz_conseq segs c T T' H Heq) | exact H]. Qed.

  (* [comment removed for export] *)
  Lemma gg_silent1 : forall mode Q T c c',
    node_ok segs c unit (fun _ => []) (fun _ => c') -> GG mode Q T c' -> GG mode Q T c.
  Proof.
    intros [|] Q T c c' Hnode H.
    - exact (rz_silent1 segs c c' T Hnode H).
    - eapply gg_reach; [| exact H]. apply reach_step. exact (proj1 Hnode tt).
  Qed.

  (* [comment removed for export] *)
  Lemma gg_alt2 : forall mode Q c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet) (a0 : IA) (b0 : IB),
    node_ok segs c (IA + IB) (fun _ => []) nx ->
    (mode = true -> forall i, realizes segs (nx (inl i)) A) ->
    (forall i, GG mode Q B (nx (inr i))) ->
    GG mode Q (t_alt2 A B) c.
  Proof.
    intros [|] Q c IA IB nx A B a0 b0 Hnode HA HB.
    - exact (rz_alt2 segs c IA IB nx A B a0 b0 Hnode (HA eq_refl) HB).
    - eapply gg_reach; [| exact (HB b0)]. apply reach_step. exact (proj1 Hnode (inr b0)).
  Qed.

  (* [comment removed for export] *)
  Lemma gg_cases : forall mode Q c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
    node_ok segs c I (fun _ => []) nx ->
    (mode = true -> forall i, realizes segs (nx i) (T i)) ->
    GG mode Q (T i0) (nx i0) ->
    GG mode Q (t_alt T) c.
  Proof.
    intros [|] Q c I nx T i0 Hnode HA HB.
    - exact (rz_cases segs c I nx T i0 Hnode (HA eq_refl)).
    - eapply gg_reach; [| exact HB]. apply reach_step. exact (proj1 Hnode i0).
  Qed.

  (* [comment removed for export] *)
  Lemma gg_step : forall mode Q ms model ms' T,
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    GG mode Q T (mkCfg ms' model) -> GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model ms' T Hh Hlazy Hsvc Hstep H.
    eapply gg_silent1; [apply node_instr; eassumption | exact H].
  Qed.

  Lemma gg_msteps : forall mode Q ms ms' model T,
    m_halted model = None -> m_vm_lazy model = [] ->
    msteps segs ms ms' ->
    GG mode Q T (mkCfg ms' model) -> GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms ms' model T Hh Hlazy Hms;
      induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
    eapply gg_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma gg_sys : forall mode Q regs pc mem rom model w T,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    GG mode Q T (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
    GG mode Q T (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros mode Q regs pc mem rom model w T Hh Hlazy HF HE Hc.
    eapply gg_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma gg_det : forall mode Q ms model x8 eff0 m0 T,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    (forall eff m' evs,
       check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
       (eff = eff0 /\ m' = m0 /\ evs = [])) ->
    (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
    m_halted m0 = None -> m_vm_lazy m0 = [] ->
    GG mode Q T (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) ->
    GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
    eapply gg_silent1; [eapply node_det; eassumption | exact Hc].
  Qed.

  Lemma gg_ret_only_silent : forall mode Q ms model x8 r m' T,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
    m_halted m' = None -> m_vm_lazy m' = [] ->
    GG mode Q T (mkCfg (advance_past_svc (set_gpr0 ms r)) m') ->
    GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
    eapply gg_silent1; [eapply node_ret_only; eassumption | exact Hc].
  Qed.

  Lemma gg_ret_only_copyins_silent : forall mode Q ms model x8 reads r m' T,
    m_halted model = None ->
    ms_svc_pending ms = Some x8 ->
    (forall eff, check_syscall (sys_input segs ms x8) eff model
                 = check_ret_only_copyins reads eff r m' []) ->
    m_halted m' = None -> m_vm_lazy m' = [] ->
    GG mode Q T (mkCfg (advance_past_svc (set_gpr0 ms r)) m') ->
    GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
    eapply gg_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma gg_munmap_raw : forall mode Q ms model x8 T,
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    GG mode Q T (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                       (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) ->
    GG mode Q T (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
    eapply gg_silent1; [| exact Hc]. split.
    - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      + exact Hh.
      + exact Hsvc.
      + apply munmap_ok; assumption.
      + rewrite munmap_model_halted; exact Hh.
      + apply materialize_model_accesses_no_lazy. exact (munmap_model_no_lazy _ _ _ Hlazy).
    - intros e st Hss.
      destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss) as [-> ->].
      exists tt. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma gg_mmap_raw : forall mode Q ms model x8 A B,
    m_halted model = None -> m_vm_lazy model = [] ->
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (mode = true -> forall e, In e mmap_errnos ->
       realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       GG mode Q B (mkCfg (advance_past_svc
                             (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                          (mmap_model a (page_round_up (ms_gpr ms 1)) model))) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    GG mode Q (t_alt2 A B) (mkCfg ms model).
  Proof.
    intros mode Q ms model x8 A B Hh Hlazy Hsvc Hno Hargs HA HB Hex.
    set (n := page_round_up (ms_gpr ms 1)).
    set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
    destruct Hex as [b0 Hb0].
    pose (IA := {e : Z | In e mmap_errnos}).
    pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
    pose (nx := fun (i : IA + IB) =>
      match i with
      | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
      | inr (exist _ a _) =>
          mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)]))) (mmap_model a n model)
      end).
    apply (gg_alt2 mode Q (mkCfg ms model) IA IB nx A B
             (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ b0 Hb0)).
    - split.
      + intros [[e He] | [a Ha]]; cbn.
        * rewrite <- (apply_effect_no_write ms (errno_ret e)).
          apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] []) model model []).
          -- exact Hh.
          -- exact Hsvc.
          -- apply mmap_fail_ok; assumption.
          -- exact Hh.
          -- apply materialize_model_accesses_no_lazy. exact Hlazy.
        * apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
                   (mmap_model a n model) (mmap_model a n model) []).
          -- exact Hh.
          -- exact Hsvc.
          -- apply mmap_succ_ok; assumption.
          -- rewrite mmap_model_halted; exact Hh.
          -- apply materialize_model_accesses_no_lazy.
             exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
      + intros e st Hss.
        destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
          as [-> [(er & Her & ->) | (a & Ha & ->)]].
        * exists (inl (exist _ er Her)). split; reflexivity.
        * exists (inr (exist _ a Ha)). split; reflexivity.
    - intros Hm [e He]. cbn. apply (HA Hm e He).
    - intros [a Ha]. cbn. apply HB. exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma gg_close : forall mode Q regs (pc : word) mem model w fd e K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 57 ->
    getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
    fd_lookup (m_fds model) fd = Some e ->
    GG mode Q K (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) ->
    GG mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply gg_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
    - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
      unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
    - rewrite with_fds_halted'. exact Hh.
    - rewrite with_fds_lazy. exact Hlazy.
  Qed.

  Lemma gg_read_file : forall mode Q regs (pc : word) mem model w fd p off data (cnt : Z) K,
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
    GG mode Q K (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                             (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) ->
    GG mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hacc bs Hc.
    assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
    rewrite Z2Nat.id in Hw by lia.
    set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
    assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
    { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
    destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
                ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
                ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
                ltac:(fold ms; rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Hacc)) as [Hchk Hnu].
    unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
    subst bs. revert Hc Hchk.
    generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
    eapply (gg_det mode Q _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
              (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
      [exact Hh | reflexivity | exact Hchk | exact Hnu
      | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
    destruct bs as [|b bsr]; cbn [delivered_writes].
    - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
    - unfold ms. rewrite adv_write1_epend. exact Hc.
  Qed.

  Lemma gg_mmap_anon : forall mode Q regs (pc : word) mem model w (len : Z) KA KB,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 222 ->
    getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
    getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
    getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
    let n := page_round_up_Z len in
    (exists a, grant_ok (getr regs 10) model a n = true) ->
    (mode = true -> forall e, In e mmap_errnos ->
       realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
    (forall a, grant_ok (getr regs 10) model a n = true ->
       GG mode Q KB (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                  (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                          (mmap_model a (Z_to_bv 64 n) model))) ->
    GG mode Q (t_alt2 KA KB) (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Hex HA HB.
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
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
    eapply (gg_mmap_raw mode Q ms model (getr regs 17) KA KB Hh Hlazy eq_refl
              ltac:(rewrite H17; apply u64_lit; lia) Hargs).
    - intros Hm e He. unfold ms. rewrite adv_set_epend. apply (HA Hm). exact He.
    - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
    - rewrite H0, Hu1. exact Hex.
  Qed.

  Lemma gg_munmap : forall mode Q regs (pc : word) mem model w (a : word) (len : Z) K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 215 ->
    getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
    getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
    (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
    map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
    GG mode Q K (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                       (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) ->
    GG mode Q K (mkCfg (mkst regs pc mem (seg_rom segs)) model).
  Proof.
    intros mode Q regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
    assert (Hlen' : (len < two_pow_64)%Z).
    { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a).
      unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
    eapply gg_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
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
    eapply (gg_munmap_raw mode Q ms model (getr regs 17));
      [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
    unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem gg_run : forall mode Q fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                           E M rom R model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E M kn ->
    scs_denot segs M E scs -> scs_denot segs M E scs2 ->
    m_halted model = None ->
    m_vm_lazy model = [] ->
    (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
       M' = mem_denot E M (s_log ss') ->
       GG mode Q T (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model)) ->
    GG mode Q T (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model).
  Proof.
    intros mode Q fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
           Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
    destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
      as (R' & HR' & Hlf & Hms).
    eapply gg_msteps; [exact Hh | exact Hlazy | exact Hms |].
    apply (Hcont R' _ HR'); [|reflexivity].
    eapply carry_after; eassumption.
  Qed.

End G.

(* [comment removed for export] *)
Ltac gg_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- GG _ ?mode ?Q ?T (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (gg_run segs mode Q fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "gg_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => gg_block_with HR HK fuel stops scr NX keep
  end.
