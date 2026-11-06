(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes FileSim
  AsanAcct LazyFrame NoReserve RefNodes CxNodesBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require NodesCfg.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma accesses_ret_only : forall r, syscall_effect_accesses (mkEffect r [] []) = [].
Proof. reflexivity. Qed.

Lemma accesses_copyins_ret : forall reads r,
  syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads ++ [].
Proof. reflexivity. Qed.

Lemma accesses_outside_lazy_app_nil : forall accs lazy,
  accesses_outside_lazy accs lazy -> accesses_outside_lazy (accs ++ []) lazy.
Proof. intros accs lazy H. rewrite app_nil_r. exact H. Qed.

Lemma accesses_outside_lazy_mono1 : forall (a : word) (n n' : nat) lazy,
  (n' <= n)%nat -> accesses_outside_lazy [(a, n)] lazy -> accesses_outside_lazy [(a, n')] lazy.
Proof.
  intros a n n' lazy Hle H b k lo sz Hin Hl. destruct Hin as [Hin|[]]. injection Hin as <- <-.
  eapply access_outside_range_mono; [exact Hle|]. apply (H a n lo sz); [left; reflexivity | exact Hl].
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_chk_ev_id : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hmat. split.
  - intros i. apply (sstep_syscall segs ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (Hh' i).
    + exact (Hmat i).
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma node_det_id : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  materialize_model_accesses m0 (syscall_effect_accesses eff0) = Some m0 ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hmat.
  apply (node_chk_ev_id ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_lt : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh'.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det_id ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - apply materialize_model_accesses_nil.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_copyins_mi : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  mat_id m' reads ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hmat.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det_id ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - rewrite accesses_copyins_ret. apply mat_id_app_nil. exact Hmat.
Qed.

Lemma node_ret_only_copyins_lt : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  accesses_outside_lazy reads (m_vm_lazy m') ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hout.
  eapply node_ret_only_copyins_mi; [exact Hh | exact Hsvc | exact Hchk | exact Hh' | apply mat_id_of_outside; exact Hout].
Qed.

Lemma srz_ret_only_silent_lt : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  crz segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hc.
  eapply crz_silent1; [eapply node_ret_only_lt; eassumption | exact Hc].
Qed.

Lemma srz_ret_only_copyins_silent_mi : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  mat_id m' reads ->
  crz segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hmat Hc.
  eapply crz_silent1; [eapply node_ret_only_copyins_mi; eassumption | exact Hc].
Qed.

Lemma srz_ret_only_copyins_silent_lt : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  accesses_outside_lazy reads (m_vm_lazy m') ->
  crz segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hout Hc.
  eapply crz_silent1; [eapply node_ret_only_copyins_lt; eassumption | exact Hc].
Qed.

Lemma srz_det_id : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  materialize_model_accesses m0 (syscall_effect_accesses eff0) = Some m0 ->
  crz segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hmat Hc.
  eapply crz_silent1; [eapply node_det_id; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma node_open_mi : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  mat_id model reads -> (forall fd, mat_id (mk fd) reads) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hsvc Hchk Hmk Hm0 Hm1 Hfree.
  assert (Hmat1 : forall fd r, materialize_model_accesses (mk fd) (syscall_effect_accesses (with_copyins reads (mkEffect r [] []))) = Some (mk fd)).
  { intros fd r. rewrite accesses_copyins_ret. apply mat_id_app_nil. apply Hm1. }
  assert (Hmat0' : forall r, materialize_model_accesses model (syscall_effect_accesses (with_copyins reads (mkEffect r [] []))) = Some model).
  { intros r. rewrite accesses_copyins_ret. apply mat_id_app_nil. exact Hm0. }
  split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_syscall segs ms model x8 _ model model [] Hh Hsvc).
      * apply check_syscall_ok_iff. rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
      * exact Hh.
      * apply Hmat0'.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_syscall segs ms model x8 _ (mk (alloc_fd (m_fds model))) (mk (alloc_fd (m_fds model))) [] Hh Hsvc).
      * apply check_syscall_ok_iff. rewrite Hchk. apply check_open_result_copyins_ok_iff.
        right. exists (alloc_fd (m_fds model)). auto.
      * apply Hmk.
      * apply Hmat1.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite Hmat0' in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite Hmat1 in Hmat. injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite Hmat0' in Hmat. discriminate.
      * subst fd. rewrite Hmat1 in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

Lemma node_open_lt : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = m_vm_lazy model) ->
  accesses_outside_lazy reads (m_vm_lazy model) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hsvc Hchk Hmk Hmklazy Hout Hfree.
  apply (node_open_mi ms model x8 reads mk Hh Hsvc Hchk Hmk); [| | exact Hfree].
  - apply mat_id_of_outside. exact Hout.
  - intros fd. apply mat_id_of_outside. rewrite Hmklazy. exact Hout.
Qed.

Lemma srz_open_mi : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  mat_id model reads -> (forall fd, mat_id (mk fd) reads) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     crz segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  crz segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                        (mk (alloc_fd (m_fds model)))) B ->
  NodesCfg.sysno_family_off cfg0 (bv_unsigned x8) = false ->
  crz segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hsvc Hchk Hmk Hm0 Hm1 Hfree HA HB Hfam.
  apply (crz_alt2_on segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open_mi; eassumption.
  - intros y Hy. cbn [cfg_ms] in Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hfam.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

Lemma srz_open_lt : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = m_vm_lazy model) ->
  accesses_outside_lazy reads (m_vm_lazy model) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     crz segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  crz segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                        (mk (alloc_fd (m_fds model)))) B ->
  NodesCfg.sysno_family_off cfg0 (bv_unsigned x8) = false ->
  crz segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hsvc Hchk Hmk Hmklazy Hout Hfree HA HB Hfam.
  apply (crz_alt2_on segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open_lt; eassumption.
  - intros y Hy. cbn [cfg_ms] in Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hfam.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_close : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                        (with_fds (fd_remove (m_fds model) fd) model)) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hc.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_only_silent_lt; [exact Hh | reflexivity | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
Qed.

(* [comment removed for export] *)
Lemma srz_ioctl_winsz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  e <> FdUrandom ->  (* [comment removed for export] *)
  getr regs 11 = Z_to_bv 64 0x5413 ->
  crz segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                        model) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hnn H11 Hc.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_only_silent_lt; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
  unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
  destruct e; try reflexivity. exfalso. apply Hnn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_read_dir : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  crz segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh H17 Hfd Hfd32 Hlk Hdir Hc.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_only_silent_lt; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite Hdir. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_read_file_mi : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  access_okb (getr regs 11) cnt = true ->
  (forall k, (k <= Z.to_nat cnt)%nat -> mat_id model [(getr regs 11, k)]) ->
  let bs := file_read data off (getr regs 12) in
  crz segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                               (wbytes mem (getr regs 11) bs) (seg_rom segs))
                        (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Haok Hmat bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(fold ms; rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Haok)) as [Hchk Hnu].
  unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  assert (HL : (length (file_read data off (getr regs 12)) <= Z.to_nat cnt)%nat).
  { rewrite length_file_read. unfold word_to_nat. rewrite H12, u64_lit by lia. lia. }
  subst bs. revert Hc Hchk HL.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk HL.
  eapply (srz_det_id _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk | exact Hnu
    | rewrite with_fds_halted'; exact Hh | | ].
  - destruct bs as [|b bsr]; cbn [delivered_writes syscall_effect_accesses eff_copyins eff_writes write_accesses app].
    + apply mat_id_with_fds. apply mat_id_nil.
    + apply mat_id_with_fds. apply Hmat. exact HL.
  - destruct bs as [|b bsr]; cbn [delivered_writes].
    + unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
    + unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

Lemma srz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  access_okb (getr regs 11) cnt = true ->
  accesses_outside_lazy [(getr regs 11, Z.to_nat cnt)] (m_vm_lazy model) ->
  let bs := file_read data off (getr regs 12) in
  crz segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                               (wbytes mem (getr regs 11) bs) (seg_rom segs))
                        (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Haok Hout bs Hc.
  eapply srz_read_file_mi; try eassumption.
  intros k Hk. apply mat_id_of_outside. eapply accesses_outside_lazy_mono1; [exact Hk | exact Hout].
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
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  (* [comment removed for export] *)
  Hypothesis Hmat : mat_id model (open_copyins ms).
  (* [comment removed for export] *)
  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma srz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    crz segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_ret_only_copyins_silent_mi; [exact Hh | reflexivity | | exact Hh | exact Hmat | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), Hp. apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_openat_empty : forall K,
    path_at segs regs mem [] ->
    crz segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_ret_only_copyins_silent_mi; [exact Hh | reflexivity | | exact Hh | exact Hmat | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem [] Hp).
    apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_openat_absent : forall p K,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = None ->
    crz segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hns Hnd Hfs Hc. cbv delta [post] in *.
    eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_ret_only_copyins_silent_mi; [exact Hh | reflexivity | | exact Hh | exact Hmat | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
    rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_openat_dirref : forall p KA KB,
    path_at segs regs mem p -> path_is_dirref p = true ->
    (forall e, In e openat_errnos -> crz segs (mkCfg (post (errno_ret e)) model) KA) ->
    crz segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hd HA HB. cbv delta [post] in *.
    assert (Hne : path_eqb p [] = false).
    { destruct p; [|reflexivity]. cbv in Hd. discriminate Hd. }
    eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_open_mi; [exact Hh | reflexivity | | | exact Hmat | | exact Hfree | | | rewrite H17; reflexivity].
    - intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem _ Hp).
      rewrite Hne, (path_is_dirref_no_slash _ Hd), Hd. apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. apply mat_id_with_fds. exact Hmat.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_openat_dot : forall KA KB,
    path_at segs regs mem dot_path ->
    (forall e, In e openat_errnos -> crz segs (mkCfg (post (errno_ret e)) model) KA) ->
    crz segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof. intros KA KB Hp HA HB. exact (srz_openat_dirref dot_path KA KB Hp eq_refl HA HB). Qed.

  (* [comment removed for export] *)
  Lemma srz_openat_file : forall p d KA KB,
    path_at segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> crz segs (mkCfg (post (errno_ret e)) model) KA) ->
    crz segs (mkCfg (post (alloc_fd fds))
                          (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hns Hnd Hfs HA HB. cbv delta [post] in *.
    eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_open_mi; [exact Hh | reflexivity | | | exact Hmat | | exact Hfree | | | rewrite H17; reflexivity].
    - intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
      rewrite (path_eqb_neq _ _ Hne), Hns, Hnd, Hfs. apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. apply mat_id_with_fds. exact Hmat.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

End WithSegs.
