(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts RefNodes LazyFrame Hoare LibWritev LibWritevX.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nolazy_rng (L : list (word * word)) (a : word) (n : Z) : Prop :=
  forall k, (0 <= k < n)%Z -> page_in_ranges (page_base_of (bv_unsigned a + k)) L = false.

Definition acc_nolazy (L : list (word * word)) (accs : list (word * nat)) : Prop :=
  forall a n, In (a, n) accs -> nolazy_rng L a (Z.of_nat n).

Lemma nolazy_rng_sub : forall L a n m, nolazy_rng L a n -> (m <= n)%Z -> nolazy_rng L a m.
Proof. intros L a n m H Hm k Hk. apply H. lia. Qed.

Lemma acc_nolazy_nil : forall L, acc_nolazy L [].
Proof. intros L a n []. Qed.

Lemma acc_nolazy_cons : forall L a n accs, nolazy_rng L a (Z.of_nat n) -> acc_nolazy L accs -> acc_nolazy L ((a, n) :: accs).
Proof. intros L a n accs H1 H2 a' n' [E|Hin]; [injection E as <- <-; exact H1 | exact (H2 a' n' Hin)]. Qed.

Lemma acc_nolazy_app : forall L l1 l2, acc_nolazy L l1 -> acc_nolazy L l2 -> acc_nolazy L (l1 ++ l2).
Proof. intros L l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 a n Hin) | exact (H2 a n Hin)]. Qed.

Lemma acc_nolazy_one : forall L a n m, nolazy_rng L a m -> (Z.of_nat n <= m)%Z -> acc_nolazy L [(a, n)].
Proof. intros L a n m H Hm. apply acc_nolazy_cons; [exact (nolazy_rng_sub L a m _ H Hm) | apply acc_nolazy_nil]. Qed.

(* [comment removed for export] *)
Lemma mat_id_of_nolazy : forall m accs,
  acc_nolazy (m_vm_lazy m) accs -> materialize_model_accesses m accs = Some m.
Proof.
  intros m accs H. unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m) _ _ accs).
  - rewrite with_vm_backing_id. reflexivity.
  - unfold newly_materialized_pages. apply filter_all_false. intros p Hp.
    destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (H a n Hin (Z.of_nat k) ltac:(lia)). reflexivity.
Qed.

Lemma with_fds_vm_lazy : forall f m, m_vm_lazy (with_fds f m) = m_vm_lazy m.
Proof. intros f [fd vm io fsy pr lim tm]. reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend_lz : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

Lemma srz_sys_lz : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply (srz_step_disjoint segs scfg _ model _ [] T Hh); [reflexivity | eapply stepacc_ecall_epend_lz; eassumption | | exact Hc].
  intros a n lo sz [].
Qed.


(* [comment removed for export] *)
Lemma node_svc_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
       (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
    \/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, acc_nolazy (m_vm_lazy (ms' i)) (syscall_effect_accesses (effs i))) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hnl. split.
  - intros i.
    apply (sstep_cfg_syscall segs scfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc
             (Hok i) (Hns i) (Hh' i)).
    apply mat_id_of_nolazy. exact (Hnl i).
  - intros e st Hss.
    destruct (sstep_cfg_svc_cases segs scfg ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hspec &
           [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (Hum & -> & ->)].
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
      rewrite (mat_id_of_nolazy _ _ (Hnl i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
      rewrite (mat_id_of_nolazy _ _ (Hnl i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [_ Hh3]];
        [rewrite Hh' in Hh2; discriminate | rewrite Hh3 in Hh2; discriminate].
    + exfalso. exact (Hnu Hum).
Qed.

Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, acc_nolazy (m_vm_lazy (ms' i)) (syscall_effect_accesses (effs i))) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hnl Hns.
  apply (node_svc_mat ms model x8 I effs ms' evs Hh Hsvc).
  - intros i. apply check_syscall_ok_iff. apply Hok.
  - exact Hns.
  - intros eff m' ev Hspec. left. apply Hinv. apply check_syscall_ok_iff. exact Hspec.
  - intros Hum. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. exact Hum.
  - exact Hh'.
  - exact Hnl.
Qed.

Lemma node_det_mat : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  acc_nolazy (m_vm_lazy m0) (syscall_effect_accesses eff0) ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hnl0.
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
            exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
  { intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
  apply (node_chk_ev_mat ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - exact Hinv.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hnl0.
  - apply (uniform_not_spurious segs scfg ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
             (refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
    intros []. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_silent_lz : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hc.
  eapply srz_silent1; [| exact Hc].
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det_mat ms model x8 (mkEffect r [] []) m' [] Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - apply acc_nolazy_nil.
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_copyins_silent_lz : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  acc_nolazy (m_vm_lazy m') reads ->
  srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hnl Hc.
  eapply srz_silent1; [| exact Hc].
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det_mat ms model x8 (with_copyins reads (mkEffect r [] [])) m' [] Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - unfold syscall_effect_accesses. cbn. rewrite app_nil_r. exact Hnl.
Qed.

Lemma rz_det_lz : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  acc_nolazy (m_vm_lazy m0) (syscall_effect_accesses eff0) ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hnl0 Hc.
  eapply srz_silent1; [eapply node_det_mat; eassumption | exact Hc].
Qed.


(* [comment removed for export] *)
Lemma sstep_of_check_mat : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  acc_nolazy (m_vm_lazy m') (syscall_effect_accesses eff) ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hnl.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply mat_id_of_nolazy. exact Hnl.
Qed.

Lemma accesses_with_copyins_ret : forall reads r,
  syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads.
Proof. intros. unfold syscall_effect_accesses. cbn. apply app_nil_r. Qed.

(* [comment removed for export] *)
Lemma node_open_lz : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  acc_nolazy (m_vm_lazy model) reads ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = m_vm_lazy model) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  fam_on segs scfg ms ->
  node_ok segs scfg (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hnl Hsvc Hchk Hmk Hmklazy Hfree Hon.
  apply node_ok_of_pnode; [| exact Hon]. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | exact Hh | rewrite accesses_with_copyins_ret; exact Hnl].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | apply Hmk | rewrite accesses_with_copyins_ret, Hmklazy; exact Hnl].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite accesses_with_copyins_ret, (mat_id_of_nolazy _ _ Hnl) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite accesses_with_copyins_ret, (mat_id_of_nolazy (mk _) reads) in Hmat by (rewrite Hmklazy; exact Hnl).
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite accesses_with_copyins_ret, (mat_id_of_nolazy _ _ Hnl) in Hmat. discriminate.
      * rewrite accesses_with_copyins_ret, (mat_id_of_nolazy (mk _) reads) in Hmat by (rewrite Hmklazy; exact Hnl). discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

Lemma rz_open_lz : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  acc_nolazy (m_vm_lazy model) reads ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = m_vm_lazy model) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  fam_on segs scfg ms ->
  (forall e, In e openat_errnos ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  srealizes segs scfg (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hnl Hsvc Hchk Hmk Hmklazy Hfree Hon HA HB.
  apply (srz_alt2 segs scfg (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open_lz; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close_lz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
Qed.

Lemma rz_ioctl_winsz_lz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end = true ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hnd H11 Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
  unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
  destruct e; first [reflexivity | discriminate Hnd].
Qed.

Lemma rz_read_dir_lz : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  (bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh H17 Hfd Hfd32 Hlk Hts Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite (access_okb_intro_le _ _ (proj1 (bv_unsigned_in_range 64 (getr regs 12))) Hts).
  reflexivity.
Qed.

Lemma rz_read_dir_cnt_lz : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt -> (0 <= cnt)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd cnt K HF HE Hh H17 Hfd Hfd32 Hlk H12 Hc0 Hts Hc.
  eapply (rz_read_dir_lz regs pc mem model w fd K); try eassumption.
  rewrite H12, u64_lit; [exact Hts|]. unfold TASK_SIZE in Hts. pose proof (u64_range (getr regs 11)). lia.
Qed.

(* [comment removed for export] *)
Lemma rz_read_file_lz : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 65536)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) (getr regs 11) cnt ->
  let bs := file_read data off (getr regs 12) in
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hts Hnl bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; apply access_okb_intro_le; lia)) as [Hchk Hnu].
  unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  assert (Hlen : (Z.of_nat (length bs) <= cnt)%Z).
  { subst bs. rewrite length_file_read. unfold word_to_nat. rewrite H12, u64_lit by lia. lia. }
  subst bs. revert Hc Hchk Hlen.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk Hlen.
  eapply (rz_det_lz _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk | exact Hnu
    | rewrite with_fds_halted'; exact Hh | | ].
  - rewrite with_fds_vm_lazy. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    destruct bs as [|b bsr]; cbn [delivered_writes write_accesses length]; [apply acc_nolazy_nil|].
    apply (acc_nolazy_one _ _ _ cnt Hnl Hlen).
  - destruct bs as [|b bsr]; cbn [delivered_writes].
    + unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
    + unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cstr_access_len_aux_le : forall mp fuel a, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp fuel. induction fuel as [|f IH]; intros a; cbn [cstr_access_len_aux]; [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)). lia.
Qed.

Section OpenatLz.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.
  Hypothesis Hfs_on : sc_fs scfg = true.
  (* [comment removed for export] *)
  Hypothesis Hnl : nolazy_rng (m_vm_lazy model) (getr regs 11) 4096.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma open_copyins_nolazy : acc_nolazy (m_vm_lazy model) (open_copyins ms).
  Proof.
    unfold open_copyins. cbv delta [ms]. rewrite ms_gpr_epend1.
    eapply acc_nolazy_one; [exact Hnl|].
    pose proof (cstr_access_len_aux_le (ms_read_byte (epend regs pc mem (seg_rom segs) (getr regs 17))) path_max (getr regs 11)) as Hle.
    unfold path_max in Hle at 2. lia.
  Qed.

  Lemma rz_openat_toolong_lz : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    srealizes segs scfg (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), Hp. apply check_copyins_after_ret_only.
  Qed.

  Lemma rz_openat_empty_lz : forall K,
    path_at segs regs mem [] ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem [] Hp). apply check_copyins_after_ret_only.
  Qed.

  Lemma rz_openat_absent_lz : forall p K,
    path_at segs regs mem p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hpl Hfs Hc. cbv delta [post] in *.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
    rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
    apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma rz_openat_dirref_lz : forall p KA KB,
    path_at segs regs mem p -> path_is_dirref p = true ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hdr HA HB. cbv delta [post] in *.
    assert (Hne : p <> []) by (intros ->; discriminate Hdr).
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_open_lz; [exact Hh | exact open_copyins_nolazy | reflexivity | | | | exact Hfree | exact (fam_on_openat_ms segs scfg regs pc mem H17 Hfs_on) | |].
    - intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem _ Hp).
      rewrite (path_eqb_neq _ _ Hne), (path_is_dirref_no_slash _ Hdr), Hdr.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. apply with_fds_vm_lazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  Lemma rz_openat_dot_lz : forall KA KB,
    path_at segs regs mem dot_path ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof. intros KA KB Hp. apply (rz_openat_dirref_lz dot_path KA KB Hp). reflexivity. Qed.

  Lemma rz_openat_file_lz : forall p d KA KB,
    path_at segs regs mem p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_open_lz; [exact Hh | exact open_copyins_nolazy | reflexivity | | | | exact Hfree | exact (fam_on_openat_ms segs scfg regs pc mem H17 Hfs_on) | |].
    - intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
      rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. apply with_fds_vm_lazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End OpenatLz.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma copy_iovecs_accesses_nolazy : forall L mp k (a0 : word),
  (bv_unsigned a0 + 16 * Z.of_nat k < 2 ^ 64)%Z ->
  nolazy_rng L a0 (16 * Z.of_nat k) ->
  acc_nolazy L (copy_iovecs_accesses mp a0 k).
Proof.
  intros L mp k. induction k as [|k IH]; intros a0 Hw Hnl; cbn [copy_iovecs_accesses]; [apply acc_nolazy_nil|].
  apply acc_nolazy_cons.
  - intros j Hj. apply Hnl. lia.
  - destruct (read_iovec_entry mp a0); try apply acc_nolazy_nil.
    assert (Hu : bv_unsigned (a0 + 16) = (bv_unsigned a0 + 16)%Z).
    { rewrite bv_add_unsigned. change (bv_unsigned (16 : word)) with 16%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (u64_range a0). apply Z.mod_small. lia. }
    apply IH; [rewrite Hu; lia|].
    intros j Hj. rewrite Hu. replace (bv_unsigned a0 + 16 + j)%Z with (bv_unsigned a0 + (16 + j))%Z by ring. apply Hnl. lia.
Qed.

Lemma import_iovecs_accesses_nolazy : forall L mp (iov : word) (cnt : nat),
  (bv_unsigned iov + 16 * Z.of_nat cnt <= TASK_SIZE)%Z -> (cnt <= 1024)%nat ->
  nolazy_rng L iov (16 * Z.of_nat cnt) ->
  acc_nolazy L (import_iovecs_accesses mp iov (Z_to_bv 64 (Z.of_nat cnt))).
Proof.
  intros L mp iov cnt Hts Hc Hnl. unfold import_iovecs_accesses.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat cnt)) = cnt).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !u64_lit in E1 by lia.
    destruct (negb (access_okb iov 16)); [apply acc_nolazy_nil|].
    apply (acc_nolazy_one L iov 16%nat (16 * Z.of_nat cnt) Hnl). lia.
  - destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 0)); [apply acc_nolazy_nil|].
    destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat cnt)))%Z; [apply acc_nolazy_nil|].
    destruct (negb (access_okb iov (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat cnt))))); [apply acc_nolazy_nil|].
    rewrite Hwn. apply copy_iovecs_accesses_nolazy; [unfold TASK_SIZE in Hts; lia | exact Hnl].
Qed.

Lemma iov_prefix_accesses_nolazy : forall L iovs left,
  Forall (fun bn => nolazy_rng L (fst bn) (bv_unsigned (snd bn))) iovs ->
  acc_nolazy L (iov_prefix_accesses iovs left).
Proof.
  intros L iovs. induction iovs as [|[b n] r IH]; intros left HF.
  - destruct left; apply acc_nolazy_nil.
  - inversion HF as [|x l Hb Hr]; subst. cbn [fst snd] in Hb.
    destruct left as [|l']; [apply acc_nolazy_nil|]. cbn [iov_prefix_accesses].
    destruct (Nat.eqb (word_to_nat_bounded n (S l')) 0); [apply IH; exact Hr|].
    apply acc_nolazy_cons; [|apply IH; exact Hr].
    apply (nolazy_rng_sub L b (bv_unsigned n) _ Hb).
    rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pending_lz : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  nolazy_rng (m_vm_lazy model) iov (16 * Z.of_nat (length iovs)) ->
  Forall (fun bn => nolazy_rng (m_vm_lazy model) (fst bn) (bv_unsigned (snd bn))) iovs ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  srealizes segs scfg (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Hnl1 Hnl2 bs
         Ht1 Ht30 Hk.
  destruct (writev_checkX segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (HnlA : forall k, acc_nolazy (m_vm_lazy model) (CA ++ iov_prefix_accesses iovs k)).
  { intros k. apply acc_nolazy_app; [apply import_iovecs_accesses_nolazy; [exact Hiok | lia | exact Hnl1] | apply iov_prefix_accesses_nolazy; exact Hnl2]. }
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Eacc : forall i, syscall_effect_accesses (effs i) = CA ++ iov_prefix_accesses iovs (proj1_sig i)).
  { intros i. unfold effs, syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. apply app_nil_r. }
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | exact Hh | rewrite Eacc; apply HnlA].
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite Eacc, (mat_id_of_nolazy _ _ (HnlA _)) in Hmat. injection Hmat as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite Eacc, (mat_id_of_nolazy _ _ (HnlA _)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 32 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) -> nolazy_rng (m_vm_lazy model) b2 (bv_unsigned n2) ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Nl0 Nl1 Nl2 Ht1 Ht30 Hk.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_lz (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption |
    | change (16 * Z.of_nat (length [(b1, n1); (b2, n2)]))%Z with 32%Z; exact Nl0
    | repeat constructor; assumption
    | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 16 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Nl0 Nl1 Ht1 Ht30 Hk.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_lz (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] |
    | change (16 * Z.of_nat (length [(b1, n1)]))%Z with 16%Z; exact Nl0
    | repeat constructor; assumption
    | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_wall_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 32 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) -> nolazy_rng (m_vm_lazy model) b2 (bv_unsigned n2) ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Nl0 Nl1 Nl2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2_lz regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 16 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Nl0 Nl1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1_lz regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_ch_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 32 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) -> nolazy_rng (m_vm_lazy model) b2 (bv_unsigned n2) ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_write_ch (Z_to_bv 64 fd) (bs1 ++ bs2) K).
Proof.
  intros. unfold t_write_ch.
  eapply (rz_writev2_lz regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_writev1_zero_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 16 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Nl0 Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
  eapply (rz_ret_only_copyins_silent_lz ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | apply (acc_nolazy_one _ _ _ 16 Nl0); lia | unfold ms; rewrite adv_set_epend; exact Hc].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si, Himp, Hacc.
  (* [comment removed for export] *)
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_exit_at_lz : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma rz_exit_at_lit_lz : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at_lz; eassumption.
Qed.

End WithSegs.
End FPX_1.
