(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim
  AsanAcct LazyFrame MmapSim RefNodes NoReserve AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50%Z.  Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma mmap_flags_core_100022 : mmap_flags_core (Z_to_bv 64 1048610) = 1048610%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_100032 : mmap_flags_core (Z_to_bv 64 1048626) = 1048626%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_104022 : mmap_flags_core (Z_to_bv 64 1064994) = 1048610%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_104032 : mmap_flags_core (Z_to_bv 64 1065010) = 1048626%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_100022 : mmap_noreserve_b (Z_to_bv 64 1048610) = false. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_100032 : mmap_noreserve_b (Z_to_bv 64 1048626) = false. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104032 : mmap_noreserve_b (Z_to_bv 64 1065010) = true. Proof. vm_compute. reflexivity. Qed.

Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_lazy : forall flags a n m,
  mmap_noreserve_b flags = true -> with_mmap_backing flags a n m = vm_add_lazy a n m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_fs : forall flags a n m,
  m_fs (with_mmap_backing flags a n m) = m_fs m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_vmmaps : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

(* [comment removed for export] *)
Lemma region_free_not_contains : forall l (lo n : word),
  (0 < bv_unsigned n)%Z ->
  region_free l lo n = true -> map_contains l lo n = false.
Proof.
  intros l lo n Hn Hfree. unfold map_contains.
  apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
  cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (2 ^ 64 - 12).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)

Definition mat_id (m : Model) (accs : list (word * nat)) : Prop :=
  materialize_model_accesses m accs = Some m.

(* [comment removed for export] *)
Lemma mat_id_of_outside : forall m accs,
  accesses_outside_lazy accs (m_vm_lazy m) -> mat_id m accs.
Proof. intros m accs H. exact (materialize_model_accesses_disjoint m accs H). Qed.

(* [comment removed for export] *)
Lemma mat_id_nil : forall m, mat_id m [].
Proof. intros m. exact (materialize_model_accesses_nil m). Qed.

Lemma mat_id_app_nil : forall m accs, mat_id m accs -> mat_id m (accs ++ []).
Proof. intros m accs H. rewrite app_nil_r. exact H. Qed.

(* [comment removed for export] *)
Lemma materialize_with_fds : forall fds m accs,
  materialize_model_accesses (with_fds fds m) accs
  = option_map (with_fds fds) (materialize_model_accesses m accs).
Proof.
  intros fds m accs. unfold materialize_model_accesses.
  destruct m as [fd [maps lazy mat] io fsys proc lim tm].
  unfold with_fds, with_vm_backing, vm_backing_used. cbn -[materialize_accesses live_bytes maps_subtract_all vm_backed_maps].
  destruct (materialize_accesses lazy mat _ _ accs); reflexivity.
Qed.

Lemma mat_id_with_fds : forall fds m accs, mat_id m accs -> mat_id (with_fds fds m) accs.
Proof.
  intros fds m accs H. unfold mat_id in *. rewrite materialize_with_fds, H. reflexivity.
Qed.

Section Generic.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
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

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  apply node_ok_of_u; [CfgStep.kit_pending_on |]. split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_mat_u : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  CfgStep.node_ok_u segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc. split.
  - intros i. apply (sstep_syscall segs ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (Hh' i).
    + rewrite (Hacc i). apply materialize_model_accesses_nil.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hacc i), materialize_model_accesses_nil in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  CfgStep.alloc_no_b (bv_unsigned x8) = false ->   (* [comment removed for export] *)
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hna Hok Hinv Hnu Hh' Hacc.
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 _ Hsvc eq_refl Hna) |].
  apply (node_chk_ev_mat_u ms model x8 I effs ms' evs); assumption.
Qed.

(* [comment removed for export] *)
Lemma node_chk_mat_grants : forall ms model x8 (IA IB : Type)
    (effs : IA + IB -> SyscallEffect) (ms' : IA + IB -> Model) (b0 : IB),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  CfgStep.alloc_no_b (bv_unsigned x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall a, refusal_b (sys_input segs ms x8) model (eff_ret (effs (inl a))) = true) ->
  (forall b, refusal_b (sys_input segs ms x8) model (eff_ret (effs (inr b))) = false) ->
  ShapeAlg.node_ok segs (mkCfg ms model) IB (fun _ => [])
          (fun b => mkCfg (advance_past_svc (apply_effect ms (effs (inr b)))) (ms' (inr b))).
Proof.
  intros ms model x8 IA IB effs ms' b0 Hh Hsvc Hal Hok Hinv Hnu Hh' Hacc HA HB.
  apply (node_ok_grants_r segs (mkCfg ms model) IA IB (fun _ => [])
           (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) b0).
  - exact (CfgStep.kit_pending_off_sysno segs ms model x8 _ Hsvc eq_refl Hal).
  - apply (node_chk_ev_mat_u ms model x8 (IA + IB) effs ms' (fun _ => [])); assumption.
  - intros a. rewrite (CfgStep.child_refusal_b_syscall segs ms model x8 _ _ Hsvc (Hh' (inl a))). apply HA.
  - intros b. rewrite (CfgStep.child_refusal_b_syscall segs ms model x8 _ _ Hsvc (Hh' (inr b))). apply HB.
  - cbn [cfg_model]. apply Hh'.
Qed.

(* [comment removed for export] *)
Lemma node_chk_mat_sub : forall ms model x8 (I J : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (f : J -> I) (j0 : J),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  CfgStep.alloc_no_b (bv_unsigned x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall j, refusal_b (sys_input segs ms x8) model (eff_ret (effs (f j))) = false) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false -> exists j, f j = i) ->
  ShapeAlg.node_ok segs (mkCfg ms model) J (fun _ => [])
          (fun j => mkCfg (advance_past_svc (apply_effect ms (effs (f j)))) (ms' (f j))).
Proof.
  intros ms model x8 I J effs ms' f j0 Hh Hsvc Hal Hok Hinv Hnu Hh' Hacc Hkeep Hsurj.
  apply (node_ok_sub segs (mkCfg ms model) I J (fun _ => [])
           (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) f j0).
  - apply (node_chk_ev_mat_u ms model x8 I effs ms' (fun _ => [])); assumption.
  - exact (CfgStep.kit_pending_off_sysno segs ms model x8 _ Hsvc eq_refl Hal).
  - intros j. rewrite (CfgStep.child_refusal_b_syscall segs ms model x8 _ _ Hsvc (Hh' (f j))). apply Hkeep.
  - cbn [cfg_model]. apply Hh'.
  - intros i Hi. rewrite (CfgStep.child_refusal_b_syscall segs ms model x8 _ _ Hsvc (Hh' i)) in Hi.
    destruct (Hsurj i Hi) as (j & <-). exists j. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_chk_mat_forced : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hacc Hall.
  apply node_ok_forced.
  - apply (node_chk_ev_mat_u ms model x8 I effs ms' (fun _ => [])); assumption.
  - intros i. cbn [cfg_model]. apply Hh'.
  - intros i. rewrite (CfgStep.child_refusal_b_syscall segs ms model x8 _ _ Hsvc (Hh' i)). apply Hall.
Qed.

(* [comment removed for export] *)
Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

End Generic.
