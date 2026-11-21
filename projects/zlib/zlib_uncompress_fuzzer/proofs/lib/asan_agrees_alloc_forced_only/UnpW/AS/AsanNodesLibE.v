(* TRIAL NOT-OFFICIAL: AS/AsanNodesLibE = our text + 's own edits to theories/Common/AsanNodesLibE.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.FO.P04 Require Import Mmap Mprotect.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore FOStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra NodesFO.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS Require Import AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanCeil.  (* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* The lazy-syscall node over the filtered step (AS.NodesFO.node_chk_fo): the successors must not be spurious
   refusals ([Hns]); the converse needs no filter here since it covers every checked outcome. *)
Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hacc.
  apply (node_chk_fo segs ms model x8 I effs ms' evs Hh Hsvc Hok Hns).
  - intros eff m' ev Hc _. exact (Hinv eff m' ev Hc).
  - exact Hnu.
  - intros eff m' ev Hc. destruct (Hinv eff m' ev Hc) as (i & _ & -> & _). apply Hh'.
  - exact Hacc.
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall i, ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hns Hinv Hnu Hh' Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok Hns); auto.
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff0 ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hns0 Hh Hsvc Hchk Hnu Hh0 Hacc.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros []. exact Hns0.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hacc.
Qed.

Lemma rz_det_noacc : forall ms model x8 eff0 m0 T,
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff0 ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hns0 Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply rz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff0 ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hns0 Hh Hsvc Hchk Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) (T i)) ->
  srealizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma with_vm_backing_halted : forall l p m, m_halted (with_vm_backing l p m) = m_halted m.
Proof. reflexivity. Qed.

Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_replacement_halted : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
  apply vm_forget_range_halted.
Qed.

Lemma with_mmap_destroyed_halted : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. unfold with_mmap_destroyed. rewrite vm_forget_range_halted. apply with_vmmaps_halted. Qed.

Lemma forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
  intros. unfold brk_model, with_brk_next. cbv zeta.
  rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_cfg_instr segs alloc_forced_cfg ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma rz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
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

(* [comment removed for export] *)

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
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->  (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
  rewrite H0, Hpr in Hchk.
  (* a worker : munmap is an alloc-family arm with an ENOMEM refusal; the filtered step drops it
     (node_chk_fo_w), so the success outcome is the only successor. *)
  assert (Hne : errno_ret_in munmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  eapply (srz_silent1 segs _
            (mkCfg (advance_past_svc (apply_effect ms
                      (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])))
                   (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)));
    [| unfold ms; rewrite adv_unmaps1_epend; exact Hc].
  apply (node_chk_fo_w segs ms model (getr regs 17) unit
           (fun _ => mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
           (fun _ => munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model) (fun _ => []) tt).
  - exact Hh.
  - reflexivity.
  - exact (munmap_family_off segs ms (getr regs 17) Hno).
  - intros []. rewrite Hchk. cbv beta iota. rewrite Hne. unfold w_is0. rewrite bv_eqb_refl.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. unfold refusal_b. rewrite in_sysno_sys_input, Hno. cbn -[munmap_errnos]. exact Hne.
  - intros eff m' evs Hck Hnr. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    cbv beta iota in Hck.
    destruct (errno_ret_in munmap_errnos r) eqn:Er.
    + exfalso. unfold refusal_b in Hnr. rewrite in_sysno_sys_input, Hno in Hnr. cbn -[munmap_errnos] in Hnr.
      change (errno_ret_in munmap_errnos r = false) in Hnr. congruence.
    + destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. exists tt. repeat split; reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    cbv beta iota in Hck.
    destruct (errno_ret_in munmap_errnos r); [destruct us; discriminate|].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - intros eff m' evs Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    cbv beta iota in Hck.
    destruct (errno_ret_in munmap_errnos r).
    + destruct us; [|discriminate]. injection Hck as <- _. exact Hh.
    + destruct (w_is0 r && listNN_eqb us _)%bool; [|discriminate]. injection Hck as <- _.
      rewrite munmap_model_halted. exact Hh.
  - intros []. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* A brk successor at the filtered step: a resolution the spec allows that is not a spurious refusal. *)
Definition brk_ok_ns (ms : machine_state) (model : Model) (x8 r : word) : Prop :=
  brk_resolution_ok model (ms_gpr ms 0) r /\
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model
      (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                 (brk_unmaps r (vm_brk (m_vmmaps model))) [] []).

(* With a single allowed resolution nothing is spurious: no other answer is a non-refusal. *)
Lemma brk_single_not_spurious : forall ms model x8 b eff,
  bv_unsigned x8 = 214%Z ->
  (forall r, brk_resolution_ok model (ms_gpr ms 0) r -> r = b) ->
  eff_ret eff = b ->
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff.
Proof.
  intros ms model x8 b eff Hno Hone Hr (_ & Href & (eff' & m' & evs' & Hs' & Hn')).
  apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hs' as (_ & _ & Hok' & _).
  rewrite (Hone _ Hok'), <- Hr in Hn'. congruence.
Qed.

Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_ok_ns ms model x8 r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_fo segs ms model x8 {r : word | brk_ok_ns ms model x8 r}
           (fun i => mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) (fun _ => []) Hh Hsvc).
  - intros [r [Hr Hr']]. cbn [proj1_sig]. apply check_syscall_ok_iff.
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r [Hr Hn]]. exact Hn.
  - intros eff m' evs Hc Hn. apply check_syscall_ok_iff in Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
    assert (Hn' : brk_ok_ns ms model x8 (eff_ret eff)) by (split; [exact Hok | rewrite <- Heff; exact Hn]).
    exists (exist _ (eff_ret eff) Hn'). cbn [proj1_sig]. rewrite <- Heff. repeat split; reflexivity.
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (_ & -> & _ & ->).
    rewrite brk_model_halted. exact Hh.
  - intros [r Hr]. reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_ok_ns ms model (getr regs 17) (vm_brk (m_vmmaps model))).
  { split; [apply Hcases; reflexivity |].
    eapply brk_single_not_spurious; [exact Hno | exact (fun r Hr => proj1 (Hcases r) Hr) | reflexivity]. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_ok_ns ms model (getr regs 17) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hq) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hr']]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* A grow the model can serve: the old break is then a spurious refusal, so only the grow is a successor. *)
Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  assert (Hg : brk_ok_ns ms model (getr regs 17) req).
  { split; [exact Hgrow |]. apply spurious_refusal_not_refusal. cbn [eff_ret].
    rewrite (refusal_b_brk_fo segs ms model _ _ Hno). apply brk_ne_refusal_fo. exact Hneq. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_ok_ns ms model (getr regs 17) r} => KB)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hg); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hg) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hrn]]. cbn [proj1_sig]. fold h.
  destruct (proj1 (Hcases r) Hr) as [-> | [-> _]].
  - exfalso. apply Hrn. apply (spurious_of_witness _ _ _
      (mkEffectU req [] (brk_zeros (ms_gpr ms 0) req (vm_brk (m_vmmaps model)))
                 (brk_unmaps req (vm_brk (m_vmmaps model))) [] [])
      (brk_model (ms_gpr ms 0) req model) []).
    + exact (family_off_fo segs ms _ 214 Hno in_alloc_brk).
    + cbn [eff_ret]. rewrite (refusal_b_brk_fo segs ms model _ _ Hno), H0.
      exact (brk_keep_refusal_fo model req Hreq0 ltac:(rewrite Hureq; exact Hs) Hneq).
    + exact (brk_ok_intro segs ms _ model req Hno Hgrow).
    + cbn [eff_ret]. rewrite (refusal_b_brk_fo segs ms model _ _ Hno). apply brk_ne_refusal_fo. exact Hneq.
  - assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_brk_grow_lazy_same : forall regs (pc : word) mem rom model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) K ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w d K HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB.
  exact (srz_brk_grow_lazy regs pc mem rom model w d K HF HE Hh H17 Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB).
Qed.

Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_ok_ns ms model (getr regs 17) b).
  { split; [apply Hcases; reflexivity |].
    eapply brk_single_not_spurious; [exact Hno | exact (fun r Hr => proj1 (Hcases r) Hr) | reflexivity]. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_ok_ns ms model (getr regs 17) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hr']]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  apply (node_chk_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
  - intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - intros i. apply no_spurious_sysno. rewrite Hno. apply not_alloc_sysno. lia.
  - intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
  - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
  - intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
  - intros [t Ht]. reflexivity.
Qed.

Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

Lemma srz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx ->
  srealizes segs (nx T1) A -> srealizes segs (nx T2) B -> srealizes segs (nx T3) C ->
  srealizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (srz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (srz_cases c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* Case on every boolean test left in the goal (never on a constructor), reducing after each. *)
Local Ltac split_ifs :=
  repeat (match goal with |- context [if ?b then _ else _] =>
            lazymatch b with true => fail | false => fail | _ => destruct b eqn:? end end; cbn [eff_ret]).

(* The fixed-in mmap check at the release spec: beside the grant it offers the errnos, with the range
   preserved or destroyed. *)
Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = if Z.eqb prot 0 then
      match eff with
      | mkEffectU r [] [] us [] [] =>
          if errno_ret_in mmap_errnos r
          then match us with
               | [] => CheckOk model []
               | _ => if listNN_eqb us [(addr, n)]
                      then CheckOk (with_mmap_destroyed addr n
                                      (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []
                      else CheckReject
               end
          else if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (fixedin_ok_model prot flags addr n model) []
          else CheckReject
      | _ => CheckReject
      end
    else
      match eff with
      | mkEffectU r [] zs us [] [] =>
          if errno_ret_in mmap_errnos r
          then match zs with
               | _ :: _ => CheckReject
               | [] => match us with
                       | [] => CheckOk model []
                       | _ => if listNN_eqb us [(addr, n)]
                              then CheckOk (with_mmap_destroyed addr n
                                              (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []
                              else CheckReject
                       end
               end
          else match us with
               | _ :: _ => CheckReject
               | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_budget_ok flags model addr n
                       then CheckOk (fixedin_ok_model prot flags addr n model) []
                       else CheckReject
               end
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc.
  pose proof (alloc_top_lt (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    reflexivity.
  - rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    reflexivity.
Qed.

(* Every checked fixed-in outcome is an errno (model kept or range destroyed, still running) or the grant. *)
Lemma mmap_fixedin_cases : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z) m' evs,
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  (errno_ret_in mmap_errnos (eff_ret eff) = true /\ m_halted m' = m_halted model)
  \/ (eff = fixedin_ok_eff prot addr n /\ m' = fixedin_ok_model prot flags addr n model /\ evs = []).
Proof.
  intros ms x8 model eff prot flags addr len m' evs Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc.
  rewrite (mmap_fixedin_check ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop Hrf Hmc).
  fold n. destruct eff as [r ws zs us cs ci]. cbn [eff_ret].
  destruct (Z.eqb prot 0) eqn:Ep, ws, zs, us, cs, ci; cbn [eff_ret]; split_ifs;
    intros Hc; try discriminate Hc; injection Hc as <- <-;
    first [ left; split; [reflexivity | first [reflexivity | apply with_mmap_destroyed_halted']]
          | right;
            repeat match goal with
                   | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
                   | H : bv_eqb _ _ = true |- _ => apply bv_eqb_eq in H
                   | H : listNN_eqb _ _ = true |- _ => apply listNN_eqb_eq in H
                   | H : _ :: _ = _ :: _ |- _ => injection H as ? ?
                   | H : [] = _ :: _ |- _ => discriminate H
                   | H : _ :: _ = [] |- _ => discriminate H
                   end;
            subst; unfold fixedin_ok_eff; rewrite Ep; repeat split; reflexivity ].
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_lt (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  assert (G0 : ms_gpr ms 0 = addr) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = Z_to_bv 64 len) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 prot) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  assert (G3 : ms_gpr ms 3 = flags) by (unfold ms; rewrite ms_gpr_epend3; exact H13).
  assert (G4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) by (unfold ms; rewrite ms_gpr_epend4; exact H14).
  assert (G5 : ms_gpr ms 5 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend5; exact H15).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           G0 Hal Hpos G1 Hlen G2 G3 G4 G5 Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  pose proof (fun eff m' evs => mmap_fixedin_cases ms (getr regs 17) model eff prot flags addr len m' evs Hno Hprot
                                  Hcore G0 Hal Hpos G1 Hlen G2 G3 G4 G5 Htop Hrf Hmc) as Hcases.
  cbv zeta in Hcases. fold n in Hcases.
  assert (Ea : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity |].
    pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  assert (Hok0 : check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
                 = CheckOk (fixedin_ok_model prot flags addr n model) []).
  { rewrite Hchk. unfold fixedin_ok_eff. destruct Hprot as [-> | ->]; cbn [Z.eqb].
    - rewrite Ea, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    - rewrite Ea, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), (Hbud eq_refl). reflexivity. }
  assert (Hnr0 : refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (fixedin_ok_eff prot addr n)) = false).
  { rewrite (refusal_b_mmap_fo segs ms model _ _ Hno). unfold fixedin_ok_eff. destruct (Z.eqb prot 0); exact Ea. }
  apply (srz_det_fo segs ms model (getr regs 17) (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model)
           KB Hh eq_refl Hok0).
  - exact (spurious_refusal_not_refusal _ _ _ _ Hnr0).
  - intros eff m' evs Hc Hn. destruct (Hcases eff m' evs Hc) as [[Er _] | Hg]; [| exact Hg].
    exfalso. apply Hn.
    apply (spurious_of_witness _ _ _ (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) []).
    + exact (family_off_fo segs ms _ 222 Hno in_alloc_mmap).
    + rewrite (refusal_b_mmap_fo segs ms model _ _ Hno). exact Er.
    + apply check_syscall_ok_iff. exact Hok0.
    + exact Hnr0.
  - intros eff Hc. rewrite Hchk in Hc. revert Hc.
    destruct eff as [r ws zs us cs ci].
    destruct (Z.eqb prot 0), ws, zs, us, cs, ci; cbn [eff_ret]; split_ifs; intros Hc; discriminate Hc.
  - intros eff m' evs Hc. destruct (Hcases eff m' evs Hc) as [[_ ->] | (_ & -> & _)]; [exact Hh |].
    unfold fixedin_ok_model. rewrite with_mmap_replacement_halted', with_vmmaps_halted. exact Hh.
  - unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2 AX2S AP APS.

(* [comment removed for export] *)
Lemma is_ecall_at_sound : forall SEGS cs,
  is_ecall_at SEGS cs = true ->
  0 <= pc cs /\ pc cs + 4 < two64 /\
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  repeat split; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
  v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma cs_ok_refuse : forall E cs R FULL model,
  cs_ok E cs R FULL model ->
  cs_ok E (refuse cs) (regupd R 10 (Z_to_bv 64 ENOMEM_RET)) FULL model.
Proof.
  intros E cs R FULL model HC.
  assert (HMr : Mr A argH E (refuse cs) model FULL = Mr A argH E cs model FULL) by reflexivity.
  assert (HA : allowA A E (refuse cs) = allowA A E cs) by reflexivity.
  destruct HC; constructor; unfold refuse, set_pc, set_reg, with_ss, mk_ss in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  apply regs_ok_set_n; [exact co_regs0 | lia | rewrite edenot_lit; reflexivity].
Qed.

Lemma pc_refuse : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.
Lemma nxt_refuse : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.
End CsOk.
