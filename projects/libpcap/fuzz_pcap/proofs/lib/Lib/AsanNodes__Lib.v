(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the lemma srz_mmap_noreplace_occupied, which no proof used and which built an srz_spin, is removed, because srz_spin now takes a proof of False (lib/Common/SpinAlg.v). *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StreamSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk MmapSim AllocSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesMmB AsanNodesLibE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanNodes.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StreamSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require BackingAlgebra. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesMmLib AsanNodesMmB AsanNodesLibE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.StreamExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StreamSim__Common.StreamSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.FileSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.ShapeNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesFs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance asannodes_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma MInv_same_vm : forall A m m',
  m_vmmaps m' = m_vmmaps m -> m_vm_lazy m' = m_vm_lazy m -> m_vm_materialized m' = m_vm_materialized m ->
  MInv A m -> MInv A m'.
Proof.
  intros A m m' Hv Hl Hm HM. eapply MInv_transport; [exact HM | exact Hm | exact Hl |].
  unfold eager_used. rewrite Hv, Hl. apply HM.
Qed.

Lemma lazy_cover_same : forall H A m m',
  m_vm_lazy m' = m_vm_lazy m -> lazy_cover H (m_vm_lazy m) A -> lazy_cover H (m_vm_lazy m') A.
Proof. intros H A m m' -> HL. exact HL. Qed.

(* [comment removed for export] *)
Lemma lazy_cover_pages_sub : forall H A (l l' : list (word * word)),
  (forall p, page_in_ranges p l' = true -> page_in_ranges p l = true) ->
  lazy_cover H l A -> lazy_cover H l' A.
Proof. intros H A l l' Hsub HL w Hp Hw. apply HL; [apply Hsub; exact Hp | exact Hw]. Qed.

Lemma with_fds_vmmaps : forall t m, m_vmmaps (with_fds t m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma with_fds_lazy : forall t m, m_vm_lazy (with_fds t m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma with_fds_materialized : forall t m, m_vm_materialized (with_fds t m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma with_fds_halted : forall t m, m_halted (with_fds t m) = m_halted m. Proof. reflexivity. Qed.

Lemma MInv_with_fds : forall A t m, MInv A m -> MInv A (with_fds t m).
Proof. intros A t m HM. apply (MInv_same_vm A m); [reflexivity | reflexivity | reflexivity | exact HM]. Qed.

Lemma ranges_avoid_single : forall H a n, range_avoids H a n -> ranges_avoid H [(a, n)].
Proof. intros H a n Hr. apply ranges_avoid_cons; [exact Hr | apply ranges_avoid_nil]. Qed.

(* [comment removed for export] *)
Lemma range_avoids_prefix : forall H a n m, (m <= n)%nat -> range_avoids H a n -> range_avoids H a m.
Proof. intros H a n m Hle Hr k Hk. apply Hr. lia. Qed.

Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
Hypothesis HA : A_wf A.
Let ROM := seg_rom segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="HA"] Theorem node_chk_A : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (M i)) A) ->
  (forall i, MInv A (M i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (E i))) ->
  (forall i, MInv A (materialized_succ (M i) (syscall_effect_accesses (E i)))
          /\ same_but_materialized (M i) (materialized_succ (M i) (syscall_effect_accesses (E i))))
  /\ node_ok segs (mkCfg ms model) I EV
       (fun i => mkCfg (advance_past_svc (apply_effect ms (E i)))
                       (materialized_succ (M i) (syscall_effect_accesses (E i)))).
Proof.
  intros ms model x8 chk I E M EV Hh Hsvc Hchk Hok Hinv Hnu Hnh Hcov HM Hav.
  apply (node_syscall_restricted segs H A ms model x8 I E M EV HA Hh Hsvc).
  - intros i. apply check_syscall_ok_iff. rewrite Hchk. apply Hok.
  - intros [eff m' evs|] Hs.
    + apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
      destruct (Hinv eff m' evs Hs) as (i & -> & -> & ->). exists i. reflexivity.
    + exfalso. apply (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] []) _) in Hs.
      rewrite Hchk in Hs. exact (Hnu _ Hs).
  - exact Hnh.
  - exact Hcov.
  - exact HM.
  - exact Hav.
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_sys_chk_A : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event) (T : I -> TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (M i)) A) ->
  (forall i, MInv A (M i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (E i))) ->
  (forall i mdl', MInv A mdl' -> same_but_materialized (M i) mdl' ->
     srealizes segs (mkCfg (advance_past_svc (apply_effect ms (E i))) mdl') (T i)) ->
  srealizes segs (mkCfg ms model) (t_alt (fun i => t_emit (EV i) (T i))).
Proof.
  intros ms model x8 chk I E M EV T i0 Hh Hsvc Hal Hchk Hok Hinv Hnu Hnh Hcov HM Hav Hcont.
  destruct (node_chk_A ms model x8 chk I E M EV Hh Hsvc Hchk Hok Hinv Hnu Hnh Hcov HM Hav) as [Hmat Hnode].
  apply (srz_node segs (mkCfg ms model) I EV _ T i0 (cnode_lift segs _ _ _ _ (unfiltered_sysno ms model x8 Hsvc Hal) Hnode)).
  intros i. destruct (Hmat i) as [HMi HSi]. exact (Hcont i _ HMi HSi).
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_sys_chk_const_A : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (T : TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) []) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = []) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (M i)) A) ->
  (forall i, MInv A (M i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (E i))) ->
  (forall i mdl', MInv A mdl' -> same_but_materialized (M i) mdl' ->
     srealizes segs (mkCfg (advance_past_svc (apply_effect ms (E i))) mdl') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 chk I E M T i0 Hh Hsvc Hal Hchk Hok Hinv Hnu Hnh Hcov HM Hav Hcont.
  destruct (node_chk_A ms model x8 chk I E M (fun _ => []) Hh Hsvc Hchk Hok Hinv Hnu Hnh Hcov HM Hav) as [Hmat Hnode].
  assert (HT : T []).
  { destruct (Hmat i0) as [HMi HSi]. eapply srealizes_nonempty. exact (Hcont i0 _ HMi HSi). }
  eapply srz_conseq.
  - apply (srz_node segs (mkCfg ms model) I (fun _ => []) _ (fun _ => T) i0
             (cnode_lift segs _ _ _ _ (unfiltered_sysno ms model x8 Hsvc Hal) Hnode)).
    intros i. destruct (Hmat i) as [HMi HSi]. exact (Hcont i _ HMi HSi).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
    + intro Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Htr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_ret_chk_A : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hcont.
  assert (HT : T []) by (eapply srealizes_nonempty; exact Hcont).
  eapply srz_conseq.
  - apply (srz_node segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m')
             (fun _ => T) tt).
    + apply cnode_lift_unit.
      apply (node_chk_ev_noacc segs ms model x8 unit (fun _ => mkEffect r [] []) (fun _ => m') (fun _ => []) Hh Hsvc).
      * intros []. rewrite Hchk. apply check_ret_only_ok_iff. auto.
      * intros eff m2 evs2 Hc. rewrite Hchk in Hc. apply check_ret_only_ok_iff in Hc.
        destruct Hc as (-> & -> & ->). exists tt. auto.
      * intros eff Hc. rewrite Hchk in Hc. exact (check_ret_only_no_unmodeled _ _ _ _ Hc).
      * intros []. exact Hh'.
      * intros []. reflexivity.
    + intros []. exact Hcont.
  - intro tr. split.
    + intros [[] Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
    + intro Htr. exists tt. exact (proj2 (t_emit_nil_eq T HT tr) Htr).
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_ret_copyins_A : forall ms model x8 reads r T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only_copyins reads eff r model []) ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  ranges_avoid H reads ->
  (forall mdl', MInv A mdl' -> same_but_materialized model mdl' ->
     srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) mdl') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r T Hh Hsvc Hchk HL HM Hav Hcont.
  assert (Hacc : syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads).
  { unfold syscall_effect_accesses, with_copyins. cbn. apply app_nil_r. }
  assert (Happ : apply_effect ms (with_copyins reads (mkEffect r [] [])) = apply_effect ms (mkEffect r [] [])) by reflexivity.
  rewrite <- Happ in Hcont.
  destruct (node_chk_A ms model x8 (fun eff => check_ret_only_copyins reads eff r model []) unit
           (fun _ => with_copyins reads (mkEffect r [] [])) (fun _ => model) (fun _ => []) Hh Hsvc Hchk) as [Hmat Hnode].
  - intros []. apply check_ret_only_copyins_ok_iff. auto.
  - intros eff m2 evs2 Hc. apply check_ret_only_copyins_ok_iff in Hc. destruct Hc as (-> & -> & ->). exists tt. auto.
  - intros eff Hc. exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hc).
  - intros []. exact Hh.
  - intros []. exact HL.
  - intros []. exact HM.
  - intros []. rewrite Hacc. exact Hav.
  - destruct (Hmat tt) as [HM' HS'].
    eapply srz_silent1; [apply cnode_lift_unit; exact Hnode | exact (Hcont _ HM' HS')].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma srz_ecall_A : forall regs (pc : word) mem model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (ecall_st regs pc mem ROM) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) T.
Proof.
  intros regs pc mem model w T Hh HF HE Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  change (epend regs pc mem ROM (getr regs 17)) with (ecall_st regs pc mem ROM). exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_close_A : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem ROM)
                        (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hc.
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_chk_A; [exact Hh | reflexivity | eapply close_check; eassumption | cbn; exact Hh |].
  rewrite adv_ret_st. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_read_dir_A : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem ROM) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh H17 Hfd Hfd32 Hlk Hok Hc.
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_chk_A; [exact Hh | reflexivity | eapply read_dir_check; eassumption | cbn; exact Hh |].
  rewrite adv_ret_st. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_read_file_A : forall regs (pc : word) mem model w fd p off data cnt wit K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = cnt ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb (getr regs 11) (bv_unsigned cnt) = true ->
  read_bytes_map (wview segs mem) (getr regs 11) cnt = Some wit ->
  range_avoids H (getr regs 11) (Z.to_nat (bv_unsigned cnt)) ->
  (forall mdl', MInv A mdl' ->
     same_but_materialized
       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word (rd_bytes data off cnt)))) model) mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (len_word (rd_bytes data off cnt))) (v_addi pc 4)
                             (wbytes mem (getr regs 11) (rd_bytes data off cnt)) ROM) mdl') K) ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt wit K HF HE Hh HL HM H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw Hav Hc.
  destruct (read_file_chk_facts segs regs pc mem model fd p off data cnt wit H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw)
    as (Hok1 & Hinv & Hnu).
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  set (bs := rd_bytes data off cnt) in *.
  set (m1 := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model) in *.
  apply (srz_sys_chk_const_A (ecall_st regs pc mem ROM) model (getr regs 17) _ unit
           (fun _ => mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []) (fun _ => m1) K tt Hh eq_refl
           ltac:(cbn [ecall_st ms_svc_pending]; rewrite H17; reflexivity) (fun eff => eq_refl)).
  - intros []. exact Hok1.
  - intros eff m2 evs2 Hck. destruct (Hinv eff m2 evs2 Hck) as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []. cbn. exact Hh.
  - intros []. exact HL.
  - intros []. apply MInv_with_fds. exact HM.
  - intros []. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    assert (Hlen : (length bs <= Z.to_nat (bv_unsigned cnt))%nat).
    { unfold bs, rd_bytes. rewrite length_file_read. unfold word_to_nat. lia. }
    destruct bs as [|b bsr]; cbn [delivered_writes write_accesses].
    + apply ranges_avoid_nil.
    + apply ranges_avoid_single. eapply range_avoids_prefix; [exact Hlen | exact Hav].
  - intros [] mdl' HM' HS'. rewrite adv_delivered_st, write_to_mem_wbytes. exact (Hc mdl' HM' HS').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cstr_access_len_aux_le : forall mp a fuel, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp a fuel. revert a. induction fuel as [|fuel IH]; intros a; cbn; [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)). lia.
Qed.

#[using="Type"] Lemma open_copyins_avoid : forall regs pc mem,
  range_avoids H (getr regs 11) path_max -> ranges_avoid H (open_copyins (ecall_st regs pc mem ROM)).
Proof.
  intros regs pc mem Hav. unfold open_copyins. rewrite ecall_st_gpr1.
  apply ranges_avoid_single. eapply range_avoids_prefix; [apply cstr_access_len_aux_le | exact Hav].
Qed.

Local Notation "'path_at' mem a" := (read_cstr (mrb segs mem) a) (at level 10, mem at level 9, a at level 9, only parsing).

(* [comment removed for export] *)
#[using="HA"] Theorem srz_openat_toolong_A : forall regs (pc : word) mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  getr regs 17 = Z_to_bv 64 56 ->
  modeled_open_flags (getr regs 12) = true ->
  path_at mem (getr regs 11) = CstrTooLong ->
  range_avoids H (getr regs 11) path_max ->
  (forall mdl', MInv A mdl' -> same_but_materialized model mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem ROM) mdl') K) ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w K HF HE Hh HL HM H17 Hfl Hp Hav Hc.
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_copyins_A; [exact Hh | reflexivity | eapply openat_toolong_check'; eassumption | exact HL | exact HM
    | apply open_copyins_avoid; exact Hav |].
  intros mdl' HM' HS'. rewrite adv_ret_st. exact (Hc mdl' HM' HS').
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_openat_enoent_A : forall regs (pc : word) mem model w p K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  (path_eqb p [] = true \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  range_avoids H (getr regs 11) path_max ->
  (forall mdl', MInv A mdl' -> same_but_materialized model mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem ROM) mdl') K) ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w p K HF HE Hh HL HM H17 Hdirfd Hp Hfl Hcase Hav Hc.
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  eapply srz_ret_copyins_A; [exact Hh | reflexivity | eapply openat_enoent_check; eassumption | exact HL | exact HM
    | apply open_copyins_avoid; exact Hav |].
  intros mdl' HM' HS'. rewrite adv_ret_st. exact (Hc mdl' HM' HS').
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_open_A : forall ms model x8 reads (mk : word -> Model) TA TB,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vmmaps (mk fd) = m_vmmaps model /\ m_vm_lazy (mk fd) = m_vm_lazy model
              /\ m_vm_materialized (mk fd) = m_vm_materialized model) ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  ranges_avoid H reads ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e mdl', In e openat_errnos -> MInv A mdl' -> same_but_materialized model mdl' ->
     srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) mdl') TA) ->
  (forall mdl', MInv A mdl' -> same_but_materialized (mk (alloc_fd (m_fds model))) mdl' ->
     srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model)))) mdl') TB) ->
  srealizes segs (mkCfg ms model) (t_alt2 TA TB).
Proof.
  intros ms model x8 reads mk TA TB Hh Hsvc Hal Hchk Hmk Hvm HL HM Hav Hfree HA' HB'.
  set (I := ({e : Z | In e openat_errnos} + unit)%type).
  set (E := fun i : I => match i with
                         | inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
                         | inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []) end).
  set (M := fun i : I => match i with inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
  assert (Hacc : forall i, syscall_effect_accesses (E i) = reads).
  { intros [[e He]|[]]; unfold syscall_effect_accesses, with_copyins; cbn; apply app_nil_r. }
  assert (Happ : forall r, apply_effect ms (with_copyins reads (mkEffect r [] [])) = set_gpr0 ms r).
  { intros r. rewrite <- (apply_effect_no_write ms r). reflexivity. }
  destruct (node_chk_A ms model x8 (fun eff => check_open_result_copyins reads eff model mk) I E M (fun _ => [])
              Hh Hsvc Hchk) as [Hmat Hnode].
  - intros [[e He]|[]]; cbn [E M]; apply check_open_result_copyins_ok_iff.
    + left. exists e. auto.
    + right. exists (alloc_fd (m_fds model)). auto.
  - intros eff m' evs Hc. apply check_open_result_copyins_ok_iff in Hc.
    destruct Hc as [(e & He & -> & -> & ->) | (fd & Hlk & -> & -> & -> & ->)].
    + exists (inl (exist _ e He)). auto.
    + exists (inr tt). auto.
  - intros eff Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
  - intros [[e He]|[]]; cbn [M]; [exact Hh | apply Hmk].
  - intros [[e He]|[]]; cbn [M]; [exact HL |].
    destruct (Hvm (alloc_fd (m_fds model))) as (_ & Hl & _). rewrite Hl. exact HL.
  - intros [[e He]|[]]; cbn [M]; [exact HM |].
    destruct (Hvm (alloc_fd (m_fds model))) as (Hv & Hl & Hm).
    apply (MInv_same_vm A model); assumption.
  - intros i. rewrite Hacc. exact Hav.
  - apply (srz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit _ TA TB
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt
             (cnode_lift segs _ _ _ _ (unfiltered_sysno ms model x8 Hsvc Hal) Hnode)).
    + intros [e He]. destruct (Hmat (inl (exist _ e He))) as [HM' HS']. cbn [E M] in *.
      rewrite Happ. exact (HA' e _ He HM' HS').
    + intros []. destruct (Hmat (inr tt)) as [HM' HS']. cbn [E M] in *.
      rewrite Happ. exact (HB' _ HM' HS').
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_openat_file_A : forall regs (pc : word) mem model w p d TA TB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  range_avoids H (getr regs 11) path_max ->
  (forall e mdl', In e openat_errnos -> MInv A mdl' -> same_but_materialized model mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem ROM) mdl') TA) ->
  (forall mdl', MInv A mdl' -> same_but_materialized (open_file_model model p (alloc_fd (m_fds model))) mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem ROM) mdl') TB) ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) (t_alt2 TA TB).
Proof.
  intros regs pc mem model w p d TA TB HF HE Hh HL HM H17 Hdirfd Hp Hpe Hfl Hplain Hfs Hfree Hav HA' HB'.
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  eapply (srz_open_A (ecall_st regs pc mem ROM) model (getr regs 17) _ (open_file_model model p));
    [exact Hh | reflexivity | rewrite H17; reflexivity | eapply openat_file_check; eassumption
    | intros fd; cbn; exact Hh | intros fd; repeat split; reflexivity | exact HL | exact HM
    | apply open_copyins_avoid; exact Hav | exact Hfree
    | intros e mdl' He HM' HS'; rewrite adv_setgpr0_st; exact (HA' e mdl' He HM' HS')
    | intros mdl' HM' HS'; rewrite adv_setgpr0_st; exact (HB' mdl' HM' HS') ].
Qed.

(* [comment removed for export] *)
#[using="HA"] Theorem srz_openat_dir_A : forall regs (pc : word) mem model w p TA TB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  lazy_cover H (m_vm_lazy model) A -> MInv A model ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  path_is_dirref p = true ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  range_avoids H (getr regs 11) path_max ->
  (forall e mdl', In e openat_errnos -> MInv A mdl' -> same_but_materialized model mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem ROM) mdl') TA) ->
  (forall mdl', MInv A mdl' -> same_but_materialized (open_dir_model model (alloc_fd (m_fds model))) mdl' ->
     srealizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem ROM) mdl') TB) ->
  srealizes segs (mkCfg (mkst regs pc mem ROM) model) (t_alt2 TA TB).
Proof.
  intros regs pc mem model w p TA TB HF HE Hh HL HM H17 Hdirfd Hp Hfl Hdir Hfree Hav HA' HB'.
  eapply srz_ecall_A; [exact Hh | exact HF | exact HE |].
  eapply (srz_open_A (ecall_st regs pc mem ROM) model (getr regs 17) _ (open_dir_model model));
    [exact Hh | reflexivity | rewrite H17; reflexivity | eapply openat_dir_check; eassumption
    | intros fd; cbn; exact Hh | intros fd; repeat split; reflexivity | exact HL | exact HM
    | apply open_copyins_avoid; exact Hav | exact Hfree
    | intros e mdl' He HM' HS'; rewrite adv_setgpr0_st; exact (HA' e mdl' He HM' HS')
    | intros mdl' HM' HS'; rewrite adv_setgpr0_st; exact (HB' mdl' HM' HS') ].
Qed.

(* [comment removed for export] *)
Definition srz_exit_A := srz_exit_at_lazy segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_pin_not_errno : forall m a nZ, 0 <= nZ -> grant_ok_na_pin m a nZ = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros m a nZ HnZ Hg. destruct (grant_ok_na_pin_unpack m a nZ Hg) as (_ & _ & Htop & _).
  pose proof (alloc_top_room (m_vmmaps m)) as Hroom. unfold stack_max_size in Hroom.
  apply errno_ret_in_below; [reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_mmap_rw_pin : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) Hb0 HKB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check segs ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk. rewrite Hb0 in Hchk.
  assert (Hn0 : 0 <= nZ) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => with_mmap_backing flags a n (mmap_model a n model) end).
  apply (srz_prune segs ms model (getr regs 17) (unit + IB) effs ms'
           (fun i => match i with inl _ => false | inr _ => true end) (inr (exist _ a0 Ha0)) KB eq_refl
           ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk_ev_mat segs ms model (getr regs 17) (unit + IB) effs ms' (fun _ => []) Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
        destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | [a Ha]]; reflexivity.
  - intros [[] | [a Ha]] Hk; [discriminate Hk|]. cbn [effs]. rewrite (mmap_refusal_b segs _ _ _ _ Hno).
    exact (grant_pin_not_errno model a nZ Hn0 Ha).
  - intros [[] | [a Ha]] Hk; [|discriminate Hk]. cbn [effs]. rewrite (mmap_refusal_b segs _ _ _ _ Hno).
    exact (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos).
  - reflexivity.
  - intros [[] | [a Ha]] Hk; [discriminate Hk|]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HKB. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_mmap_rw_pin_nogrant : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall a, grant_ok_na_pin model a (page_round_up_Z len) && mmap_noreserve_backed_ok flags model (page_round_up_Z len) = false) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w len flags KA HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 Hng HKA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check segs ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk.
  eapply (srz_ret_chk_A ms model (getr regs 17) (errno_ret ENOMEM) model KA Hh eq_refl); [| exact Hh |].
  - intros [r ws zs us cs ci]. rewrite Hchk. unfold check_ret_only.
    destruct ws; [|reflexivity]. destruct zs.
    + destruct us; [|cbn; destruct (errno_ret_in mmap_errnos r); reflexivity].
      destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (mmap_errnos_ENOMEM e He), bv_eqb_refl. reflexivity.
      * rewrite Hng. destruct (bv_eqb r (errno_ret ENOMEM)) eqn:Eb; [|reflexivity].
        apply bv_eqb_eq in Eb. subst r. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos) in Er. discriminate.
    + destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
      destruct (errno_ret_in mmap_errnos r); [reflexivity|].
      destruct (grant_ok_na_pin model r (page_round_up_Z len) && mmap_noreserve_backed_ok flags model (page_round_up_Z len)) eqn:Hg.
      * rewrite Hng in Hg. discriminate.
      * cbn [andb]. reflexivity.
  - unfold ms. change (mkEffect (errno_ret ENOMEM) [] []) with (mkEffectU (errno_ret ENOMEM) [] [] [] [] []).
    rewrite adv_ret_epend. exact HKA.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fixedin_check_top : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222 ->
  (prot = 0 \/ prot = 3) ->
  mmap_flags_core flags = 50 ->
  ms_gpr ms 0 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
  ms_gpr ms 1 = Z_to_bv 64 len -> 0 < len ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model) ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3 -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs, us with
             | [], [] => CheckOk model []
             | [], _ => if listNN_eqb us [(addr, n)]
                        then CheckOk (fixedin_destroyed_model addr n model) []
                        else CheckReject
             | _, _ => CheckReject
             end
        else if (Z.eqb prot 0)
             then match zs with
                  | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
             else match us with
                  | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud.
  pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  assert (Hlen' : len < 2 ^ 64).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
    reflexivity.
  - (* [comment removed for export] *)
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_mmap_fixedin_top : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3) -> mmap_flags_core flags = 50 ->
  getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3 -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HKB.
  pose proof (u64_range addr) as Har. pose proof (alloc_top_room (m_vmmaps model)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : len < 2 ^ 64) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check_top ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Htop Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => fixedin_ok_eff prot addr n
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixedin_ok_model prot flags addr n model
                          | T3 => fixedin_destroyed_model addr n model end).
  assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
  assert (Hret2 : eff_ret (fixedin_ok_eff prot addr n) = addr)
    by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
  apply (srz_prune segs ms model (getr regs 17) three effs ms'
           (fun i => match i with T2 => true | _ => false end) T2 KB eq_refl ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk_noacc segs ms model (getr regs 17) three effs ms' Hh eq_refl).
    + intros [| |]; cbn [effs ms'].
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
      * rewrite Hchk. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (Herr e He).
        destruct zs; [|discriminate]. destruct us.
        -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
        -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
           apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
      * destruct (Z.eqb prot 0) eqn:Ep.
        -- destruct zs; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
        -- destruct us; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists T2. cbn [effs ms']. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh
                              | unfold fixedin_destroyed_model; rewrite with_mmap_destroyed_halted'; cbn; exact Hh].
    + intros [| |]; cbn [effs]; unfold fixedin_ok_eff; [reflexivity | destruct (Z.eqb prot 0); reflexivity | reflexivity].
  - intros [| |] Hk; try discriminate Hk. cbn [effs]. rewrite Hret2, (mmap_refusal_b segs _ _ _ _ Hno). exact Haddr_ne.
  - intros [| |] Hk; try discriminate Hk; cbn [effs]; rewrite (mmap_refusal_b segs _ _ _ _ Hno);
      exact (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos).
  - reflexivity.
  - intros [| |] Hk; try discriminate Hk. cbn [effs ms']. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HKB.
    + rewrite adv_zeros1_epend. exact HKB.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_mmap_fixedin_spin : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3) -> mmap_flags_core flags = 50 ->
  getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len ->
  bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3 -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof. exact srz_mmap_fixedin_top. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="HA"] Lemma backed_ok_of_budget : forall m nZ,
  MInv A m -> eager_used m + nZ + A_bytes A <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m).
Proof.
  intros m nZ [Hnd Hal Hallow Hlz Hb] Hle.
  rewrite vm_backing_used_split.
  pose proof (allowed_pages_bound A (m_vm_materialized m) HA Hnd Hal Hallow) as Hp. lia.
Qed.

#[using="HA"] Lemma mmap_backed_ok_of_budget : forall flags m nZ,
  MInv A m -> eager_used m + nZ + A_bytes A <= vm_limit (m_vmmaps m) ->
  mmap_noreserve_backed_ok flags m nZ = true.
Proof.
  intros flags m nZ HM Hle. unfold mmap_noreserve_backed_ok.
  destruct (mmap_noreserve_b flags); [reflexivity|]. apply Z.leb_le. exact (backed_ok_of_budget m nZ HM Hle).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma eager_used_mmap_model_le : forall (a n : word) m,
  ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (a, n) ->
  eager_used (mmap_model a n m) <= eager_used m + bv_unsigned n.
Proof.
  intros a n m W Wb. unfold mmap_model. eapply AsanNodesMmB.eager_used_cons_le; [exact W | exact Wb | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma MInv_mmap_model : forall (a n : word) m,
  ivs_wf (vm_maps (m_vmmaps m)) -> iv_wf (a, n) ->
  MInv A m -> eager_used m + bv_unsigned n + A_bytes A <= vm_limit (m_vmmaps m) ->
  MInv A (mmap_model a n m).
Proof.
  intros a n m W Wb HM Hb. eapply MInv_transport; [exact HM | reflexivity | reflexivity |].
  pose proof (eager_used_mmap_model_le a n m W Wb) as Hle.
  replace (vm_limit (m_vmmaps (mmap_model a n m))) with (vm_limit (m_vmmaps m)) by reflexivity. lia.
Qed.

#[using="Type"] Lemma mmap_model_lazy : forall (a n : word) m, m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_halted : forall (a n : word) m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fds : forall (a n : word) m, m_fds (mmap_model a n m) = m_fds m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fs : forall (a n : word) m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_maps : forall (a n : word) m, vm_maps (m_vmmaps (mmap_model a n m)) = (a, n) :: vm_maps (m_vmmaps m).
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_reserved : forall (a n : word) m, vm_reserved (m_vmmaps (mmap_model a n m)) = vm_reserved (m_vmmaps m).
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_limit : forall (a n : word) m, vm_limit (m_vmmaps (mmap_model a n m)) = vm_limit (m_vmmaps m).
Proof. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_init_sp : forall (a n : word) m, vm_init_sp (m_vmmaps (mmap_model a n m)) = vm_init_sp (m_vmmaps m).
Proof. reflexivity. Qed.
#[using="Type"] Lemma with_mmap_backing_eager : forall (flags a n : word) m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m Hf. unfold with_mmap_backing. rewrite Hf. reflexivity. Qed.
End Nodes.
End AsanNodes.

(* [comment removed for export] *)
Module AsanNodesBoot.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanNodesLibE AsanNodesMmLib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.StreamExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.FileSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.Footprint__Common.SpecConsts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesLibE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanNodesMmLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanPlanCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanNodes__Lib.AsanNodes.
Local Instance asannodesboot_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kind_none (k : APC.mkind) : bool := match k with APC.KNONE | APC.KNONELAZY => true | _ => false end.
Definition kind_lazy (k : APC.mkind) : bool := match k with APC.KRWLAZY | APC.KNONELAZY => true | _ => false end.

Record grant_post (kd : APC.mkind) (a n : word) (model model' : Model) : Prop := GP {
  gp_maps : vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model);
  gp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  gp_noacc : vm_noaccess (m_vmmaps model') = (if kind_none kd then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model));
  gp_lazy : m_vm_lazy model' = (if kind_lazy kd then (a, n) :: m_vm_lazy model else m_vm_lazy model);
  gp_mat : m_vm_materialized model' = m_vm_materialized model;
  gp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  gp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  gp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  gp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  gp_halted : m_halted model' = m_halted model;
  gp_fds : m_fds model' = m_fds model;
  gp_fs : m_fs model' = m_fs model;
  gp_tid : m_tid model' = m_tid model;
  gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model) }.

Definition grant_mem (kd : APC.mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z -> FULL' x = FULL x)
  /\ (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
        FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma srz_mmap_anon : forall regs (pc : word) mem rom model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok (getr regs 10) model a nZ = true) ->
  (forall a, grant_ok (getr regs 10) model a nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (mmap_model a n model)) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 nZ n Hex HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hpr : page_round_up (ms_gpr ms 1) = n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply (SpinAlg.srz_mmap segs ms model (getr regs 17) KB Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
  - rewrite H0, Hu1. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma srz_mmap_anon_split : forall regs (pc : word) mem rom model w (len : Z) (good : word -> bool) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok (getr regs 10) model a nZ = true /\ good a = true) ->
  (forall a, grant_ok (getr regs 10) model a nZ = true -> good a = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (mmap_model a n model)) KB) ->
  (forall a, grant_ok (getr regs 10) model a nZ = true -> good a = false ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (mmap_model a n model)) t_nil) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len good KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 nZ n Hex HB HC.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hpr : page_round_up (ms_gpr ms 1) = n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  destruct Hex as (a0 & Ha0 & Hg0).
  assert (Ha0' : grant_ok (ms_gpr ms 0) model a0 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true).
  { rewrite H0, Hu1. exact Ha0. }
  pose proof (SpinAlg.cnode_mmap segs ms model (getr regs 17) a0 Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Hargs Ha0') as Hnode.
  rewrite H0, Hu1 in Hnode. fold nZ in Hnode.
  assert (HB0 : KB []).
  { eapply srealizes_nonempty. apply (HB a0 Ha0 Hg0). }
  set (T := fun i : {a : word | grant_ok (getr regs 10) model a nZ = true} =>
              match i with exist _ a _ => if good a then KB else t_nil end).
  apply (srz_conseq segs _ (t_alt T)).
  - eapply (srz_cases segs _ _ _ T (exist _ a0 Ha0) Hnode).
    intros [a Ha]; cbn [T].
    rewrite Hpr. unfold ms, epend. rewrite adv_mmap_grant.
    destruct (good a) eqn:Hg; [apply HB | apply HC]; assumption.
  - intros tr. unfold t_alt. split.
    + intros [[a Ha] Hi]; cbn [T] in Hi.
      destruct (good a); [exact Hi|]. unfold t_nil in Hi. subst tr. exact HB0.
    + intros Hi. exists (exist _ a0 Ha0). cbn [T]. rewrite Hg0. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NR_CORE : Z := 1048610%Z.   (* [comment removed for export] *)

#[using="Type"] Lemma mmap_gates_core_nr : forall flags (prot : Z),
  mmap_flags_core flags = NR_CORE -> (prot = 0 \/ prot = 3)%Z ->
  mmap_modeled_b (Z_to_bv 64 prot) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 prot) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 prot) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 prot) flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 prot) flags (Z_to_bv 64 0) = Z.eqb prot 0
  /\ mmap_noreplace_rw_b (Z_to_bv 64 prot) flags (Z_to_bv 64 0) = Z.eqb prot 3.
Proof.
  intros flags prot Hc Hp. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b,
    mmap_noreplace_noaccess_b, mmap_noreplace_rw_b, mmap_noreplace_flags_b.
  rewrite Hc. destruct Hp as [-> | ->]; repeat split; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition noreplace_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
    (if Z.eqb prot 0 then (addr, n) :: vm_noaccess h else vm_noaccess h)
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Definition noreplace_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_backing flags addr n (with_vmmaps (noreplace_vmmaps prot addr n (m_vmmaps m)) m).

#[using="Type"] Lemma noreplace_model_halted : forall prot flags addr n m, m_halted (noreplace_model prot flags addr n m) = m_halted m.
Proof. intros. unfold noreplace_model. rewrite with_mmap_backing_halted. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_noreplace_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = NR_CORE ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  (prot = 3%Z -> mmap_noreserve_backed_ok flags model (page_round_up_Z len) = true) ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  check_syscall (sys_input segs ms x8) eff model
  = if region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n then
      match eff with
      | mkEffectU r [] zs us [] [] =>
          if errno_ret_in mmap_errnos r
          then match zs, us with [], [] => CheckOk model [] | _, _ => CheckReject end
          else if Z.eqb prot 0
               then match zs with
                    | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                            then CheckOk (noreplace_model prot flags addr n model) [] else CheckReject
                    | _ => CheckReject
                    end
               else match us with
                    | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                            then CheckOk (noreplace_model prot flags addr n model) [] else CheckReject
                    | _ => CheckReject
                    end
      | _ => CheckReject
      end
    else
      match eff with
      | mkEffectU r [] [] [] [] [] =>
          if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST) then CheckOk model [] else CheckReject
      | _ => CheckReject
      end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H5 Htop Hbud n.
  pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. pose proof (alloc_top_room (m_vmmaps model)) as AR.
    unfold two_pow_64, stack_max_size in AR. unfold page_size in PB. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core_nr flags prot Hcore Hprot) as (G1 & G2 & G3 & G4 & G5 & G6).
  rewrite G1, G2, G3, G4, G5, G6, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  assert (Hnw : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z len)%Z = false).
  { apply Z.leb_gt. pose proof (alloc_top_room (m_vmmaps model)) as AR. unfold stack_max_size in AR. lia. }
  assert (Htop' : (bv_unsigned addr + page_round_up_Z len <=? alloc_top (m_vmmaps model))%Z = true) by (apply Z.leb_le; exact Htop).
  assert (Hal' : (bv_unsigned addr mod page_size =? 0)%Z = true) by (apply Z.eqb_eq; exact Hal).
  assert (Hpos' : (0 <? bv_unsigned addr)%Z = true) by (apply Z.ltb_lt; exact Hpos).
  destruct Hprot as [-> | ->]; cbn [Z.eqb Pos.eqb]; cbv beta iota zeta;
    rewrite Hnw, Htop', Hal', Hpos'; cbn [negb]; fold n.
  - (* [comment removed for export] *)
    destruct (region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n) eqn:Hrf.
    + destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
      destruct zs; [|destruct cs; [destruct ci|]; destruct (errno_ret_in mmap_errnos r); reflexivity].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
      reflexivity.
    + reflexivity.
  - (* [comment removed for export] *)
    destruct (region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n) eqn:Hrf.
    + rewrite (Hbud eq_refl).
      destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
      destruct us; [|destruct cs; [destruct ci|]; destruct (errno_ret_in mmap_errnos r); destruct zs; reflexivity].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; reflexivity].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; reflexivity].
      destruct (errno_ret_in mmap_errnos r); [reflexivity|]. rewrite andb_true_r. reflexivity.
    + reflexivity.
Qed.

(* [comment removed for export] *)
Definition noreplace_mem (prot : Z) (addr n : word) (mem : word -> option byte) : word -> option byte :=
  if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem.
Definition noreplace_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

#[using="Type"] Lemma adv_noreplace_epend : forall prot regs pc mem rom x8 addr n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (noreplace_eff prot addr n))
  = mkst (regupd regs 10 addr) (v_addi pc 4) (noreplace_mem prot addr n mem) rom.
Proof.
  intros. unfold noreplace_eff, noreplace_mem. destruct (Z.eqb prot 0); [apply adv_unmaps1_epend | apply adv_zeros1_epend].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma not_errno_below_top : forall h (a : word) (n : Z),
  (0 < n)%Z -> (bv_unsigned a + n <= alloc_top h)%Z -> errno_ret_in mmap_errnos a = false.
Proof.
  intros h a n Hn Htop. destruct (errno_ret_in mmap_errnos a) eqn:E; [|reflexivity]. exfalso.
  destruct (proj1 (errno_ret_in_true _ _) E) as (e & He & ->).
  rewrite (mmap_errnos_is_ENOMEM e He) in Htop. pose proof (alloc_top_room h) as AR.
  unfold stack_max_size, two_pow_64 in AR.
  change (bv_unsigned (errno_ret ENOMEM)) with (2 ^ 64 - 12)%Z in Htop. lia.
Qed.

Section NoReplace.
  Variables (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (w : bv 32).
  Variables (prot : Z) (flags addr : word) (len : Z).
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 222.
  Hypothesis Hprot : (prot = 0 \/ prot = 3)%Z.
  Hypothesis Hcore : mmap_flags_core flags = NR_CORE.
  Hypothesis H10 : getr regs 10 = addr.
  Hypothesis Hal : (bv_unsigned addr mod page_size = 0)%Z.
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 len.
  Hypothesis Hlen : (0 < len)%Z.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 prot.
  Hypothesis H13 : getr regs 13 = flags.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 0.
  Hypothesis Htop : (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z.
  Hypothesis Hbud : (prot = 3%Z -> mmap_noreserve_backed_ok flags model (page_round_up_Z len) = true).

  #[local] Notation n := (Z_to_bv 64 (page_round_up_Z len)).
  #[local] Notation ms := (epend regs pc mem rom (getr regs 17)).

  #[local] Ltac get_chk Hchk :=
    pose proof (fun eff => mmap_noreplace_check ms (getr regs 17) model eff prot flags addr len
                 ltac:(rewrite H17; apply u64_lit; lia) Hprot Hcore
                 ltac:(rewrite ms_gpr_epend0; exact H10) Hal Hpos
                 ltac:(rewrite ms_gpr_epend1; exact H11) Hlen
                 ltac:(rewrite ms_gpr_epend2; exact H12)
                 ltac:(rewrite ms_gpr_epend3; exact H13)
                 ltac:(rewrite ms_gpr_epend5; exact H15) Htop Hbud) as Hchk;
    cbv zeta in Hchk.

  (* [comment removed for export] *)
  #[using="w HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen H12 H13 H15 Htop Hbud"] Lemma srz_mmap_noreplace_free : forall K,
    region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
    srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (noreplace_mem prot addr n mem) rom)
                        (noreplace_model prot flags addr n model)) K ->
    srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
  Proof.
    intros K Hrf HK. get_chk Hchk.
    assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
    eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
    pose (effs := fun b : bool => if b then noreplace_eff prot addr n else mkEffectU (errno_ret ENOMEM) [] [] [] [] []).
    pose (ms' := fun b : bool => if b then noreplace_model prot flags addr n model else model).
    assert (NE : errno_ret_in mmap_errnos addr = false).
    { apply (not_errno_below_top (m_vmmaps model) addr (page_round_up_Z len)); [|exact Htop].
      pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
    apply (srz_prune segs ms model (getr regs 17) bool effs ms' (fun b => b) true K eq_refl
             ltac:(rewrite Hno; reflexivity)).
    - apply (node_chk_noacc segs ms model (getr regs 17) bool effs ms' Hh eq_refl).
      + intros [|]; cbn [effs ms']; rewrite Hchk, Hrf.
        * unfold noreplace_eff.
          destruct Hprot as [-> | ->]; cbn [Z.eqb Pos.eqb]; rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
        * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk, Hrf in Hc.
        destruct ws; [|discriminate]. destruct cs; [|destruct zs; destruct us; destruct (errno_ret_in mmap_errnos r); try discriminate; destruct (prot =? 0)%Z; discriminate].
        destruct ci; [|destruct zs; destruct us; destruct (errno_ret_in mmap_errnos r); try discriminate; destruct (prot =? 0)%Z; discriminate].
        destruct (errno_ret_in mmap_errnos r) eqn:Er.
        * destruct zs; [|discriminate]. destruct us; [|discriminate]. injection Hc as <- <-.
          destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
          rewrite (mmap_errnos_is_ENOMEM e He). exists false. repeat split; reflexivity.
        * exists true. cbn [effs ms']. unfold noreplace_eff.
          destruct (prot =? 0)%Z.
          -- destruct zs; [|discriminate]. destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool eqn:Eb; [|discriminate].
             apply andb_prop in Eb as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us.
             injection Hc as <- <-. repeat split; reflexivity.
          -- destruct us; [|discriminate]. destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)])%bool eqn:Eb; [|discriminate].
             apply andb_prop in Eb as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs.
             injection Hc as <- <-. repeat split; reflexivity.
      + intros [r ws zs us cs ci] Hc. rewrite Hchk, Hrf in Hc.
        destruct ws; [|discriminate]. destruct cs; [|destruct zs; destruct us; destruct (errno_ret_in mmap_errnos r); try discriminate; destruct (prot =? 0)%Z; discriminate].
        destruct ci; [|destruct zs; destruct us; destruct (errno_ret_in mmap_errnos r); try discriminate; destruct (prot =? 0)%Z; discriminate].
        destruct (errno_ret_in mmap_errnos r); [destruct zs; destruct us; discriminate|].
        destruct (prot =? 0)%Z; [destruct zs; [destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate | discriminate]
                                | destruct us; [destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)])%bool; discriminate | discriminate]].
      + intros [|]; cbn [ms']; [rewrite noreplace_model_halted|]; exact Hh.
      + intros [|]; cbn [effs]; [unfold noreplace_eff; destruct (prot =? 0)%Z|]; reflexivity.
    - intros [|] Hk; [|discriminate Hk]. cbn [effs]. rewrite (mmap_refusal_b segs _ _ _ _ Hno).
      unfold noreplace_eff. destruct (prot =? 0)%Z; exact NE.
    - intros [|] Hk; [discriminate Hk|]. cbn [effs]. rewrite (mmap_refusal_b segs _ _ _ _ Hno).
      exact (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos).
    - reflexivity.
    - intros [|] Hk; [|discriminate Hk]. cbn [effs ms']. rewrite adv_noreplace_epend. exact HK.
  Qed.


End NoReplace.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_none_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem srz_mmap_none_pin_spin : forall regs (pc : word) mem rom model w (len : Z) (flags : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) K) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w len flags K HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HK.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_none_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => with_mmap_backing flags a n (noaccess_model a n model) end).
  apply (srz_prune segs ms model (getr regs 17) (unit + IB) effs ms'
           (fun i => match i with inl _ => false | inr _ => true end) (inr (exist _ a0 Ha0)) K eq_refl
           ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk_noacc segs ms model (getr regs 17) (unit + IB) effs ms' Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_is_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
        destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted, noaccess_model_halted; exact Hh].
    + intros [[] | [a Ha]]; reflexivity.
  - intros [[] | [a Ha]] Hk; [discriminate Hk|]. cbn [effs]. rewrite (mmap_refusal_b segs _ _ _ _ Hno).
    exact (grant_pin_not_errno model a nZ Hn0 Ha).
  - intros [[] | [a Ha]] Hk; [|discriminate Hk]. cbn [effs]. rewrite (mmap_refusal_b segs _ _ _ _ Hno).
    exact (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos).
  - reflexivity.
  - intros [[] | [a Ha]] Hk; [discriminate Hk|]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HK. exact Ha.
Qed.

End WithSegs.
End AsanNodesBoot.
