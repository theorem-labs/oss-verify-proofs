(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QFOH.v: module Mq1 (the start-up walk ref_startup and the set_tid_address node), over BudgetWit.QRjHB.realizes; the set_tid_address node takes its budget check. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: ref_startup's valid_launch and entry_launch_ok_va premises, main_entry over the launch's input, mmap base and entry point, and the hand-off model of init_config; RomBase.sys_rob at the set_tid_address node). *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS QSpR QRjH QBxa QFeQ Qdbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwNp QsV0 QsRG Qnhz Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB QBxaB Q9oxB.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.json_c.json_object_fuzzer.images.Plain.
Import QJyS QwNp QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG QRjH QBxa.Mq4 QBxa.Mq0 Q9ox.Mq0 QSpR.Mq3.
Import QFeQ Qdbv.
Import ListNotations.
Open Scope bv_scope.
Import QRjHB QBxaB.Mq4 Q9oxB.Mq0.

#[local] Existing Instance fp0F.
#[local] Existing Instance fp0C.

Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

Lemma bwd_rz : forall segs model K,
m_halted model = None -> m_vm_lazy model = [] ->
bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

Section SetTid.
Variable segs : list Segment.

Definition tid_I0 : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

#[using="Type"] Lemma one_tid_ok0 : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

#[using="Type"] Lemma node_set_tid0 : forall ms model x8,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
node_ok segs (mkCfg ms model) tid_I0 (fun _ => [])
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Htid.
assert (Hchk : forall o, syscall_spec (sys_input segs ms x8) model o <->
exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
{ intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
apply set_tid_fresh_outcome. exact Htid. }
pose (effs := fun i : tid_I0 => mkEffectU (proj1_sig i) [] [] [] [] []).
assert (Enx : forall i : tid_I0,
mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
= mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
{ intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
assert (Hnode : node_ok segs (mkCfg ms model) tid_I0 (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
{ apply (node_family segs ms model x8 tid_I0 effs (fun i => with_tid (proj1_sig i) model) (fun _ => []) _
Hh Hsvc Hchk).
- intros [t Ht]. exists t. split; [exact Ht|reflexivity].
- intros o (t & Ht & ->). exists (exist _ t Ht). reflexivity.
- intros i. exact Hh.
- intros i. exact Hlazy.
- intros i. apply not_spurious_sysno. rewrite in_sysno_sys_input, Hno. vm_compute. intuition discriminate. }
destruct Hnode as [Hn1 Hn2]. split.
- intros i. rewrite Enx. apply Hn1.
- intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_set_tid0 : forall regs (pc : word) mem rom model K w,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
apply (rz_conseq segs _ (t_alt (fun _ : tid_I0 => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok0); exact Ht]].
eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok0)
| eapply node_set_tid0; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
| eapply (Cfg.RomBase.sys_rob_memfree segs);
  [reflexivity | rewrite H17, u64_lit by lia; exact Cfg.RomBase.memfree_96]
| apply (budget_ok_num _ model (getr regs 17) 96);
  [reflexivity | rewrite H17; apply u64_lit; lia | reflexivity] |].
intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.
End SetTid.

(* LPS 727298f3: the start-up runs on the launch's input; the launch facts it reads ([valid_launch], the
   Sv48 [entry_launch_ok_va]) are the start's premises, and the hand-off model is the start
   configuration's own (as coturn/FuzzStunClient's RefStartup.ref_startup). *)
Theorem ref_startup : forall sp brk mbase rnd lim inp K (Hsp : valid_sp sp),
valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
(forall tid regs mem,
(0 < bv_unsigned tid < 2^22)%Z ->
@main_entry (amb_of inp rnd sp Hsp) inp mbase (0x20874 : word) sp (in_argv inp) (in_envp inp) tid regs mem ->
realizes rsegs (mkCfg (mkst regs (0x209c0 : word) mem (seg_rom rsegs))
(with_tid tid (cfg_model (init_config rsegs rpc rph sp brk mbase rnd lim inp)))) K) ->
realizes rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
Proof.
intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
change (realizes rsegs ?c K)
with ((fun st model => realizes rsegs (mkCfg st model) K) (cfg_ms c) (cfg_model c)).
apply (startup (fun st model => realizes rsegs (mkCfg st model) K)) with (Hsp := Hsp).
- intros model Hh Hlazy. apply bwd_rz; assumption.
- intros regs pc mem model w HF HE Hh Hlazy H17 Htid Hk.
eapply rz_set_tid0; eassumption.
- exact Hva.
- exact Hve.
- exact Hvl.
- exact Hlau.
- exact HK.
Qed.
End Mq1.
