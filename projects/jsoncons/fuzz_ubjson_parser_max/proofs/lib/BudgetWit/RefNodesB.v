(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from fuzz_bigint's RefNodes.v, whose twinned declarations have the same statements as this harness's RefNodes.v (whose statements are TCodec-encoded): the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: requires RomBase, passes the new read-only-memory premise via ltac:(rob_mf Hno) to SpinAlgB.rzb_cases1 in rzb_set_tid_at, drops a removed comment, and strips leading indentation from import lines and all lemma statements and proofs; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/RefNodesB.v, lines 19, 89. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import AgentNodesB SpinAlgB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common.Cfg Require RomBase.
Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Section FPX_1.
Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma check_syscall_96 : forall ms x8 eff m,
bv_unsigned x8 = 96%Z ->
check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.
Lemma node_set_tid : forall ms model x8,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
node_ok segs scfg (mkCfg ms model) RefNodes.tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Htid.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
match eff with
| mkEffectU ret [] [] [] [] [] =>
if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
then CheckOk (with_tid ret model) [] else CheckReject
| _ => CheckReject end).
{ intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
pose (effs := fun i : RefNodes.tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
assert (Enx : forall i : RefNodes.tid_I,
mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
= mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
{ intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
assert (Hnode : node_ok segs scfg (mkCfg ms model) RefNodes.tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
{ apply (node_chk segs scfg ms model x8 RefNodes.tid_I effs (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
- intros [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
- intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
- intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
- intros i. rewrite RefNodes.with_tid_halted. exact Hh.
- intros i. rewrite RefNodes.with_tid_lazy. exact Hlazy.
- intros i. apply not_spurious_on. apply injected_family_off_none. rewrite in_sysno_sys_input, Hno. exact injected_arm_96. }
destruct Hnode as [Hfw Hbw]. split.
- intros i. rewrite Enx. apply Hfw.
- intros e st Hss. destruct (Hbw e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.
Lemma rzb_set_tid_at : forall ms model x8 K,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
SpinAlgB.rzb segs scfg (mkCfg (advance_past_svc (set_gpr0 ms tid)) (with_tid tid model)) K) ->
SpinAlgB.rzb segs scfg (mkCfg ms model) K.
Proof.
intros ms model x8 K Hh Hlazy Hsvc Hno Htid Hk.
apply (SpinAlgB.rzb_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ (Z_to_bv 64 1) one_tid_ok)
(node_set_tid ms model x8 Hh Hlazy Hsvc Hno Htid)
ltac:(rob_mf Hno)
(SpinAlgB.nalloc_ok_no ms model x8 96 Hsvc Hno eq_refl)).
intros [t Ht]. cbn [proj1_sig]. apply Hk. exact Ht.
Qed.
Lemma rz_set_tid_b : forall regs (pc : word) mem rom model K w,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
SpinAlgB.rzb segs scfg (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
SpinAlgB.rzb segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
eapply AgentNodesB.rz_sys_b; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply (rzb_set_tid_at _ model (getr regs 17));
[exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid |].
intros t Ht. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.
Lemma rz_exit_at_b : forall regs (pc : word) mem rom model w code,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
(getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
getr regs 10 = code ->
SpinAlgB.rzb segs scfg (mkCfg (mkst regs pc mem rom) model)
(t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
eapply AgentNodesB.rz_sys_b; [exact Hh | exact Hlazy | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply SpinAlgB.rzb_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
End WithSegs.
End FPX_1.
