(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/RzNodesImpl.v: rz_outcomes, rz_det_silent and rz_impl_enode restated over BudgetWit.Rzb.rzb, with their released proofs; rz_det_silent_b also takes the alloc_no_b check its node needs. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: rzb_outcomes and rzb_det_silent take the node's RomBase.sys_rob, as rz_outcomes and rz_det_silent do. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ExitSim ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec Frame ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
Import RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RomBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb Lib_SCPSB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(** [RzNodes.rz_outcomes]: the node's number passes [alloc_no_b], which is
    the grant check. *)
Lemma rzb_outcomes : forall ms mo x8 (I : Type) (effs : I -> resp) (mos : I -> Model) (evs : I -> list event)
                           (T : I -> TSet) (i0 : I),
  m_halted mo = None -> ms_svc_pending ms = Some x8 -> sys_rob segs (mkCfg ms mo) -> alloc_no_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> exists i, o = Ok (effs i) (mos i) (evs i)) ->
  (forall i, m_halted (mos i) = None) -> (forall i, m_vm_lazy (mos i) = []) ->
  (forall i, rzb segs (mkCfg (nret ms (effs i)) (mos i)) (T i)) ->
  rzb segs (mkCfg ms mo) (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros ms mo x8 I effs mos evs T i0 Hh Hsvc Hrob Hb Hiff Hh' Hl' HK.
  apply (rzb_node segs (mkCfg ms mo) I evs (fun i => mkCfg (nret ms (effs i)) (mos i)) T i0).
  - apply (node_outcomes segs ms mo x8 I effs mos evs Hh Hsvc Hiff Hh' Hl').
    intros i. exact (nsp_no segs ms x8 _ mo (effs i) eq_refl Hb).
  - exact Hrob.
  - exact (grant_ok_no ms mo x8 _ Hsvc eq_refl Hb).
  - exact HK.
Qed.

(** [RzNodes.rz_det_silent], with the premise [alloc_no_b (bv_unsigned x8) =
    false]: the released lemma needs no number check (a deterministic call is
    never a spurious refusal, [Cfg.nsp_det]), but [rzb]'s node needs one. *)
Lemma rzb_det_silent : forall ms mo x8 eff mo' K,
  m_halted mo = None -> ms_svc_pending ms = Some x8 -> sys_rob segs (mkCfg ms mo) -> alloc_no_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok eff mo' []) ->
  m_halted mo' = None -> m_vm_lazy mo' = [] ->
  rzb segs (mkCfg (nret ms eff) mo') K ->
  rzb segs (mkCfg ms mo) K.
Proof.
  intros ms mo x8 eff mo' K Hh Hsvc Hrob Hb Hiff Hh' Hl' HK.
  eapply rzb_silent1; [| exact Hrob | exact (grant_ok_no ms mo x8 _ Hsvc eq_refl Hb) | exact HK].
  apply (node_outcomes segs ms mo x8 unit (fun _ => eff) (fun _ => mo') (fun _ => []) Hh Hsvc);
    [| intros _; exact Hh' | intros _; exact Hl' |].
  - intros o. rewrite Hiff. split; [intros ->; exists tt; reflexivity | intros [[] ->]; reflexivity].
  - intros _. apply nsp_det. intros eff' m' evs' Hs. apply Hiff in Hs. injection Hs as -> _ _. reflexivity.
Qed.

Lemma rzb_impl_enode : forall {A} n (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo K,
  MOK mo ->
  impl segs (at_node segs) (enode n dec) (epost Q) ms ->
  (forall ms1, at_node segs n ms1 ->
     (forall rsp' a mo' K', dec rsp' = Some a -> MOK mo' ->
        (forall ms2, Q a ms2 -> rzb segs (mkCfg ms2 mo') K') ->
        rzb segs (mkCfg (nret ms1 rsp') mo') K') ->
     rzb segs (mkCfg ms1 mo) K) ->
  rzb segs (mkCfg ms mo) K.
Proof.
  intros A n dec Q ms mo K HM Himpl Hnode.
  cbn in Himpl. eapply rzb_evt; [exact HM | exact Himpl |].
  intros ms1 [Hat Hk]. apply (Hnode ms1 Hat).
  intros rsp' a mo' K' Hdec HM' HK. specialize (Hk rsp'). rewrite Hdec in Hk. cbn in Hk.
  eapply rzb_evt; [exact HM' | exact Hk |]. intros ms2 HQ. apply HK. exact HQ.
Qed.

End WithSegs.
