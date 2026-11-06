(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState Mem Exec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes RzBridge.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Mem OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Exec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import KNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {BW : BWorld}.

(* [comment removed for export] *)
Fixpoint twf {R} (t : itree node R) (md : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r md
  | Vis n k => nsafe n md /\ forall eff md', nstep n md eff md' -> bw_gate_n n md -> twf (k eff) md' P
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rz_impl : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms md (P : R -> Model -> Prop) T,
  impl segs (at_node segs) t Q ms -> KI md -> twf t md P ->
  (forall r ms' md', Q r ms' -> P r md' -> KI md' -> realizes segs (mkCfg ms' md') T) ->
  realizes segs (mkCfg ms md) T.
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms md P T HI HK HW HC; cbn in HI, HW.
  - destruct HK as [Hh Hl]. eapply rz_evt; [exact HI | exact Hh | exact Hl |].
    intros ms' HQ. apply (HC r ms' md HQ HW). split; assumption.
  - destruct HK as [Hh Hl]. destruct HW as [Hs Hk].
    eapply rz_evt; [exact HI | exact Hh | exact Hl |].
    intros ms1 [Hat Himpl].
    apply (rz_at_node segs n ms1 md T Hat (conj Hh Hl) Hs).
    intros eff md' Hst Hgate HK'. apply (IH eff Q (nret ms1 eff) md' P T (Himpl eff) HK' (Hk eff md' Hst Hgate) HC).
Qed.

(* [comment removed for export] *)
Corollary rz_impl_epost : forall {A} (t : itree node (Exc.exc A)) (Q : A -> machine_state -> Prop) ms md
    (P : A -> Model -> Prop) T,
  impl segs (at_node segs) t (epost Q) ms -> KI md ->
  twf t md (fun r md' => match r with Exc.Unr => False | Exc.Ok a => P a md' end) ->
  (forall a ms' md', Q a ms' -> P a md' -> KI md' -> realizes segs (mkCfg ms' md') T) ->
  realizes segs (mkCfg ms md) T.
Proof.
  intros A t Q ms md P T HI HK HW HC.
  eapply (rz_impl t (epost Q) ms md _ T HI HK HW).
  intros [|a] ms' md' HQ HP HK'; cbn in HQ, HP; [contradiction|]. eapply HC; eauto.
Qed.

End WithSegs.
