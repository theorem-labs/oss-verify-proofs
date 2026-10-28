(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition B0 (vop : nat) : expr := EExt false 0 1 (EVar vop).

Lemma b0_val : forall vop E, exists w, 0 <= w < 256 /\ edenot E (B0 vop) = Z_to_bv 64 w.
Proof.
  intros vop E. unfold B0. cbn [edenot]. unfold ext_val.
  exists (ext_Z false 0 1 (bv_unsigned (ev E vop))). split; [|reflexivity].
  unfold ext_Z. change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (2 ^ 0) with 1. rewrite Z.div_1_r.
  pose proof (Z.mod_pos_bound (bv_unsigned (ev E vop)) (2 ^ 8) ltac:(lia)) as H. change (2 ^ 8) with 256 in *. exact H.
Qed.

Definition opfact_ok (vop : nat) (w : Z) (F : kentry) : bool :=
  match F with
  | KRange e lo hi =>
      match AX2.eval_closed (AX2.esubst (B0 vop) (ELit w) e) with
      | Some v => (Z.leb lo v && Z.leb v hi)%bool
      | None => false
      end
  | _ => false
  end.

Lemma opfact_ok_sound : forall vop E w F, edenot E (B0 vop) = Z_to_bv 64 w -> opfact_ok vop w F = true -> pure_holds E F.
Proof.
  intros vop E w F Hb H. unfold opfact_ok in H.
  destruct F as [ | | | | | e lo hi | | | | ]; try discriminate H.
  destruct (AX2.eval_closed (AX2.esubst (B0 vop) (ELit w) e)) as [v|] eqn:Hev; [|discriminate H].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (AX2S.eval_closed_sound E _ _ Hev) as Hd. pose proof (AX2S.eval_closed_range _ _ Hev) as Hr.
  rewrite (AX2S.esubst_sound E (B0 vop) (ELit w)) in Hd by (cbn [edenot]; symmetry; exact Hb).
  cbn [pure_holds]. rewrite Hd, u_lit64. change two64 with (2 ^ 64) in *. rewrite Z.mod_small by exact Hr. lia.
Qed.

Definition ops_cover (vop : nat) (ops : list opd) : bool :=
  forallb (fun n => existsb (fun o => forallb (opfact_ok vop (Z.of_nat n)) (od_F o)) ops) (seq 0 256).

Theorem opsel_of_cover : forall vop ops (opdom : list kentry), ops_cover vop ops = true ->
  forall E, Forall (pure_holds E) opdom -> exists o, In o ops /\ Forall (pure_holds E) (od_F o).
Proof.
  intros vop ops opdom Hc E _. destruct (b0_val vop E) as [w [Hw Hd]].
  unfold ops_cover in Hc. pose proof (proj1 (forallb_forall _ _) Hc (Z.to_nat w) ltac:(apply in_seq; lia)) as Hx.
  cbv beta in Hx. rewrite Z2Nat.id in Hx by lia. apply existsb_exists in Hx as [o [Ho Hf]].
  exists o. split; [exact Ho|]. apply Forall_forall. intros F HF.
  exact (opfact_ok_sound vop E w F Hd (proj1 (forallb_forall _ _) Hf F HF)).
Qed.
