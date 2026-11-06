(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore CxPlan CxfCarry CxfExec CxfNodes CxfPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXF.
Import AX2. Import APC. Import CAP.

Definition check_f (segs : list Segment) (IT : itab) (A : atable) (nx0 : nat) (LIMIT : Z)
  (XN : nat -> list expr -> acs -> option acs) (XE : nat -> list expr -> acs -> option (Z * list spiece * acs))
  (XB : nat -> list expr -> acs -> option (acs * acs)) (HS : nat -> option acs) (KC : nat) (FO SPIN GC : bool) (bfuel : nat)
  (fuel : nat) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  CXFP.check_g segs IT A nx0 LIMIT XN XE XB HS FO SPIN (CXFE.RB_f segs IT GC KC bfuel) (node_x segs A nx0) CXFN.node_respell_f (entails_x segs A nx0)
               fuel lc cs p.

Theorem check_f_eq : forall segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p,
  check_f segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p
  = CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p.
Proof.
  intros. unfold check_f. apply CXFP.check_g_eq; intros; try reflexivity; [apply CXFE.RB_f_eq | apply CXFN.node_respell_f_eq].
Qed.

Lemma check_f_intro : forall segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p r,
  check_f segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r ->
  CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r.
Proof. intros. rewrite <- check_f_eq. assumption. Qed.

(* [comment removed for export] *)
Lemma check_f_hooks : forall segs IT A nx0 LIMIT XN XE XB HS XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p r,
  (forall id args c, XN' id args c = XN id args c) -> (forall id args c, XE' id args c = XE id args c) ->
  (forall id args c, XB' id args c = XB id args c) -> (forall h, HS' h = HS h) ->
  check_f segs IT A nx0 LIMIT XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p = r ->
  CAP.check segs IT A nx0 LIMIT XN XE XB HS KC FO SPIN GC bfuel fuel lc cs p = r.
Proof.
  intros segs IT A nx0 LIMIT XN XE XB HS XN' XE' XB' HS' KC FO SPIN GC bfuel fuel lc cs p r H1 H2 H3 H4 H.
  assert (E1 : XN' = XN) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H1).
  assert (E2 : XE' = XE) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H2).
  assert (E3 : XB' = XB) by (apply functional_extensionality; intros id; apply functional_extensionality; intros a; apply functional_extensionality; intros c; apply H3).
  assert (E4 : HS' = HS) by (apply functional_extensionality; intros h; apply H4).
  subst XN' XE' XB' HS'. apply check_f_intro. exact H.
Qed.

End CXF.
