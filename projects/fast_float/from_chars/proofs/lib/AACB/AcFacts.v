(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition with_facts (S : sst) (fs : list fact) : sst := SST (s_pc S) (s_regs S) (s_rgs S) fs (s_next S) (s_resv S).

Section Facts.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Theorem den_facts : forall E S M ms model fs',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S) -> Forall (fact_ok E') fs') ->
  DEN segs LIMIT model0 mem0 E (with_facts S fs') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model fs' Hd Hf.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; cbn [with_facts s_rgs s_next]; try assumption.
  intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_facts s_pc s_regs s_rgs s_facts s_resv].
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj (Hf E' Ha A7) A8))))))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_sub_facts : forall E S M ms model fs',
  DEN segs LIMIT model0 mem0 E S M ms model -> forallb (fact_implied (s_facts S)) fs' = true ->
  DEN segs LIMIT model0 mem0 E (with_facts S fs') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model fs' Hd Hi. apply (den_facts E S M ms model fs' Hd).
  intros E' _ HF. rewrite Forall_forall. rewrite forallb_forall in Hi. intros f Hf. exact (fact_implied_ok E' _ f HF (Hi f Hf)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_add_facts : forall E S M ms model fs,
  DEN segs LIMIT model0 mem0 E S M ms model -> (forall E', agree (s_next S) E E' -> Forall (fact_ok E') fs) ->
  DEN segs LIMIT model0 mem0 E (with_facts S (s_facts S ++ fs)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model fs Hd Hf. apply (den_facts E S M ms model _ Hd).
  intros E' Ha HF. apply Forall_app. split; [exact HF | exact (Hf E' Ha)].
Qed.
(* [comment removed for export] *)
Definition sp_fact (M : smodel) : fact := FRange (sm_sp M) sp_window_lo sp_window_hi.
#[using="Type"] Theorem den_sp_fact : forall E S M ms model,
  DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E (with_facts S (s_facts S ++ [sp_fact M])) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model Hd. apply (den_add_facts E S M ms model _ Hd). intros E' Ha. constructor; [|constructor].
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf. unfold sm_wf in Hwf.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
  assert (Hl : lwf (s_next S) (sm_sp M) = true) by assumption.
  cbn [sp_fact fact_ok]. rewrite (lden_agree_wf _ E E' _ Hl Ha).
  rewrite <- (dn_sp _ _ _ _ _ _ _ _ _ Hd). destruct (dn_spok _ _ _ _ _ _ _ _ _ Hd) as [Hlo Hhi]. unfold init_sp_ok in Hlo. lia.
Qed.
End Facts.
(* [comment removed for export] *)
