(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_anndefs RT_state RT_rep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Theorem rta_live_nodup_real : forall (Σ : rts RTA) (m : mem), ART RTA Σ m -> List.NoDup (map fst (live Σ)).
Proof.
  intros Σ m HA. destruct HA as (WF & _). destruct WF as (_ & _ & LW & _). destruct LW as (_ & ND & _). exact (proj1 (stdpp.base.NoDup_ListNoDup _) ND).
Qed.

Theorem rta_live_fresh : forall (Σ : rts RTA) (m : mem) (p n : Z) (l : list (Z * Z)),
  ART RTA Σ m -> rt_live RTA Σ = (p, n) :: l -> 0 < n -> forall e, In e l -> fst e <> p.
Proof.
  intros Σ m p n l HA E Hn e He Hp. pose proof (rta_live_nodup_real Σ m HA) as ND.
  cbn [rt_live RTA] in E. unfold rtA_live in E.
  destruct (live Σ) as [|[q k] L] eqn:EL; [discriminate E|].
  rewrite vis_live_cons in E. cbn [map fst] in ND. apply NoDup_cons_iff in ND as [NI ND].
  assert (HQ : q = p).
  { pose proof (vis1_nonnil (ann Σ) (q, k)) as NN. destruct (vis1 (ann Σ) (q, k)) as [|x r] eqn:EV; [exfalso; exact (NN eq_refl)|].
    cbn in E. injection E as -> _. symmetry. exact (vis1_fst (ann Σ) (q, k) (p, n) ltac:(rewrite EV; left; reflexivity)). }
  subst q.

  unfold vis1 in E. cbn [fst snd] in E. destruct (alook p k (ann Σ)) as [v|] eqn:AL.
  - pose proof (alook_ok p k (ann Σ) v AL) as (O1 & _). unfold ann_block in E. rewrite (proj2 (Z.eqb_neq v k) ltac:(lia)) in E.
    cbn in E. injection E as En _. unfold ann_g1 in En. pose proof (Z.div_pos (k / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). lia.
  - cbn in E. injection E as _ <-.
    destruct e as [q' k']. cbn in Hp. subst q'. destruct (In_vis_live (ann Σ) L p k' He) as (n0 & Hin0 & _).
    apply NI. apply in_map_iff. exists (p, n0). split; [reflexivity | exact Hin0].
Qed.

End GWIN.
