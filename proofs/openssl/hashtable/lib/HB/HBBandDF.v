(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CxPlan CxHooks CxfExec CxfPlan CxfL6.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxNodesJoinZ AsanNodesRP HBPlanImage HBAtable HBHooksC HBHooks HBRPTab HBRP HBBandD HBCheckG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import CAP.
Open Scope Z_scope.

Lemma diamond_tree_g_eq : forall segs IT A KC GC bfuel (RB : nat -> list Z -> acs -> option acs),
  (forall gb stops cs, RB gb stops cs = CAP.run_block_gcx segs IT GC gb KC bfuel stops cs) ->
  forall fuel gb nx joinpc cs, CXFP.diamond_tree_g IT A RB gb nx fuel joinpc cs = CAP.diamond_tree segs IT A KC GC bfuel gb nx fuel joinpc cs.
Proof.
  intros segs IT A KC GC bfuel RB HRB fuel. induction fuel as [|f IH]; intros gb nx joinpc cs; [reflexivity|].
  cbn [CXFP.diamond_tree_g CAP.diamond_tree]. rewrite HRB.
  destruct (CAP.run_block_gcx segs IT GC gb KC bfuel (joinpc :: STOPS A) cs) as [cs'|]; [|reflexivity].
  destruct (Z.eqb (pc cs') joinpc); [reflexivity|]. destruct (negb (Nat.leb nx (nxt cs'))); [reflexivity|].
  destruct (branch_probe IT cs') as [e|]; [|reflexivity]. destruct (erange (kn cs') e) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb lo 0 && Z.ltb 0 hi)%bool; [|reflexivity]. rewrite !IH. reflexivity.
Qed.

Definition node_band_diamond_f (segs : list Segment) (A : atable) (nx0 : nat) (args : list expr) (cs : acs) : option acs :=
  match args with
  | ELit v :: ELit joinpc :: ELit depth :: ELit itlo :: ELit itn :: rsl =>
      let IT := APC.mk_itab_ranges segs [(itlo, Z.to_nat itn)] in
      let nx := nxt cs in
      match node_band A cs (Z.to_nat v) with
      | Some (csl, csh) =>
          match CXFP.diamond_tree_g IT A (CXFEL.RB_f segs IT true 0 400000) nx0 nx (Z.to_nat depth) joinpc csl,
                CXFP.diamond_tree_g IT A (CXFEL.RB_f segs IT true 0 400000) nx0 nx (Z.to_nat depth) joinpc csh with
          | Some (l0 :: ll), Some lh => diamond_join_all A nx0 nx joinpc (BDN.lits rsl) l0 (ll ++ lh)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.
Lemma node_band_diamond_f_eq : forall segs A nx0 args cs, node_band_diamond_f segs A nx0 args cs = BDN.node_band_diamond segs A nx0 args cs.
Proof.
  intros segs A nx0 args cs. unfold node_band_diamond_f, BDN.node_band_diamond.
  destruct args as [|[v| | | | | | |] [|[joinpc| | | | | | |] [|[depth| | | | | | |] [|[itlo| | | | | | |] [|[itn| | | | | | |] rsl]]]]]; try reflexivity.
  destruct (node_band A cs (Z.to_nat v)) as [[csl csh]|]; [|reflexivity].
  rewrite !(diamond_tree_g_eq segs _ A 0%nat true 400000%nat (CXFEL.RB_f segs _ true 0 400000)
              (fun gb stops c => eq_trans (f_equal (fun F => F segs _ true 0%nat 400000%nat gb stops c) CXFEL.L_CXFEL_RB_f) (CXFE.RB_f_eq segs _ true 0%nat 400000%nat gb stops c))).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition hagx_xn_f (NX : nat) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 42 then node_band_diamond_f HASEGS HAT NX args cs else hagx_xn NX id args cs.
Definition hag_XN_f (NX : nat) : nat -> list expr -> acs -> option acs :=
  xn_plus (hagx_xn_f NX) (xn_plus (RPN.xn HASEGS NX RP_HA) (xn_plus (ha_xn NX) zj_xn)).
Lemma hagx_xn_f_eq : forall NX id args cs, hagx_xn_f NX id args cs = hagx_xn NX id args cs.
Proof.
  intros NX id args cs. unfold hagx_xn_f. destruct (Nat.eqb id 42) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst id. rewrite node_band_diamond_f_eq. reflexivity.
Qed.
Lemma hag_XN_f_eq : forall NX id args cs, hag_XN_f NX id args cs = hag_XN NX id args cs.
Proof. intros NX id args cs. unfold hag_XN_f, hag_XN, xn_plus. rewrite hagx_xn_f_eq. reflexivity. Qed.
