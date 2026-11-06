(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxDrv FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChEnt FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps.

Module AsanMergeS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section MergeS.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_merge_s : forall E S M ms model l1 b1 b2 s1 s2 l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b1 s1 RW TEmpty :: RG b2 s2 RW TEmpty :: l2 ->
  (forall E', agree (s_next S) E E' -> 0 < uE E' s1 /\ 0 < uE E' s2 /\ uE E' s1 + uE E' s2 < two64 /\ uE E' b2 = uE E' b1 + uE E' s1) ->
  (forall w, uE E b1 <= w < uE E b1 + uE E s1 + uE E s2 -> in_shadow w = false) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b1 (ladd s1 s2) RW TEmpty :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b1 b2 s1 s2 l2 Hd HS Hgeo Hnsh.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hr1 : forall E1, rsz E1 (RG b1 s1 RW TEmpty) = uE E1 s1) by reflexivity.
  assert (Hr2 : forall E1, rsz E1 (RG b2 s2 RW TEmpty) = uE E1 s2) by reflexivity.
  assert (Hr : forall E1, agree (s_next S) E E1 -> rsz E1 (RG b1 (ladd s1 s2) RW TEmpty) = uE E1 s1 + uE E1 s2).
  { intros E1 Ha. destruct (Hgeo E1 Ha) as (G1 & G2 & G3 & _). unfold rsz. cbn [rg_size]. rewrite lden_ladd, bv_add_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold uE in *. lia. }
  destruct (Hgeo E (agree_refl _ _)) as (Z1 & Z2 & Z64 & HA0).
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b1 (ladd s1 s2) RW TEmpty :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr1, Hr2, (Hr E (agree_refl _ _)).
    unfold uE in HA0. rewrite HA0. unfold uE.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + bv_unsigned (lden E s1) <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b1) + bv_unsigned (lden E s1) \/ bv_unsigned (lden E b1) + bv_unsigned (lden E s1) + bv_unsigned (lden E s2) <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + (bv_unsigned (lden E s1) + bv_unsigned (lden E s2)) <= bv_unsigned x))
      by (unfold uE in Z1, Z2; lia).
    split; [intros (A & B & C & D); exact (conj A (conj (proj1 Heq (conj B C)) D)) |
            intros (A & B & D); destruct (proj2 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D)))]. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m (RG b1 s1 RW TEmpty) -> rg_ok segs E' m (RG b2 s2 RW TEmpty) ->
            rg_ok segs E' m (RG b1 (ladd s1 s2) RW TEmpty)).
  { intros E' m Ha H1 H2. destruct (Hgeo E' Ha) as (G1 & G2 & G3 & HA). unfold uE in HA, G1, G2, G3.
    unfold rg_ok in H1, H2 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr1 in H1. rewrite Hr2 in H2. rewrite (Hr E' Ha).
    unfold uE in *. destruct H1 as (P1 & F1 & B1 & _). destruct H2 as (P2 & F2 & B2 & _). rewrite HA in F2, B2.
    split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Z_lt_le_dec i (bv_unsigned (lden E' s1))) as [X|X]; [exact (B1 i ltac:(lia))|].
      specialize (B2 (i - bv_unsigned (lden E' s1)) ltac:(lia)).
      replace (bv_unsigned (lden E' b1) + bv_unsigned (lden E' s1) + (i - bv_unsigned (lden E' s1))) with (bv_unsigned (lden E' b1) + i) in B2 by lia. exact B2.
    - intros p v Hp. rewrite tget_empty in Hp. discriminate. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR1 A5r']; subst. inversion A5r' as [|? ? HR2 A5r'']; subst.
    destruct (Hgeo E' Ha) as (G1 & G2 & G3 & HA). unfold uE in HA, G1, G2, G3.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR1 HR2) | exact A5r''].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a [D2b D2c]].
      inversion D2a as [|? ? D12 D1l2]; subst.
      refine (conj D1 (conj (conj _ D2c) _)).
      * rewrite Forall_forall in D1l2, D2b |- *. intros R0 HR0. specialize (D1l2 R0 HR0). specialize (D2b R0 HR0).
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; right; right; right; exact HR0) Ha) as Hp0.
        unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D1l2. rewrite Hr2 in D2b. rewrite (Hr E' Ha). unfold uE in *. rewrite HA in D2b. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. inversion D3b as [|? ? D3c D3d]; subst.
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; left; exact HR0) Ha) as Hp0.
        constructor; [|exact D3d]. unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D3a. rewrite Hr2 in D3c. rewrite (Hr E' Ha).
        unfold uE in *. rewrite HA in D3c. lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in Hbr as [HbR2 Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR HsR]. apply andb_prop in HbR2 as [_ HsR2]. rewrite HbR, (lwf_ladd _ _ _ HsR HsR2). reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl1 Hrl2']; subst. inversion Hrl2' as [|? ? HRl2 Hrl2'']; subst.
    apply Forall_app. split; [exact Hrl1|]. constructor; [|exact Hrl2''].
    unfold rl_ok in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in HRl1. rewrite Hr2 in HRl2. rewrite (Hr E (agree_refl _ _)). split; [lia|]. left.
    destruct HRl1 as (_ & [Happ1 | (_ & _ & Hsh1)]); [| specialize (Hsh1 (uE E b1) ltac:(lia)); rewrite (Hnsh (uE E b1) ltac:(lia)) in Hsh1; destruct Hsh1; discriminate].
    destruct HRl2 as (_ & [Happ2 | (_ & _ & Hsh2)]); [| rewrite HA0 in Hsh2; specialize (Hsh2 (uE E b1 + uE E s1) ltac:(lia)); rewrite (Hnsh (uE E b1 + uE E s1) ltac:(lia)) in Hsh2; destruct Hsh2; discriminate].
    intros w Hw. destruct (Z_lt_le_dec w (uE E b1 + uE E s1)) as [X|X]; [apply Happ1; lia | apply Happ2; rewrite HA0; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_merge_sh : forall E S M ms model l1 b1 b2 s1 s2 l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b1 s1 RW TEmpty :: RG b2 s2 RW TEmpty :: l2 ->
  (forall E', agree (s_next S) E E' -> 0 < uE E' s1 /\ 0 < uE E' s2 /\ uE E' s1 + uE E' s2 < two64 /\ uE E' b2 = uE E' b1 + uE E' s1) ->
  (forall w, uE E b1 <= w < uE E b1 + uE E s1 + uE E s2 -> in_shadow w = true) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b1 (ladd s1 s2) RW TEmpty :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b1 b2 s1 s2 l2 Hd HS Hgeo Hsh.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hr1 : forall E1, rsz E1 (RG b1 s1 RW TEmpty) = uE E1 s1) by reflexivity.
  assert (Hr2 : forall E1, rsz E1 (RG b2 s2 RW TEmpty) = uE E1 s2) by reflexivity.
  assert (Hr : forall E1, agree (s_next S) E E1 -> rsz E1 (RG b1 (ladd s1 s2) RW TEmpty) = uE E1 s1 + uE E1 s2).
  { intros E1 Ha. destruct (Hgeo E1 Ha) as (G1 & G2 & G3 & _). unfold rsz. cbn [rg_size]. rewrite lden_ladd, bv_add_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold uE in *. lia. }
  destruct (Hgeo E (agree_refl _ _)) as (Z1 & Z2 & Z64 & HA0).
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b1 (ladd s1 s2) RW TEmpty :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr1, Hr2, (Hr E (agree_refl _ _)).
    unfold uE in HA0. rewrite HA0. unfold uE.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + bv_unsigned (lden E s1) <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b1) + bv_unsigned (lden E s1) \/ bv_unsigned (lden E b1) + bv_unsigned (lden E s1) + bv_unsigned (lden E s2) <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + (bv_unsigned (lden E s1) + bv_unsigned (lden E s2)) <= bv_unsigned x))
      by (unfold uE in Z1, Z2; lia).
    split; [intros (A & B & C & D); exact (conj A (conj (proj1 Heq (conj B C)) D)) |
            intros (A & B & D); destruct (proj2 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D)))]. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m (RG b1 s1 RW TEmpty) -> rg_ok segs E' m (RG b2 s2 RW TEmpty) ->
            rg_ok segs E' m (RG b1 (ladd s1 s2) RW TEmpty)).
  { intros E' m Ha H1 H2. destruct (Hgeo E' Ha) as (G1 & G2 & G3 & HA). unfold uE in HA, G1, G2, G3.
    unfold rg_ok in H1, H2 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr1 in H1. rewrite Hr2 in H2. rewrite (Hr E' Ha).
    unfold uE in *. destruct H1 as (P1 & F1 & B1 & _). destruct H2 as (P2 & F2 & B2 & _). rewrite HA in F2, B2.
    split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Z_lt_le_dec i (bv_unsigned (lden E' s1))) as [X|X]; [exact (B1 i ltac:(lia))|].
      specialize (B2 (i - bv_unsigned (lden E' s1)) ltac:(lia)).
      replace (bv_unsigned (lden E' b1) + bv_unsigned (lden E' s1) + (i - bv_unsigned (lden E' s1))) with (bv_unsigned (lden E' b1) + i) in B2 by lia. exact B2.
    - intros p v Hp. rewrite tget_empty in Hp. discriminate. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR1 A5r']; subst. inversion A5r' as [|? ? HR2 A5r'']; subst.
    destruct (Hgeo E' Ha) as (G1 & G2 & G3 & HA). unfold uE in HA, G1, G2, G3.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR1 HR2) | exact A5r''].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a [D2b D2c]].
      inversion D2a as [|? ? D12 D1l2]; subst.
      refine (conj D1 (conj (conj _ D2c) _)).
      * rewrite Forall_forall in D1l2, D2b |- *. intros R0 HR0. specialize (D1l2 R0 HR0). specialize (D2b R0 HR0).
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; right; right; right; exact HR0) Ha) as Hp0.
        unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D1l2. rewrite Hr2 in D2b. rewrite (Hr E' Ha). unfold uE in *. rewrite HA in D2b. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. inversion D3b as [|? ? D3c D3d]; subst.
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; left; exact HR0) Ha) as Hp0.
        constructor; [|exact D3d]. unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D3a. rewrite Hr2 in D3c. rewrite (Hr E' Ha).
        unfold uE in *. rewrite HA in D3c. lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in Hbr as [HbR2 Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR HsR]. apply andb_prop in HbR2 as [_ HsR2]. rewrite HbR, (lwf_ladd _ _ _ HsR HsR2). reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl1 Hrl2']; subst. inversion Hrl2' as [|? ? HRl2 Hrl2'']; subst.
    apply Forall_app. split; [exact Hrl1|]. constructor; [|exact Hrl2''].
    unfold rl_ok in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in HRl1. rewrite Hr2 in HRl2. rewrite (Hr E (agree_refl _ _)). split; [lia|]. right.
    destruct HRl1 as (_ & [Happ1 | (Hso1 & Hap1 & Hsh1)]);
      [exfalso; destruct (Happ1 (uE E b1) ltac:(lia)) as (_ & X & _); rewrite (Hsh (uE E b1) ltac:(lia)) in X; discriminate|].
    destruct HRl2 as (_ & [Happ2 | (Hso2 & Hap2 & Hsh2)]);
      [exfalso; rewrite HA0 in Happ2; destruct (Happ2 (uE E b1 + uE E s1) ltac:(lia)) as (_ & X & _); rewrite (Hsh (uE E b1 + uE E s1) ltac:(lia)) in X; discriminate|].
    rewrite HA0 in Hap2, Hsh2. split; [exact Hso1|]. split.
    + intros x Hx. destruct (Z_lt_le_dec x (8 * (uE E b1 - SH_OFF + uE E s1))) as [X|X]; [apply Hap1; lia | apply Hap2; lia].
    + intros w Hw. destruct (Z_lt_le_dec w (uE E b1 + uE E s1)) as [X|X]; [apply Hsh1; lia | apply Hsh2; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.
End MergeS.
(* [comment removed for export] *)
End AsanMergeS.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint nodup_b (l : list nat) : bool :=
  match l with [] => true | x :: xs => (negb (existsb (Nat.eqb x) xs) && nodup_b xs)%bool end.
Definition perm_ix_ok (n : nat) (ix : list nat) : bool :=
  (Nat.eqb (length ix) n && forallb (fun k => Nat.ltb k n) ix && nodup_b ix)%bool.

Lemma nodup_b_sound : forall l, nodup_b l = true -> List.NoDup l.
Proof.
  induction l as [|x xs IH]; intros H; [apply List.NoDup_nil|]. cbn [nodup_b] in H. apply andb_prop in H as [H1 H2].
  apply List.NoDup_cons; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (X : existsb (Nat.eqb x) xs = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Nat.eqb_refl]).
  rewrite X in H1. discriminate.
Qed.
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), List.map (fun k => nth k l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|]. cbn [length seq List.map nth]. f_equal.
  rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.
Lemma perm_ix_sound : forall {A} (l : list A) (d : A) ix, perm_ix_ok (length l) ix = true -> Permutation l (List.map (fun k => nth k l d) ix).
Proof.
  intros A l d ix H. unfold perm_ix_ok in H. apply andb_prop in H as [H Hnd]. apply andb_prop in H as [Hlen Hlt].
  apply Nat.eqb_eq in Hlen. rewrite forallb_forall in Hlt. apply nodup_b_sound in Hnd.
  rewrite <- (map_nth_seq0 l d) at 1. apply Permutation_map. apply NoDup_Permutation; [apply seq_NoDup | exact Hnd |].
  assert (Hinc : incl ix (seq 0 (length l))) by (intros x Hx; apply in_seq; specialize (Hlt x Hx); apply Nat.ltb_lt in Hlt; lia).
  pose proof (@NoDup_length_incl nat ix (seq 0 (length l)) Hnd ltac:(rewrite length_seq; lia) Hinc) as Hinc2.
  intros x. split; [apply Hinc2 | apply Hinc].
Qed.

(* [comment removed for export] *)
Section Entry.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_entry : forall E S M ms model l1 R l2 R1 R2 o z ix P0 n σ Sp,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  s_rgs S = l1 ++ R :: l2 -> rg_size R = lconst z -> 0 < o < z -> z < two64 ->
  rg_sub_ok R R1 0 = true -> rg_sub_ok R R2 o = true -> csz R1 = o -> csz R2 = z - o ->
  perm_ix_ok (length (l1 ++ R1 :: R2 :: l2)) ix = true ->
  entails (with_rgs S (List.map (fun k => nth k (l1 ++ R1 :: R2 :: l2) R) ix)) (mrg (sst_shift n P0) Sp) σ = true ->
  state_wf (mrg (sst_shift n P0) Sp) = true -> params_fixed σ (pos_below (s_next S)) = true ->
  (s_next S <= n + s_next P0)%positive ->
  DEN segs LIMIT model0 mem0 (ecomp E σ) (mrg (sst_shift n P0) Sp) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 R l2 R1 R2 o z ix P0 n σ Sp Hd HS Hz Ho Hz64 Hs1 Hs2 Hc1 Hc2 Hix Hent Hwp Hpf Hn.
  pose proof (den_split segs LIMIT model0 mem0 E S M ms model l1 R l2 R1 R2 o z Hd HS Hz Ho Hz64 Hs1 Hs2 Hc1 Hc2) as Hd1.
  pose proof (perm_ix_sound (l1 ++ R1 :: R2 :: l2) R ix Hix) as HP.
  pose proof (den_perm segs LIMIT model0 mem0 E _ M ms model _ Hd1 HP) as Hd2.
  cbn [with_rgs s_rgs] in Hd2.
  change (with_rgs (with_rgs S (l1 ++ R1 :: R2 :: l2)) (List.map (fun k => nth k (l1 ++ R1 :: R2 :: l2) R) ix))
    with (with_rgs S (List.map (fun k => nth k (l1 ++ R1 :: R2 :: l2) R) ix)) in Hd2.
  apply (den_ent segs LIMIT model0 mem0 E _ _ M ms model σ (s_next S) Hd2 Hent Hwp Hpf); [|exact Hn].
  exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem den_entry2 : forall E S M ms model sts l ix P0 n σ Sp,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  steps_rgs (s_next S) (s_facts S) (s_rgs S) sts = Some l ->
  perm_ix_ok (length l) ix = true ->
  entails (with_rgs S (List.map (fun k => nth k l (RG lc0 lc0 RW TEmpty)) ix)) (mrg (sst_shift n P0) Sp) σ = true ->
  state_wf (mrg (sst_shift n P0) Sp) = true -> params_fixed σ (pos_below (s_next S)) = true ->
  (s_next S <= n + s_next P0)%positive ->
  DEN segs LIMIT model0 mem0 (ecomp E σ) (mrg (sst_shift n P0) Sp) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model sts l ix P0 n σ Sp Hd Hst Hix Hent Hwp Hpf Hn.
  pose proof (den_steps segs LIMIT model0 mem0 sts E S M ms model l Hd Hst) as Hd1.
  pose proof (perm_ix_sound l (RG lc0 lc0 RW TEmpty) ix Hix) as HP.
  pose proof (den_perm segs LIMIT model0 mem0 E _ M ms model _ Hd1 HP) as Hd2.
  change (with_rgs (with_rgs S l) (List.map (fun k => nth k l (RG lc0 lc0 RW TEmpty)) ix))
    with (with_rgs S (List.map (fun k => nth k l (RG lc0 lc0 RW TEmpty)) ix)) in Hd2.
  apply (den_ent segs LIMIT model0 mem0 E _ _ M ms model σ (s_next S) Hd2 Hent Hwp Hpf); [|exact Hn].
  exact (dn_wf _ _ _ _ _ _ _ _ _ Hd).
Qed.
End Entry.
(* [comment removed for export] *)
