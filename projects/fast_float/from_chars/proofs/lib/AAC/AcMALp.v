(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxSubst FxEnt FxCall FxFacts FxPlan FxLoop FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg AcEntry AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcSteps.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps.AcP0gen.
Import ListNotations.

Module FxRgNodes.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep FxChEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcMrg AcCarve.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition track1_rg (R : region) (x : positive) : option (region * Z) :=
  match is_const (rg_size R), tget 1%positive (rg_cont R) with
  | Some sz, None =>
      if Z.eqb sz 1 then
        match rg_kind R with
        | RW => Some (RG (rg_base R) (rg_size R) RZ (tset 1%positive (BV (lvar x) 0) (rg_cont R)), 255)
        | RZ => Some (RG (rg_base R) (rg_size R) RZ (tset 1%positive (BV (lvar x) 0) (rg_cont R)), 0)
        | _ => None
        end
      else None
  | _, _ => None
  end.
Definition track1_st (S : sst) (i : nat) (R' : region) : sst :=
  SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (Pos.succ (s_next S)) (s_resv S).
Definition track1_post (S : sst) (i : nat) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match track1_rg R (s_next S) with
              | Some (R', hi) => Some (add_fact (track1_st S i R') (FRange (lvar (s_next S)) 0 hi))
              | None => None
              end
  | None => None
  end.

Section RgN.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Lemma bden_bv_byte : forall E x (b : byte), E x = Z_to_bv 64 (bv_unsigned b) -> bden E (BV (lvar x) 0) = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E x b Hx. cbn [bden]. rewrite lden_lvar, Hx. pose proof (bv_unsigned_in_range _ b) as Rb. unfold bv_modulus in Rb.
  change (2 ^ Z.of_N 8) with 256 in Rb.
  rewrite u_small64 by (unfold two64; lia). rewrite Z.mul_0_r, Z.shiftr_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

#[using="Type"] Theorem den_track1 : forall S M i S' E ms model, track1_post S i = Some S' ->
  DEN segs LIMIT model0 mem0 E S M ms model ->
  exists E', agree (s_next S) E E' /\ DEN segs LIMIT model0 mem0 E' S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M i S' E ms model Hp Hd. unfold track1_post in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate].
  destruct (track1_rg R (s_next S)) as [[R' hi]|] eqn:Hr; [|discriminate]. injection Hp as <-.
  set (x := s_next S) in *.
  unfold track1_rg in Hr. destruct (is_const (rg_size R)) as [sz|] eqn:Hs; [|discriminate].
  destruct (tget 1%positive (rg_cont R)) eqn:Ht1; [discriminate|]. destruct (Z.eqb sz 1) eqn:Hz1; [|discriminate]. apply Z.eqb_eq in Hz1. subst sz.
  assert (Hrs : forall E0, rsz E0 R = 1).
  { intros E0. unfold rsz. destruct (is_const_sound E0 _ 1 Hs) as [H1 H2]. rewrite H1. apply u_small64. exact H2. }
  (* [comment removed for export] *)
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG0 & _).
  pose proof (proj1 (Forall_nth' _ _) HG0 i R Hi) as HR0. destruct HR0 as (_ & _ & Hby0 & _).
  specialize (Hby0 0 ltac:(rewrite Hrs; lia)).
  set (m := ms_mem (restrict (Hof E M model) ms)) in *.
  set (A := bv_unsigned (lden E (rg_base R))) in *.
  assert (Hb : exists b : byte, rd1 segs m (Z_to_bv 64 (A + 0)) = Some b /\ (rg_kind R = RZ -> b = Z_to_bv 8 0) /\
                 wview segs m (Z_to_bv 64 (A + 0)) <> None /\ (rg_kind R = RW \/ rg_kind R = RZ)).
  { destruct (rg_kind R) eqn:Hk; try discriminate.
    - destruct Hby0 as [Hrd Hwv]. destruct (rd1 segs m (Z_to_bv 64 (A + 0))) as [b|] eqn:Hrb; [|congruence].
      exists b. split; [reflexivity|]. split; [discriminate|]. split; [exact Hwv | left; reflexivity].
    - destruct Hby0 as [[Hrd Hwv] Hz]. exists (Z_to_bv 8 0). split; [apply Hz; unfold okey; exact Ht1|]. split; [reflexivity|]. split; [exact Hwv | right; reflexivity]. }
  destruct Hb as (b & Hrb & Hbz & Hwv & Hkind).
  set (E1 := upd E x (Z_to_bv 64 (bv_unsigned b))).
  assert (Ha1 : agree x E E1) by exact (agree_upd x E _).
  assert (HE1 : E1 x = Z_to_bv 64 (bv_unsigned b)) by (unfold E1, upd; rewrite Pos.eqb_refl; reflexivity).
  exists E1. split; [exact Ha1|].
  assert (HR'eq : R' = RG (rg_base R) (rg_size R) RZ (tset 1%positive (BV (lvar x) 0) (rg_cont R)) /\ (hi = 255 \/ (hi = 0 /\ rg_kind R = RZ))).
  { destruct (rg_kind R); try discriminate; injection Hr as <- <-; (split; [reflexivity|]); [left; reflexivity | right; split; reflexivity]. }
  destruct HR'eq as [-> Hhi]. clear Hr.
  set (R' := RG (rg_base R) (rg_size R) RZ (tset 1%positive (BV (lvar x) 0) (rg_cont R))) in *.
  pose proof (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) as Hd1.
  pose proof (den_bump segs LIMIT model0 mem0 E1 S M ms model (Pos.succ x) Hd1 ltac:(fold x; lia)) as Hd2.
  assert (HH : Hof E1 M model = Hof E M model).
  { unfold Hof. rewrite (allowA_agree (s_next S) E E1 M (dn_wf _ _ _ _ _ _ _ _ _ Hd) Ha1). reflexivity. }
  apply den_addfact.
  - (* [comment removed for export] *)
    destruct Hd2 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind2 Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
    cbn [bump s_next s_rgs s_pc s_regs s_facts s_resv] in *.
    assert (Hb' : rg_base R' = rg_base R) by reflexivity. assert (Hs' : rg_size R' = rg_size R) by reflexivity.
    assert (Hshape : shape (s_rgs (track1_st S i R')) = shape (s_rgs (bump S (Pos.succ x)))) by (cbn [track1_st bump s_rgs]; exact (shape_upd (s_rgs S) i R' R Hi Hb' Hs')).
    assert (HbwR : lwf x (rg_base R) = true).
    { pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hb0. unfold bases_wf in Hb0. rewrite forallb_forall in Hb0.
      destruct (andb_prop _ _ (Hb0 R (nth_error_In _ _ Hi))) as [X _]. exact X. }
    constructor; try assumption.
    + intros E'' Ha''. cbn [track1_st s_next] in Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
      unfold sden0. cbn [track1_st s_pc s_regs s_rgs s_facts s_resv].
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
      * apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
        destruct (Nat.eq_dec j i) as [->|Hne].
        -- rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
           pose proof (proj1 (Forall_nth' _ _) HG i R Hi) as (Q1 & Q2 & Q3 & Q4).
           assert (HA'' : bv_unsigned (lden E'' (rg_base R)) = A).
           { unfold A. f_equal. apply (lden_agree_wf x E E'' _ HbwR). intros y Hy. rewrite (Ha1 y Hy). apply Ha''. lia. }
           assert (HEx : E'' x = Z_to_bv 64 (bv_unsigned b)) by (rewrite <- (Ha'' x ltac:(lia)); exact HE1).
           assert (Hrs' : rsz E'' R' = 1) by (unfold rsz, R'; cbn [rg_size]; exact (Hrs E'')).
           unfold rg_ok. cbv zeta. change (rg_kind R') with RZ. change (rg_base R') with (rg_base R).
           change (rg_cont R') with (tset 1%positive (BV (lvar x) 0) (rg_cont R)). cbv iota.
           rewrite Hrs'. rewrite (Hrs E'') in Q2. rewrite HA'' in *. rewrite HH in *. fold m.
           split; [lia|]. split; [exact Q2|]. split.
           ++ intros i0 Hi0. assert (i0 = 0) by lia. subst i0. split; [split; [rewrite Hrb; discriminate | exact Hwv]|].
              intros Hn. change (okey 0) with 1%positive in Hn. rewrite tget_tset_same in Hn. discriminate.
           ++ intros p v Hpv. destruct (Pos.eq_dec p 1%positive) as [->|Hp1].
              ** rewrite tget_tset_same in Hpv. injection Hpv as <-. split; [lia|]. rewrite (bden_bv_byte E'' x b HEx).
                 change (Z.pos 1 - 1) with 0. exact Hrb.
              ** rewrite tget_tset_other in Hpv by (intros X; apply Hp1; symmetry; exact X). destruct (Q4 p v Hpv) as [Q5 Q6]. rewrite (Hrs E'') in Q5. split; [exact Q5|]. exact Q6.
        -- rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
      * eapply rgs_disj_upd; [exact Hi | exact Hb' | exact Hs' | exact HD].
    + eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [track1_st bump s_next]. lia.
    + intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
      exact (outside_agree_shape (Pos.succ x) E1 E1 (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
    + exact (rl_ok_agree_shape (Pos.succ x) E1 E1 model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
    + intros p Hp0 w Hw0. destruct (Hfrz p Hp0 w Hw0) as (X1 & X2 & X3). split; [exact X1|]. split; [|exact X3].
      exact (outside_agree_shape (Pos.succ x) E1 E1 _ (s_rgs S) _ ltac:(eapply bases_wf_shape; [|exact Hshape|exact Hbw]; lia) (agree_refl _ _) (eq_sym Hshape) X2).
    + intros p Hp0 w Hw0. destruct (Hown p Hp0 w Hw0) as [Hv Hm0]. split; [exact Hv|]. intros Ho'. apply Hm0.
      exact (outside_agree_shape (Pos.succ x) E1 E1 (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
  - intros E'' Ha''. cbn [track1_st s_next] in Ha''. cbn [fact_ok]. rewrite lden_lvar. rewrite <- (Ha'' x ltac:(lia)), HE1.
    pose proof (bv_unsigned_in_range _ b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    rewrite u_small64 by (unfold two64; lia).
    destruct Hhi as [->|[-> Hkz]]; [lia|]. rewrite (Hbz Hkz). change (bv_unsigned (Z_to_bv 8 0)) with 0. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_merge_tz : forall E S M ms model l1 b1 b2 s1 c s2 cont l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b1 s1 RZ cont :: RG b2 s2 RZ TEmpty :: l2 ->
  is_const s1 = Some c -> 1 <= c ->
  (forall E', agree (s_next S) E E' -> 0 < uE E' s2 /\ c + uE E' s2 < two64 /\ uE E' b2 = uE E' b1 + c) ->
  (forall w, uE E b1 <= w < uE E b1 + c + uE E s2 -> in_shadow w = true) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b1 (laddc s2 c) RZ cont :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b1 b2 s1 c s2 cont l2 Hd HS Hs1 Hc1 Hgeo Hsh.
  assert (Hc : 1 <= c < two64) by (destruct (is_const_sound E s1 c Hs1) as [_ X]; lia).
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hr1 : forall E1, rsz E1 (RG b1 s1 RZ cont) = c).
  { intros E1. unfold rsz. cbn [rg_size]. destruct (is_const_sound E1 s1 c Hs1) as [X _]. rewrite X. apply u_small64. lia. }
  assert (Hr2 : forall E1, rsz E1 (RG b2 s2 RZ TEmpty) = uE E1 s2) by reflexivity.
  assert (Hr : forall E1, agree (s_next S) E E1 -> rsz E1 (RG b1 (laddc s2 c) RZ cont) = c + uE E1 s2).
  { intros E1 Ha. destruct (Hgeo E1 Ha) as (G1 & G2 & _). unfold rsz. cbn [rg_size]. rewrite lden_laddc. unfold uE in *.
    rewrite u_small64 by lia. lia. }
  destruct (Hgeo E (agree_refl _ _)) as (Z2 & Z64 & HA0).
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b1 (laddc s2 c) RZ cont :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr1, Hr2, (Hr E (agree_refl _ _)).
    unfold uE in HA0. rewrite HA0. unfold uE in *.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + c <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b1) + c \/ bv_unsigned (lden E b1) + c + bv_unsigned (lden E s2) <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + (c + bv_unsigned (lden E s2)) <= bv_unsigned x)) by lia.
    split; [intros (A & B & C & D); exact (conj A (conj (proj1 Heq (conj B C)) D)) |
            intros (A & B & D); destruct (proj2 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D)))]. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m (RG b1 s1 RZ cont) -> rg_ok segs E' m (RG b2 s2 RZ TEmpty) ->
            rg_ok segs E' m (RG b1 (laddc s2 c) RZ cont)).
  { intros E' m Ha H1 H2. destruct (Hgeo E' Ha) as (G1 & G2 & HA). unfold uE in HA, G1, G2.
    unfold rg_ok in H1, H2 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr1 in H1. rewrite Hr2 in H2. rewrite (Hr E' Ha).
    unfold uE in *. destruct H1 as (P1 & F1 & B1 & C1). destruct H2 as (P2 & F2 & B2 & _). rewrite HA in F2, B2.
    split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Z_lt_le_dec i c) as [X|X]; [exact (B1 i ltac:(lia))|].
      specialize (B2 (i - c) ltac:(lia)).
      replace (bv_unsigned (lden E' b1) + c + (i - c)) with (bv_unsigned (lden E' b1) + i) in B2 by lia.
      destruct B2 as [B2a B2b]. split; [exact B2a|]. intros _. apply B2b. apply tget_empty.
    - intros p v Hp. destruct (C1 p v Hp) as [C1a C1b]. split; [lia | exact C1b]. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR1 A5r']; subst. inversion A5r' as [|? ? HR2 A5r'']; subst.
    destruct (Hgeo E' Ha) as (G1 & G2 & HA). unfold uE in HA, G1, G2.
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
    apply andb_prop in HbR as [HbR HsR]. apply andb_prop in HbR2 as [_ HsR2]. rewrite HbR, (lwf_laddc _ _ c HsR2). reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl1 Hrl2']; subst. inversion Hrl2' as [|? ? HRl2 Hrl2'']; subst.
    apply Forall_app. split; [exact Hrl1|]. constructor; [|exact Hrl2''].
    unfold rl_ok in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in HRl1. rewrite Hr2 in HRl2. rewrite (Hr E (agree_refl _ _)). split; [lia|]. right.
    destruct HRl1 as (_ & [Happ1 | (Hso1 & Hap1 & Hsh1)]).
    { exfalso. destruct (Happ1 (uE E b1) ltac:(lia)) as (_ & Hns & _). rewrite (Hsh (uE E b1) ltac:(lia)) in Hns. discriminate. }
    destruct HRl2 as (_ & [Happ2 | (Hso2 & Hap2 & Hsh2)]).
    { exfalso. destruct (Happ2 (uE E b2) ltac:(lia)) as (_ & Hns & _). rewrite (Hsh (uE E b2) ltac:(rewrite HA0; lia)) in Hns. discriminate. }
    rewrite HA0 in Hap2, Hsh2. split; [exact Hso1|]. split.
    + intros x Hx. destruct (Z_lt_le_dec x (8 * (uE E b1 - SH_OFF + c))) as [X|X]; [apply Hap1; lia | apply Hap2; lia].
    + intros w Hw. destruct (Z_lt_le_dec w (uE E b1 + c)) as [X|X]; [apply Hsh1; lia | apply Hsh2; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_split_zz : forall E S M ms model l1 b z m t l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b z RZ TEmpty :: l2 ->
  lwf (s_next S) m = true -> lwf (s_next S) t = true ->
  (forall E', agree (s_next S) E E' -> 0 < uE E' m /\ 0 < uE E' t /\ uE E' m + uE E' t = uE E' z /\ uE E' b + uE E' z < two64) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b m RZ TEmpty :: RG (ladd b m) t RZ TEmpty :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b z m t l2 Hd HS Hwm Hwt Hgeo.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hr0 : forall E1, rsz E1 (RG b z RZ TEmpty) = uE E1 z) by reflexivity.
  assert (Hr1 : forall E1, rsz E1 (RG b m RZ TEmpty) = uE E1 m) by reflexivity.
  assert (Hr2 : forall E1, rsz E1 (RG (ladd b m) t RZ TEmpty) = uE E1 t) by reflexivity.
  assert (Hb2 : forall E1, agree (s_next S) E E1 -> uE E1 (ladd b m) = uE E1 b + uE E1 m).
  { intros E1 Ha. destruct (Hgeo E1 Ha) as (G1 & G2 & G3 & G4). unfold uE. apply ladd_u2. unfold uE in *. lia. }
  destruct (Hgeo E (agree_refl _ _)) as (Z1 & Z2 & Z3 & Z4). pose proof (Hb2 E (agree_refl _ _)) as HB0.
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b m RZ TEmpty :: RG (ladd b m) t RZ TEmpty :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr0, Hr1, Hr2.
    unfold uE in HB0. rewrite HB0. unfold uE in *.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b) \/ bv_unsigned (lden E b) + bv_unsigned (lden E z) <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b) \/ bv_unsigned (lden E b) + bv_unsigned (lden E m) <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b) + bv_unsigned (lden E m) \/ bv_unsigned (lden E b) + bv_unsigned (lden E m) + bv_unsigned (lden E t) <= bv_unsigned x)) by lia.
    split; [intros (A & B & D); destruct (proj1 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D))) |
            intros (A & B & C & D); exact (conj A (conj (proj2 Heq (conj B C)) D))]. }
  assert (Hok : forall E' mm, agree (s_next S) E E' -> rg_ok segs E' mm (RG b z RZ TEmpty) ->
            rg_ok segs E' mm (RG b m RZ TEmpty) /\ rg_ok segs E' mm (RG (ladd b m) t RZ TEmpty)).
  { intros E' mm Ha H0. destruct (Hgeo E' Ha) as (G1 & G2 & G3 & G4). pose proof (Hb2 E' Ha) as HB. unfold uE in HB, G1, G2, G3, G4.
    unfold rg_ok in H0 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr0 in H0. rewrite Hr1, Hr2.
    unfold uE in *. destruct H0 as (P0 & F0 & B0 & _). rewrite HB. split.
    - split; [lia|]. split; [lia|]. split; [intros i Hi; exact (B0 i ltac:(lia)) | intros p v Hp; rewrite tget_empty in Hp; discriminate].
    - split; [lia|]. split; [lia|]. split; [|intros p v Hp; rewrite tget_empty in Hp; discriminate].
      intros i Hi. specialize (B0 (bv_unsigned (lden E' m) + i) ltac:(lia)).
      replace (bv_unsigned (lden E' b) + (bv_unsigned (lden E' m) + i)) with (bv_unsigned (lden E' b) + bv_unsigned (lden E' m) + i) in B0 by lia.
      destruct B0 as [B0a B0b]. split; [exact B0a|]. intros _. apply B0b. apply tget_empty. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR0 A5r']; subst.
    destruct (Hgeo E' Ha) as (G1 & G2 & G3 & G4). pose proof (Hb2 E' Ha) as HB. unfold uE in HB, G1, G2, G3, G4.
    destruct (Hok E' _ Ha HR0) as [HK1 HK2].
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact HK1|]. constructor; [exact HK2 | exact A5r'].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a D2b].
      refine (conj D1 (conj _ _)).
      * cbn [rgs_disj]. split; [|split; [|exact D2b]].
        -- constructor.
           ++ unfold rg_disj. cbv zeta. cbn [rg_base]. rewrite Hr1, Hr2. unfold uE. rewrite HB. left. lia.
           ++ rewrite Forall_forall in D2a |- *. intros R0 HR0'. specialize (D2a R0 HR0').
              unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr0 in D2a. rewrite Hr1. unfold uE in *. lia.
        -- rewrite Forall_forall in D2a |- *. intros R0 HR0'. specialize (D2a R0 HR0').
           unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr0 in D2a. rewrite Hr2. unfold uE in *. rewrite HB. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0'. specialize (D3 R0 HR0'). inversion D3 as [|? ? D3a D3b]; subst.
        constructor; [|constructor; [|exact D3b]]; unfold rg_disj in *; cbv zeta in *; cbn [rg_base] in *; rewrite Hr0 in D3a;
          [rewrite Hr1 | rewrite Hr2]; unfold uE in *; [|rewrite HB]; lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR HsR]. rewrite HbR, Hwm, Hwt, (lwf_ladd _ _ _ HbR Hwm). reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl0 Hrl2']; subst.
    apply Forall_app. split; [exact Hrl1|].
    unfold rl_ok in HRl0. cbv zeta in HRl0. cbn [rg_base] in HRl0. rewrite Hr0 in HRl0. destruct HRl0 as (_ & HRl0).
    constructor; [|constructor; [|exact Hrl2']]; unfold rl_ok; cbv zeta; cbn [rg_base]; [rewrite Hr1 | rewrite Hr2, HB0]; (split; [lia|]);
      (destruct HRl0 as [Happ | (Hso & Hap & Hshc)]; [left; intros w Hw; apply Happ; lia | right]).
    + split; [exact Hso|]. split; [intros x Hx; apply Hap; lia | intros w Hw; apply Hshc; lia].
    + split; [lia|]. split; [intros x Hx; apply Hap; lia | intros w Hw; apply Hshc; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_split_ww : forall E S M ms model l1 b z m t l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b z RW TEmpty :: l2 ->
  lwf (s_next S) m = true -> lwf (s_next S) t = true ->
  (forall E', agree (s_next S) E E' -> 0 < uE E' m /\ 0 < uE E' t /\ uE E' m + uE E' t = uE E' z /\ uE E' b + uE E' z < two64) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b m RW TEmpty :: RG (ladd b m) t RW TEmpty :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b z m t l2 Hd HS Hwm Hwt Hgeo.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hr0 : forall E1, rsz E1 (RG b z RW TEmpty) = uE E1 z) by reflexivity.
  assert (Hr1 : forall E1, rsz E1 (RG b m RW TEmpty) = uE E1 m) by reflexivity.
  assert (Hr2 : forall E1, rsz E1 (RG (ladd b m) t RW TEmpty) = uE E1 t) by reflexivity.
  assert (Hb2 : forall E1, agree (s_next S) E E1 -> uE E1 (ladd b m) = uE E1 b + uE E1 m).
  { intros E1 Ha. destruct (Hgeo E1 Ha) as (G1 & G2 & G3 & G4). unfold uE. apply ladd_u2. unfold uE in *. lia. }
  destruct (Hgeo E (agree_refl _ _)) as (Z1 & Z2 & Z3 & Z4). pose proof (Hb2 E (agree_refl _ _)) as HB0.
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b m RW TEmpty :: RG (ladd b m) t RW TEmpty :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr0, Hr1, Hr2.
    unfold uE in HB0. rewrite HB0. unfold uE in *.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b) \/ bv_unsigned (lden E b) + bv_unsigned (lden E z) <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b) \/ bv_unsigned (lden E b) + bv_unsigned (lden E m) <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b) + bv_unsigned (lden E m) \/ bv_unsigned (lden E b) + bv_unsigned (lden E m) + bv_unsigned (lden E t) <= bv_unsigned x)) by lia.
    split; [intros (A & B & D); destruct (proj1 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D))) |
            intros (A & B & C & D); exact (conj A (conj (proj2 Heq (conj B C)) D))]. }
  assert (Hok : forall E' mm, agree (s_next S) E E' -> rg_ok segs E' mm (RG b z RW TEmpty) ->
            rg_ok segs E' mm (RG b m RW TEmpty) /\ rg_ok segs E' mm (RG (ladd b m) t RW TEmpty)).
  { intros E' mm Ha H0. destruct (Hgeo E' Ha) as (G1 & G2 & G3 & G4). pose proof (Hb2 E' Ha) as HB. unfold uE in HB, G1, G2, G3, G4.
    unfold rg_ok in H0 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr0 in H0. rewrite Hr1, Hr2.
    unfold uE in *. destruct H0 as (P0 & F0 & B0 & _). rewrite HB. split.
    - split; [lia|]. split; [lia|]. split; [intros i Hi; exact (B0 i ltac:(lia)) | intros p v Hp; rewrite tget_empty in Hp; discriminate].
    - split; [lia|]. split; [lia|]. split; [|intros p v Hp; rewrite tget_empty in Hp; discriminate].
      intros i Hi. specialize (B0 (bv_unsigned (lden E' m) + i) ltac:(lia)).
      replace (bv_unsigned (lden E' b) + (bv_unsigned (lden E' m) + i)) with (bv_unsigned (lden E' b) + bv_unsigned (lden E' m) + i) in B0 by lia.
      exact B0. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR0 A5r']; subst.
    destruct (Hgeo E' Ha) as (G1 & G2 & G3 & G4). pose proof (Hb2 E' Ha) as HB. unfold uE in HB, G1, G2, G3, G4.
    destruct (Hok E' _ Ha HR0) as [HK1 HK2].
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact HK1|]. constructor; [exact HK2 | exact A5r'].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a D2b].
      refine (conj D1 (conj _ _)).
      * cbn [rgs_disj]. split; [|split; [|exact D2b]].
        -- constructor.
           ++ unfold rg_disj. cbv zeta. cbn [rg_base]. rewrite Hr1, Hr2. unfold uE. rewrite HB. left. lia.
           ++ rewrite Forall_forall in D2a |- *. intros R0 HR0'. specialize (D2a R0 HR0').
              unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr0 in D2a. rewrite Hr1. unfold uE in *. lia.
        -- rewrite Forall_forall in D2a |- *. intros R0 HR0'. specialize (D2a R0 HR0').
           unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr0 in D2a. rewrite Hr2. unfold uE in *. rewrite HB. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0'. specialize (D3 R0 HR0'). inversion D3 as [|? ? D3a D3b]; subst.
        constructor; [|constructor; [|exact D3b]]; unfold rg_disj in *; cbv zeta in *; cbn [rg_base] in *; rewrite Hr0 in D3a;
          [rewrite Hr1 | rewrite Hr2]; unfold uE in *; [|rewrite HB]; lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR HsR]. rewrite HbR, Hwm, Hwt, (lwf_ladd _ _ _ HbR Hwm). reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl0 Hrl2']; subst.
    apply Forall_app. split; [exact Hrl1|].
    unfold rl_ok in HRl0. cbv zeta in HRl0. cbn [rg_base] in HRl0. rewrite Hr0 in HRl0. destruct HRl0 as (_ & HRl0).
    constructor; [|constructor; [|exact Hrl2']]; unfold rl_ok; cbv zeta; cbn [rg_base]; [rewrite Hr1 | rewrite Hr2, HB0]; (split; [lia|]);
      (destruct HRl0 as [Happ | (Hso & Hap & Hshc)]; [left; intros w Hw; apply Happ; lia | right]).
    + split; [exact Hso|]. split; [intros x Hx; apply Hap; lia | intros w Hw; apply Hshc; lia].
    + split; [lia|]. split; [intros x Hx; apply Hap; lia | intros w Hw; apply Hshc; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.
End RgN.
End FxRgNodes.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition sub_cont_ref (c : tree bval) (o z : Z) : tree bval :=
  List.fold_left (fun acc p => let off := Zpos (fst p) - 1 in if (Z.leb o off && Z.ltb off (o + z))%bool then tset (okey (off - o)) (snd p) acc else acc)
    (telems c) TEmpty.
(* [comment removed for export] *)
Fixpoint sub_walk (o z : Z) (t : tree bval) (k : positive -> positive) (acc : tree bval) : tree bval :=
  match t with
  | TEmpty => acc
  | TNode l v r =>
      let a2 := sub_walk o z r (fun p => k (xI p)) (sub_walk o z l (fun p => k (xO p)) acc) in
      match v with
      | Some x => let off := Zpos (k xH) - 1 in if (Z.leb o off && Z.ltb off (o + z))%bool then tset (okey (off - o)) x a2 else a2
      | None => a2
      end
  end.
Definition sub_cont (c : tree bval) (o z : Z) : tree bval := sub_walk o z c (fun p => p) TEmpty.
Lemma sub_walk_eq : forall o z t (k : positive -> positive) rest acc,
  List.fold_left (fun acc p => let off := Zpos (fst p) - 1 in if (Z.leb o off && Z.ltb off (o + z))%bool then tset (okey (off - o)) (snd p) acc else acc)
    (telems_acc t k rest) acc =
  List.fold_left (fun acc p => let off := Zpos (fst p) - 1 in if (Z.leb o off && Z.ltb off (o + z))%bool then tset (okey (off - o)) (snd p) acc else acc)
    rest (sub_walk o z t k acc).
Proof.
  intros o z t. induction t as [|l IHl v r IHr]; intros k rest acc; [reflexivity|]. cbn [telems_acc sub_walk].
  rewrite (IHl (fun p => k (xO p))), (IHr (fun p => k (xI p))). destruct v as [x|]; reflexivity.
Qed.
Lemma sub_cont_eq : forall c o z, sub_cont c o z = sub_cont_ref c o z.
Proof. intros c o z. unfold sub_cont, sub_cont_ref, telems. symmetry. exact (sub_walk_eq o z c (fun p => p) [] TEmpty). Qed.

(* [comment removed for export] *)
Definition inst_rg (σ : tree lin) (n : positive) (R : region) : region :=
  RG (lsubst σ (lshift n (rg_base R))) (lsubst σ (lshift n (rg_size R))) (rg_kind R) TEmpty.

(* [comment removed for export] *)
Fixpoint win_steps (i : nat) (b : lin) (rz : Z) (ps : list region) : list rstep :=
  match ps with
  | [] => []
  | P :: ps' => match ps' with
                | [] => []
                | _ => let z1 := csz P in
                       RSplit i P (RG (laddc b z1) (lconst (rz - z1)) RW TEmpty) z1 :: win_steps (Datatypes.S i) (laddc b z1) (rz - z1) ps'
                end
  end.

(* [comment removed for export] *)
Definition entry_steps (S : sst) (stk : nat) (ps : list region) : option (list rstep) :=
  match nth_error (s_rgs S) stk with
  | Some R =>
      match lin_off (rget (s_regs S) (rk 2)) (rg_base R), is_const (rg_size R) with
      | Some o, Some z =>
          Some (RSplit stk (RG (rg_base R) (lconst o) RW TEmpty) (RG (laddc (rg_base R) o) (lconst (z - o)) (rg_kind R) (sub_cont (rg_cont R) o (z - o))) o ::
                RSplit stk (RG (rg_base R) (lconst (o - 8192)) RW TEmpty) (RG (laddc (rg_base R) (o - 8192)) (lconst 8192) RW TEmpty) (o - 8192) ::
                win_steps (Datatypes.S stk) (laddc (rg_base R) (o - 8192)) 8192 ps)
      | _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition sel_pos (stk np : nat) (i : nat) : nat := if Nat.ltb i stk then i else (i + np + 1)%nat.
Definition perm_ix (len stk np : nat) (sel : list nat) : list nat :=
  let head := List.map (fun k => (stk + 1 + k)%nat) (seq 0 np) ++ List.map (sel_pos stk np) sel in
  head ++ List.filter (fun k => negb (existsb (Nat.eqb k) head)) (seq 0 len).

(* [comment removed for export] *)
Definition KEQ : list Z := [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition eq_facts (n : positive) (regs : tree lin) : list fact :=
  List.fold_right (fun k acc => let l := rget regs (rk k) in
                                match is_const l with Some _ => acc | None => FCond BC_EQ (lvar (n + Pos.of_nat (Z.to_nat k))) l true :: acc end) [] KEQ.

Record entry_res : Type := ER { er_P0 : sst ; er_vs : list positive ; er_n : positive ; er_sig : tree lin ; er_steps : list rstep ;
                               er_ix : list nat ; er_Sp : sst ; er_rgs : list region ; er_split : list region }.

(* [comment removed for export] *)
Definition entry_of (S : sst) (ws : list (Z * Z)) (sel : list nat) (stk : nat) : option entry_res :=
  let spl := rget (s_regs S) (rk 2) in
  let lohi := irange (s_facts S) spl in
  let P0R := p0_of S ws sel (fst lohi) (snd lohi) in
  let P0 := fst P0R in let vs := snd P0R in
  let n := s_next S in
  let σ := sig_of n (s_regs S) vs in
  let ps := List.map (inst_rg σ n) (win_rgs ws) in
  match entry_steps S stk ps with
  | Some sts =>
      match steps_rgs (s_next S) (s_facts S) (s_rgs S) sts with
      | Some l =>
          let ix := perm_ix (length l) stk (length ws) sel in
          let rgs_i := List.map (fun k => nth k l (RG lc0 lc0 RW TEmpty)) ix in
          let rest := skipn (length ws + length sel) rgs_i in
          let Sp := SST (s_pc S) (s_regs S) rest (eq_facts n (s_regs S) ++ s_facts S) (s_next S) (s_resv S) in
          Some (ER P0 vs n σ sts ix Sp rgs_i l)
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition entry_ok (S : sst) (er : entry_res) : bool :=
  (perm_ix_ok (length (er_split er)) (er_ix er) && entails (with_rgs S (er_rgs er)) (mrg (sst_shift (er_n er) (er_P0 er)) (er_Sp er)) (er_sig er) &&
   state_wf (mrg (sst_shift (er_n er) (er_P0 er)) (er_Sp er)) && params_fixed (er_sig er) (pos_below (s_next S)) && state_wf (er_P0 er))%bool.
