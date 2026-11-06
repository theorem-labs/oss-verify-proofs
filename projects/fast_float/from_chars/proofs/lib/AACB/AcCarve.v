(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma Forall_perm' : forall {A} (P : A -> Prop) l l', Permutation l l' -> Forall P l -> Forall P l'.
Proof.
  intros A P l l' HP H. rewrite Forall_forall in *. intros x Hx. apply H. apply (Permutation_in x (Permutation_sym HP) Hx).
Qed.
Lemma forallb_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> forallb f l = true -> forallb f l' = true.
Proof.
  intros A f l l' HP H. rewrite forallb_forall in *. intros x Hx. apply H. apply (Permutation_in x (Permutation_sym HP) Hx).
Qed.
Lemma rgs_disj_perm : forall E l l', Permutation l l' -> rgs_disj E l -> rgs_disj E l'.
Proof.
  intros E l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' HP1 IH1 HP2 IH2]; intros H.
  - exact I.
  - destruct H as [Hx Hl]. split; [exact (Forall_perm' _ _ _ HP Hx) | exact (IH Hl)].
  - destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
    split; [constructor; [exact (rg_disj_sym E _ _ Hyx) | exact Hx]|]. split; [exact Hyl | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.
Lemma outside_perm : forall E l l' x, Permutation l l' -> outside E l x -> outside E l' x.
Proof. intros E l l' x HP H. unfold outside in *. exact (Forall_perm' _ _ _ HP H). Qed.

Section Carve.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_perm : forall E S M ms model rgs', DEN segs LIMIT model0 mem0 E S M ms model -> Permutation (s_rgs S) rgs' ->
  DEN segs LIMIT model0 mem0 E (with_rgs S rgs') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model rgs' Hd HP.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (HPs : Permutation rgs' (s_rgs S)) by exact (Permutation_sym HP).
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + exact (Forall_perm' _ _ _ HP A5).
    + exact (rgs_disj_perm E' _ _ HP A6).
  - unfold bases_wf in *. exact (forallb_perm _ _ _ HP Hbw).
  - intros w Hw Hout Hno Hnb. exact (Hzr w Hw (outside_perm E _ _ _ HPs Hout) Hno Hnb).
  - exact (Forall_perm' _ _ _ HP Hrl).
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (outside_perm E _ _ _ HP X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Hout. exact (Hm (outside_perm E _ _ _ HPs Hout)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_disj_sub_l : forall E R R1 R', rg_disj E R R' -> uE E (rg_base R) <= uE E (rg_base R1) ->
  uE E (rg_base R1) + rsz E R1 <= uE E (rg_base R) + rsz E R -> 0 <= rsz E R1 -> 0 <= rsz E R' -> rg_disj E R1 R'.
Proof. LiaFast.lf_pins LiaFast.u0. intros E R R1 R' H H1 H2 H3 H4. unfold rg_disj, uE in *. cbv zeta in *. lia. Qed.
#[using="Type"] Lemma rl_ok_sub : forall E model R R1, rl_ok E model R -> uE E (rg_base R) <= uE E (rg_base R1) ->
  uE E (rg_base R1) + rsz E R1 <= uE E (rg_base R) + rsz E R -> 0 < rsz E R1 -> rl_ok E model R1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E model R R1 H H1 H2 H3. unfold rl_ok in *. cbv zeta in *. destruct H as (Hz & [Happ | (Hsh & Happ & Hsw)]); split; [lia| |lia|].
  - left. intros w Hw. apply Happ. lia.
  - right. split; [lia|]. split; [intros x Hx; apply Happ; lia | intros w Hw; apply Hsw; lia].
Qed.

#[using="Type"] Theorem den_split : forall E S M ms model l1 R l2 R1 R2 o z,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ R :: l2 -> rg_size R = lconst z -> 0 < o < z -> z < two64 ->
  rg_sub_ok R R1 0 = true -> rg_sub_ok R R2 o = true -> csz R1 = o -> csz R2 = z - o ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ R1 :: R2 :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 R l2 R1 R2 o z Hd HS Hz Ho Hz64 Hs1 Hs2 Hc1 Hc2.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  (* [comment removed for export] *)
  assert (Hrz : forall E1, rsz E1 R = z) by (intros E1; unfold rsz; rewrite Hz, lden_lconst, u_small64 by lia; reflexivity).
  assert (Geo : forall E1 m, rg_ok segs E1 m R -> rg_ok segs E1 m R1 /\ rg_ok segs E1 m R2 /\
             uE E1 (rg_base R1) = uE E1 (rg_base R) /\ rsz E1 R1 = o /\ uE E1 (rg_base R2) = uE E1 (rg_base R) + o /\ rsz E1 R2 = z - o /\
             uE E1 (rg_base R) + z <= two64).
  { intros E1 m HR. destruct (rg_sub_sound segs E1 m R R1 0 HR Hs1) as (A1 & A2 & _ & _ & A5 & A6).
    destruct (rg_sub_sound segs E1 m R R2 o HR Hs2) as (B1 & B2 & _ & _ & B5 & B6).
    destruct HR as (_ & HF & _). rewrite Hrz in HF. refine (conj A1 (conj B1 _)). unfold uE. rewrite A2, B2, A6, B6, Hc1, Hc2. lia. }
  (* [comment removed for export] *)
  assert (Cov : forall E1 m (x : word), rg_ok segs E1 m R ->
            (bv_unsigned x < uE E1 (rg_base R) \/ uE E1 (rg_base R) + rsz E1 R <= bv_unsigned x) <->
            ((bv_unsigned x < uE E1 (rg_base R1) \/ uE E1 (rg_base R1) + rsz E1 R1 <= bv_unsigned x) /\
             (bv_unsigned x < uE E1 (rg_base R2) \/ uE E1 (rg_base R2) + rsz E1 R2 <= bv_unsigned x))).
  { intros E1 m x HR. destruct (Geo E1 m HR) as (_ & _ & G1 & G2 & G3 & G4 & _). rewrite Hrz, G1, G2, G3, G4. lia. }
  assert (HR0 : rg_ok segs E (ms_mem (restrict (Hof E M model) ms)) R).
  { destruct (Hsd E (agree_refl _ _)) as (_ & _ & _ & _ & A5 & _). rewrite HS in A5. apply Forall_app in A5 as [_ A5]. inversion A5; assumption. }
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ R1 :: R2 :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. unfold uE in Cov. rewrite (Cov E _ x HR0). tauto. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR' A5r']; subst.
    destruct (Geo E' _ HR') as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact G1|]. constructor; [exact G2 | exact A5r'].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a D2b].
      assert (Hz0 : forall R', In R' (l1 ++ R :: l2) -> 0 <= rsz E' R').
      { intros R' HR3. rewrite <- HS in HR3. destruct (Hsd E' Ha) as (_ & _ & _ & _ & X & _).
        rewrite Forall_forall in X. exact (proj1 (X R' HR3)). }
      refine (conj D1 (conj _ _)).
      * cbn [rgs_disj]. split; [|split; [|exact D2b]].
        -- constructor; [unfold rg_disj; cbv zeta; unfold uE in *; lia|]. rewrite Forall_forall in D2a |- *. intros R' HR''.
           apply (rg_disj_sub_l E' R R1 R' (D2a R' HR'')); [lia | rewrite Hrz; lia | lia | apply Hz0; apply in_or_app; right; right; exact HR''].
        -- rewrite Forall_forall in D2a |- *. intros R' HR''.
           apply (rg_disj_sub_l E' R R2 R' (D2a R' HR'')); [lia | rewrite Hrz; lia | lia | apply Hz0; apply in_or_app; right; right; exact HR''].
      * rewrite Forall_forall in D3 |- *. intros R' HR''. specialize (D3 R' HR''). inversion D3 as [|? ? D3a D3b]; subst.
        constructor; [|constructor; [|exact D3b]].
        -- apply rg_disj_sym. apply (rg_disj_sub_l E' R R1 R' (rg_disj_sym E' _ _ D3a)); [lia | rewrite Hrz; lia | lia | apply Hz0; apply in_or_app; left; exact HR''].
        -- apply rg_disj_sym. apply (rg_disj_sub_l E' R R2 R' (rg_disj_sym E' _ _ D3a)); [lia | rewrite Hrz; lia | lia | apply Hz0; apply in_or_app; left; exact HR''].
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in HbR as [Hb Hsz'].
    unfold rg_sub_ok in Hs1, Hs2. do 5 (apply andb_prop in Hs1 as [Hs1 _]). do 5 (apply andb_prop in Hs2 as [Hs2 _]).
    apply lin_eqb_eq in Hs1, Hs2. rewrite Hbl, Hbr. cbn [andb]. rewrite Hs1, Hs2. unfold laddc, lwf in *. cbn [l_t] in *. rewrite Hb.
    assert (Hc : forall R', csz R' >= 0 -> lwf (s_next S) (rg_size R') = true).
    { intros R' HR'. unfold csz in HR'. destruct (is_const (rg_size R')) as [c|] eqn:Hic; [|lia]. unfold is_const in Hic.
      unfold lwf. destruct (l_t (rg_size R')); [reflexivity | discriminate]. }
    unfold lwf in Hc. rewrite (Hc R1 ltac:(lia)), (Hc R2 ltac:(lia)). reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl Hrl2']; subst. apply Forall_app. split; [exact Hrl1|].
    destruct (Geo E _ HR0) as (_ & _ & G3 & G4 & G5 & G6 & _).
    constructor; [|constructor; [|exact Hrl2']].
    + apply (rl_ok_sub E model R R1 HRl); rewrite ?Hrz; lia.
    + apply (rl_ok_sub E model R R2 HRl); rewrite ?Hrz; lia.
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fact_eq_sound : forall E a b, fact_ok E (FCond BC_EQ a b true) -> lden E a = lden E b.
Proof. LiaFast.lf_pins LiaFast.u0. intros E a b H. cbn [fact_ok Sem.branch_taken] in H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_rebase : forall E S M ms model l1 R l2 b',
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ R :: l2 -> lwf (s_next S) b' = true ->
  (forall E', agree (s_next S) E E' -> lden E' b' = lden E' (rg_base R)) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b' (rg_size R) (rg_kind R) (rg_cont R) :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 R l2 b' Hd HS Hwb Heq.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (R' := RG b' (rg_size R) (rg_kind R) (rg_cont R)).
  assert (EB : forall E', agree (s_next S) E E' -> uE E' (rg_base R') = uE E' (rg_base R) /\ rsz E' R' = rsz E' R).
  { intros E' Ha. unfold uE, rsz, R'. cbn [rg_base rg_size]. rewrite (Heq E' Ha). split; reflexivity. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m R -> rg_ok segs E' m R').
  { intros E' m Ha HR. destruct (EB E' Ha) as [E1 E2]. unfold uE in E1.
    assert (Ek : rg_kind R' = rg_kind R) by reflexivity. assert (Ec : rg_cont R' = rg_cont R) by reflexivity.
    unfold rg_ok in *. cbv zeta in *. rewrite E1, E2, Ek, Ec. exact HR. }
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ R' :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. destruct (EB E (agree_refl _ _)) as [E1 E2]. unfold uE in E1. rewrite E1, E2. tauto. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR' A5r']; subst.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR') | exact A5r'].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a D2b]. destruct (EB E' Ha) as [E1 E2].
      refine (conj D1 (conj (conj _ D2b) _)).
      * rewrite Forall_forall in D2a |- *. intros R0 HR0. specialize (D2a R0 HR0). unfold rg_disj in *. cbv zeta in *. unfold uE in E1. rewrite E1, E2. exact D2a.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. constructor; [|exact D3b].
        unfold rg_disj in *. cbv zeta in *. unfold uE in E1. rewrite E1, E2. exact D3a.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in HbR as [Hb Hsz'].
    rewrite Hbl, Hbr. unfold R'. cbn [rg_base rg_size]. rewrite Hwb, Hsz'. reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl Hrl2']; subst. apply Forall_app. split; [exact Hrl1|].
    constructor; [|exact Hrl2']. unfold rl_ok in *. cbv zeta in *. destruct (EB E (agree_refl _ _)) as [E1 E2]. rewrite E1, E2. exact HRl.
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
Definition with_reg (S : sst) (k : positive) (l : lin) : sst := SST (s_pc S) (rset (s_regs S) k l) (s_rgs S) (s_facts S) (s_next S) (s_resv S).
#[using="Type"] Theorem den_reg_eq : forall E S M ms model k l,
  DEN segs LIMIT model0 mem0 E S M ms model -> k <> xH ->
  (forall E', agree (s_next S) E E' -> lden E' l = lden E' (rget (s_regs S) k)) ->
  DEN segs LIMIT model0 mem0 E (with_reg S k l) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model k l Hd Hk Heq.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; cbn [with_reg s_rgs s_next]; try assumption.
  intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_reg s_pc s_regs s_rgs s_facts s_resv].
  refine (conj A1 (conj A2 (conj A3 (conj _ (conj A5 (conj A6 (conj A7 A8))))))).
  intros r. rewrite (A4 r). destruct (Pos.eq_dec (rkey r) k) as [->|Hne].
  - rewrite rget_rset_same by exact Hk. symmetry. exact (Heq E' Ha).
  - rewrite rget_rset_other by exact Hne. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_weaken_rg : forall E S M ms model l1 R l2 R',
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ R :: l2 -> rg_base R' = rg_base R -> rg_size R' = rg_size R ->
  (forall E' m, agree (s_next S) E E' -> rg_ok segs E' m R -> rg_ok segs E' m R') ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ R' :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 R l2 R' Hd HS Hb Hz Hok.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (EB : forall E1, uE E1 (rg_base R') = uE E1 (rg_base R) /\ rsz E1 R' = rsz E1 R) by (intros E1; unfold uE, rsz; rewrite Hb, Hz; split; reflexivity).
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ R' :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. destruct (EB E) as [E1 E2]. unfold uE in E1. rewrite E1, E2. tauto. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR' A5r']; subst.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR') | exact A5r'].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a D2b]. destruct (EB E') as [E1 E2].
      refine (conj D1 (conj (conj _ D2b) _)).
      * rewrite Forall_forall in D2a |- *. intros R0 HR0. specialize (D2a R0 HR0). unfold rg_disj in *. cbv zeta in *. unfold uE in E1. rewrite E1, E2. exact D2a.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. constructor; [|exact D3b].
        unfold rg_disj in *. cbv zeta in *. unfold uE in E1. rewrite E1, E2. exact D3a.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb] in *. rewrite Hb, Hz. exact Hbw.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl Hrl2']; subst. apply Forall_app. split; [exact Hrl1|].
    constructor; [|exact Hrl2']. unfold rl_ok in *. cbv zeta in *. destruct (EB E) as [E1 E2]. rewrite E1, E2. exact HRl.
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem den_track_rg : forall E S M ms model l1 R l2 R',
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ R :: l2 -> rg_base R' = rg_base R -> rg_size R' = rg_size R ->
  (forall E', agree (s_next S) E E' -> rg_ok segs E' (ms_mem (restrict (Hof E M model) ms)) R -> rg_ok segs E' (ms_mem (restrict (Hof E M model) ms)) R') ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ R' :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 R l2 R' Hd HS Hb Hz Hok.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (EB : forall E1, uE E1 (rg_base R') = uE E1 (rg_base R) /\ rsz E1 R' = rsz E1 R) by (intros E1; unfold uE, rsz; rewrite Hb, Hz; split; reflexivity).
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ R' :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. destruct (EB E) as [E1 E2]. unfold uE in E1. rewrite E1, E2. tauto. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR' A5r']; subst.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' Ha HR') | exact A5r'].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a D2b]. destruct (EB E') as [E1 E2].
      refine (conj D1 (conj (conj _ D2b) _)).
      * rewrite Forall_forall in D2a |- *. intros R0 HR0. specialize (D2a R0 HR0). unfold rg_disj in *. cbv zeta in *. unfold uE in E1. rewrite E1, E2. exact D2a.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. constructor; [|exact D3b].
        unfold rg_disj in *. cbv zeta in *. unfold uE in E1. rewrite E1, E2. exact D3a.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb] in *. rewrite Hb, Hz. exact Hbw.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl Hrl2']; subst. apply Forall_app. split; [exact Hrl1|].
    constructor; [|exact Hrl2']. unfold rl_ok in *. cbv zeta in *. destruct (EB E) as [E1 E2]. rewrite E1, E2. exact HRl.
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem den_merge0 : forall E S M ms model l1 b1 b2 z1 z2 l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b1 (lconst z1) RW TEmpty :: RG b2 (lconst z2) RW TEmpty :: l2 ->
  0 < z1 -> 0 < z2 -> z1 + z2 < two64 ->
  (forall E', agree (s_next S) E E' -> uE E' b2 = uE E' b1 + z1) ->
  (forall w, uE E b1 <= w < uE E b1 + z1 + z2 -> in_shadow w = false) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b1 (lconst (z1 + z2)) RW TEmpty :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b1 b2 z1 z2 l2 Hd HS Hz1 Hz2 Hz64 Hadj Hnsh.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hrs : forall E1 b z, 0 <= z < two64 -> rsz E1 (RG b (lconst z) RW TEmpty) = z) by (intros E1 b z Hz; unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_small64 by exact Hz; reflexivity).
  pose proof (fun E1 => Hrs E1 b1 z1 ltac:(lia)) as Hr1. pose proof (fun E1 => Hrs E1 b2 z2 ltac:(lia)) as Hr2.
  pose proof (fun E1 => Hrs E1 b1 (z1 + z2) ltac:(lia)) as Hr.
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b1 (lconst (z1 + z2)) RW TEmpty :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr1, Hr2, Hr.
    pose proof (Hadj E (agree_refl _ _)) as HA. unfold uE in HA. rewrite HA.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + z1 <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b1) + z1 \/ bv_unsigned (lden E b1) + z1 + z2 <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + (z1 + z2) <= bv_unsigned x)) by lia.
    split; [intros (A & B & C & D); exact (conj A (conj (proj1 Heq (conj B C)) D)) |
            intros (A & B & D); destruct (proj2 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D)))]. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m (RG b1 (lconst z1) RW TEmpty) -> rg_ok segs E' m (RG b2 (lconst z2) RW TEmpty) ->
            rg_ok segs E' m (RG b1 (lconst (z1 + z2)) RW TEmpty)).
  { intros E' m Ha H1 H2. pose proof (Hadj E' Ha) as HA. unfold uE in HA.
    unfold rg_ok in H1, H2 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr1 in H1. rewrite Hr2 in H2. rewrite Hr.
    destruct H1 as (P1 & F1 & B1 & _). destruct H2 as (P2 & F2 & B2 & _). rewrite HA in F2, B2.
    split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Z_lt_le_dec i z1) as [X|X]; [exact (B1 i ltac:(lia))|].
      specialize (B2 (i - z1) ltac:(lia)). replace (bv_unsigned (lden E' b1) + z1 + (i - z1)) with (bv_unsigned (lden E' b1) + i) in B2 by lia. exact B2.
    - intros p v Hp. rewrite tget_empty in Hp. discriminate. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR1 A5r']; subst. inversion A5r' as [|? ? HR2 A5r'']; subst.
    pose proof (Hadj E' Ha) as HA. unfold uE in HA.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR1 HR2) | exact A5r''].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a [D2b D2c]].
      inversion D2a as [|? ? D12 D1l2]; subst.
      refine (conj D1 (conj (conj _ D2c) _)).
      * rewrite Forall_forall in D1l2, D2b |- *. intros R0 HR0. specialize (D1l2 R0 HR0). specialize (D2b R0 HR0).
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; right; right; right; exact HR0) Ha) as Hp0.
        unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D1l2. rewrite Hr2 in D2b. rewrite Hr. rewrite HA in D2b. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. inversion D3b as [|? ? D3c D3d]; subst.
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; left; exact HR0) Ha) as Hp0.
        constructor; [|exact D3d]. unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D3a. rewrite Hr2 in D3c. rewrite Hr.
        rewrite HA in D3c. lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in Hbr as [_ Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR _]. rewrite HbR. reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl1 Hrl2']; subst. inversion Hrl2' as [|? ? HRl2 Hrl2'']; subst.
    apply Forall_app. split; [exact Hrl1|]. constructor; [|exact Hrl2''].
    pose proof (Hadj E (agree_refl _ _)) as HA.
    unfold rl_ok in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in HRl1. rewrite Hr2 in HRl2. rewrite Hr. split; [lia|]. left.
    destruct HRl1 as (_ & [Happ1 | (_ & _ & Hsh1)]); [| specialize (Hsh1 (uE E b1) ltac:(lia)); rewrite (Hnsh (uE E b1) ltac:(lia)) in Hsh1; destruct Hsh1; discriminate].
    destruct HRl2 as (_ & [Happ2 | (_ & _ & Hsh2)]); [| rewrite HA in Hsh2; specialize (Hsh2 (uE E b1 + z1) ltac:(lia)); rewrite (Hnsh (uE E b1 + z1) ltac:(lia)) in Hsh2; destruct Hsh2; discriminate].
    intros w Hw. destruct (Z_lt_le_dec w (uE E b1 + z1)) as [X|X]; [apply Happ1; lia | apply Happ2; rewrite HA; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
Definition mc_ok (c2 c : tree bval) (z1 z2 : Z) : bool :=
  tforall (fun p v => (Z.leb z1 (Zpos p - 1) && Z.ltb (Zpos p - 1) (z1 + z2) &&
                       match tget (Z.to_pos (Zpos p - z1)) c2 with Some v' => bval_eqb v v' | None => false end)%bool) c.

#[using="Type"] Theorem den_mergeC : forall E S M ms model l1 b1 b2 z1 z2 c2 c l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b1 (lconst z1) RW TEmpty :: RG b2 (lconst z2) RW c2 :: l2 ->
  0 < z1 -> 0 < z2 -> z1 + z2 < two64 -> mc_ok c2 c z1 z2 = true ->
  (forall E', agree (s_next S) E E' -> uE E' b2 = uE E' b1 + z1) ->
  (forall w, uE E b1 <= w < uE E b1 + z1 + z2 -> in_shadow w = false) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b1 (lconst (z1 + z2)) RW c :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b1 b2 z1 z2 c2 c l2 Hd HS Hz1 Hz2 Hz64 Hmc Hadj Hnsh.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hrs : forall E1 b z cc, 0 <= z < two64 -> rsz E1 (RG b (lconst z) RW cc) = z) by (intros E1 b z cc Hz; unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_small64 by exact Hz; reflexivity).
  pose proof (fun E1 => Hrs E1 b1 z1 TEmpty ltac:(lia)) as Hr1. pose proof (fun E1 => Hrs E1 b2 z2 c2 ltac:(lia)) as Hr2.
  pose proof (fun E1 => Hrs E1 b1 (z1 + z2) c ltac:(lia)) as Hr.
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b1 (lconst (z1 + z2)) RW c :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr1, Hr2, Hr.
    pose proof (Hadj E (agree_refl _ _)) as HA. unfold uE in HA. rewrite HA.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + z1 <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b1) + z1 \/ bv_unsigned (lden E b1) + z1 + z2 <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + (z1 + z2) <= bv_unsigned x)) by lia.
    split; [intros (A & B & C & D); exact (conj A (conj (proj1 Heq (conj B C)) D)) |
            intros (A & B & D); destruct (proj2 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D)))]. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m (RG b1 (lconst z1) RW TEmpty) -> rg_ok segs E' m (RG b2 (lconst z2) RW c2) ->
            rg_ok segs E' m (RG b1 (lconst (z1 + z2)) RW c)).
  { intros E' m Ha H1 H2. pose proof (Hadj E' Ha) as HA. unfold uE in HA.
    unfold rg_ok in H1, H2 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr1 in H1. rewrite Hr2 in H2. rewrite Hr.
    destruct H1 as (P1 & F1 & B1 & _). destruct H2 as (P2 & F2 & B2 & C2). rewrite HA in F2, B2, C2.
    split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Z_lt_le_dec i z1) as [X|X]; [exact (B1 i ltac:(lia))|].
      specialize (B2 (i - z1) ltac:(lia)). replace (bv_unsigned (lden E' b1) + z1 + (i - z1)) with (bv_unsigned (lden E' b1) + i) in B2 by lia. exact B2.
    - intros p v Hp. pose proof (tforall_spec _ _ Hmc p v Hp) as X. cbv beta in X.
      apply andb_prop in X as [X Hv]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
      destruct (tget (Z.to_pos (Zpos p - z1)) c2) as [v'|] eqn:Hp2; [|discriminate]. apply bval_eqb_eq in Hv. subst v'.
      destruct (C2 _ _ Hp2) as [Y1 Y2]. rewrite Z2Pos.id in Y1, Y2 by lia. split; [lia|].
      replace (bv_unsigned (lden E' b1) + (Zpos p - 1)) with (bv_unsigned (lden E' b1) + z1 + (Zpos p - z1 - 1)) by lia. exact Y2. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR1 A5r']; subst. inversion A5r' as [|? ? HR2 A5r'']; subst.
    pose proof (Hadj E' Ha) as HA. unfold uE in HA.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR1 HR2) | exact A5r''].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a [D2b D2c]].
      inversion D2a as [|? ? D12 D1l2]; subst.
      refine (conj D1 (conj (conj _ D2c) _)).
      * rewrite Forall_forall in D1l2, D2b |- *. intros R0 HR0. specialize (D1l2 R0 HR0). specialize (D2b R0 HR0).
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; right; right; right; exact HR0) Ha) as Hp0.
        unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D1l2. rewrite Hr2 in D2b. rewrite Hr. rewrite HA in D2b. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. inversion D3b as [|? ? D3c D3d]; subst.
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; left; exact HR0) Ha) as Hp0.
        constructor; [|exact D3d]. unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D3a. rewrite Hr2 in D3c. rewrite Hr.
        rewrite HA in D3c. lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in Hbr as [_ Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR _]. rewrite HbR. reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl1 Hrl2']; subst. inversion Hrl2' as [|? ? HRl2 Hrl2'']; subst.
    apply Forall_app. split; [exact Hrl1|]. constructor; [|exact Hrl2''].
    pose proof (Hadj E (agree_refl _ _)) as HA.
    unfold rl_ok in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in HRl1. rewrite Hr2 in HRl2. rewrite Hr. split; [lia|]. left.
    destruct HRl1 as (_ & [Happ1 | (_ & _ & Hsh1)]); [| specialize (Hsh1 (uE E b1) ltac:(lia)); rewrite (Hnsh (uE E b1) ltac:(lia)) in Hsh1; destruct Hsh1; discriminate].
    destruct HRl2 as (_ & [Happ2 | (_ & _ & Hsh2)]); [| rewrite HA in Hsh2; specialize (Hsh2 (uE E b1 + z1) ltac:(lia)); rewrite (Hnsh (uE E b1 + z1) ltac:(lia)) in Hsh2; destruct Hsh2; discriminate].
    intros w Hw. destruct (Z_lt_le_dec w (uE E b1 + z1)) as [X|X]; [apply Happ1; lia | apply Happ2; rewrite HA; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

(* [comment removed for export] *)
Definition mc2_ok (c1 c2 c : tree bval) (z1 z2 : Z) : bool :=
  tforall (fun p v => (Z.ltb (Zpos p - 1) (z1 + z2) &&
                       if Z.ltb (Zpos p - 1) z1 then match tget p c1 with Some v' => bval_eqb v v' | None => false end
                       else match tget (Z.to_pos (Zpos p - z1)) c2 with Some v' => bval_eqb v v' | None => false end)%bool) c.

#[using="Type"] Theorem den_mergeCC : forall E S M ms model l1 b1 b2 z1 z2 c1 c2 c l2,
  DEN segs LIMIT model0 mem0 E S M ms model -> s_rgs S = l1 ++ RG b1 (lconst z1) RW c1 :: RG b2 (lconst z2) RW c2 :: l2 ->
  0 < z1 -> 0 < z2 -> z1 + z2 < two64 -> mc2_ok c1 c2 c z1 z2 = true ->
  (forall E', agree (s_next S) E E' -> uE E' b2 = uE E' b1 + z1) ->
  (forall w, uE E b1 <= w < uE E b1 + z1 + z2 -> in_shadow w = false) ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (l1 ++ RG b1 (lconst (z1 + z2)) RW c :: l2)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model l1 b1 b2 z1 z2 c1 c2 c l2 Hd HS Hz1 Hz2 Hz64 Hmc Hadj Hnsh.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  assert (Hrs : forall E1 b z cc, 0 <= z < two64 -> rsz E1 (RG b (lconst z) RW cc) = z) by (intros E1 b z cc Hz; unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_small64 by exact Hz; reflexivity).
  pose proof (fun E1 => Hrs E1 b1 z1 c1 ltac:(lia)) as Hr1. pose proof (fun E1 => Hrs E1 b2 z2 c2 ltac:(lia)) as Hr2.
  pose proof (fun E1 => Hrs E1 b1 (z1 + z2) c ltac:(lia)) as Hr.
  assert (Hout : forall x, outside E (s_rgs S) x <-> outside E (l1 ++ RG b1 (lconst (z1 + z2)) RW c :: l2) x).
  { intros x. rewrite HS. unfold outside. rewrite !Forall_app, !Forall_cons_iff. cbn [rg_base]. rewrite Hr1, Hr2, Hr.
    pose proof (Hadj E (agree_refl _ _)) as HA. unfold uE in HA. rewrite HA.
    assert (Heq : (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + z1 <= bv_unsigned x) /\
                  (bv_unsigned x < bv_unsigned (lden E b1) + z1 \/ bv_unsigned (lden E b1) + z1 + z2 <= bv_unsigned x) <->
                  (bv_unsigned x < bv_unsigned (lden E b1) \/ bv_unsigned (lden E b1) + (z1 + z2) <= bv_unsigned x)) by lia.
    split; [intros (A & B & C & D); exact (conj A (conj (proj1 Heq (conj B C)) D)) |
            intros (A & B & D); destruct (proj2 Heq B) as [B1 C1]; exact (conj A (conj B1 (conj C1 D)))]. }
  assert (Hok : forall E' m, agree (s_next S) E E' -> rg_ok segs E' m (RG b1 (lconst z1) RW c1) -> rg_ok segs E' m (RG b2 (lconst z2) RW c2) ->
            rg_ok segs E' m (RG b1 (lconst (z1 + z2)) RW c)).
  { intros E' m Ha H1 H2. pose proof (Hadj E' Ha) as HA. unfold uE in HA.
    unfold rg_ok in H1, H2 |- *. cbv zeta in *. cbn [rg_base rg_kind rg_cont] in *. rewrite Hr1 in H1. rewrite Hr2 in H2. rewrite Hr.
    destruct H1 as (P1 & F1 & B1 & C1). destruct H2 as (P2 & F2 & B2 & C2). rewrite HA in F2, B2, C2.
    split; [lia|]. split; [lia|]. split.
    - intros i Hi. destruct (Z_lt_le_dec i z1) as [X|X]; [exact (B1 i ltac:(lia))|].
      specialize (B2 (i - z1) ltac:(lia)). replace (bv_unsigned (lden E' b1) + z1 + (i - z1)) with (bv_unsigned (lden E' b1) + i) in B2 by lia. exact B2.
    - intros p v Hp. pose proof (tforall_spec _ _ Hmc p v Hp) as X. cbv beta in X.
      apply andb_prop in X as [X2 Hv]. apply Z.ltb_lt in X2.
      destruct (Z.ltb (Zpos p - 1) z1) eqn:Hlt.
      + apply Z.ltb_lt in Hlt. destruct (tget p c1) as [v'|] eqn:Hp1; [|discriminate]. apply bval_eqb_eq in Hv. subst v'.
        destruct (C1 _ _ Hp1) as [Y1 Y2]. split; [lia | exact Y2].
      + apply Z.ltb_ge in Hlt. destruct (tget (Z.to_pos (Zpos p - z1)) c2) as [v'|] eqn:Hp2; [|discriminate]. apply bval_eqb_eq in Hv. subst v'.
        destruct (C2 _ _ Hp2) as [Y1 Y2]. rewrite Z2Pos.id in Y1, Y2 by lia. split; [lia|].
        replace (bv_unsigned (lden E' b1) + (Zpos p - 1)) with (bv_unsigned (lden E' b1) + z1 + (Zpos p - z1 - 1)) by lia. exact Y2. }
  assert (Hpos : forall R0 E', In R0 (s_rgs S) -> agree (s_next S) E E' -> 0 < rsz E' R0).
  { intros R0 E' HR0 Ha. rewrite Forall_forall in Hrl. destruct (Hrl R0 HR0) as (Hp & _).
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 HR0)) as [_ Hs].
    unfold rsz in *. rewrite (lden_agree_wf _ E E' _ Hs Ha). exact Hp. }
  constructor; cbn [with_rgs s_rgs s_next]; try assumption.
  - intros E' Ha. destruct (Hsd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold sden0; cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv].
    rewrite HS in A5, A6. apply Forall_app in A5 as [A5l A5r]. inversion A5r as [|? ? HR1 A5r']; subst. inversion A5r' as [|? ? HR2 A5r'']; subst.
    pose proof (Hadj E' Ha) as HA. unfold uE in HA.
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj _ (conj A7 A8))))))).
    + apply Forall_app. split; [exact A5l|]. constructor; [exact (Hok E' _ Ha HR1 HR2) | exact A5r''].
    + apply rgs_disj_app_iff in A6 as (D1 & D2 & D3). apply rgs_disj_app_iff. destruct D2 as [D2a [D2b D2c]].
      inversion D2a as [|? ? D12 D1l2]; subst.
      refine (conj D1 (conj (conj _ D2c) _)).
      * rewrite Forall_forall in D1l2, D2b |- *. intros R0 HR0. specialize (D1l2 R0 HR0). specialize (D2b R0 HR0).
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; right; right; right; exact HR0) Ha) as Hp0.
        unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D1l2. rewrite Hr2 in D2b. rewrite Hr. rewrite HA in D2b. lia.
      * rewrite Forall_forall in D3 |- *. intros R0 HR0. specialize (D3 R0 HR0). inversion D3 as [|? ? D3a D3b]; subst. inversion D3b as [|? ? D3c D3d]; subst.
        pose proof (Hpos R0 E' ltac:(rewrite HS; apply in_or_app; left; exact HR0) Ha) as Hp0.
        constructor; [|exact D3d]. unfold rg_disj in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in D3a. rewrite Hr2 in D3c. rewrite Hr.
        rewrite HA in D3c. lia.
  - unfold bases_wf in *. rewrite HS in Hbw. rewrite !forallb_app in *. cbn [forallb rg_base rg_size] in *.
    apply andb_prop in Hbw as [Hbl Hbr]. apply andb_prop in Hbr as [HbR Hbr]. apply andb_prop in Hbr as [_ Hbr]. rewrite Hbl, Hbr.
    apply andb_prop in HbR as [HbR _]. rewrite HbR. reflexivity.
  - intros w Hw Hout' Hno Hnb. exact (Hzr w Hw (proj2 (Hout _) Hout') Hno Hnb).
  - rewrite HS in Hrl. apply Forall_app in Hrl as [Hrl1 Hrl2]. inversion Hrl2 as [|? ? HRl1 Hrl2']; subst. inversion Hrl2' as [|? ? HRl2 Hrl2'']; subst.
    apply Forall_app. split; [exact Hrl1|]. constructor; [|exact Hrl2''].
    pose proof (Hadj E (agree_refl _ _)) as HA.
    unfold rl_ok in *. cbv zeta in *. cbn [rg_base] in *. rewrite Hr1 in HRl1. rewrite Hr2 in HRl2. rewrite Hr. split; [lia|]. left.
    destruct HRl1 as (_ & [Happ1 | (_ & _ & Hsh1)]); [| specialize (Hsh1 (uE E b1) ltac:(lia)); rewrite (Hnsh (uE E b1) ltac:(lia)) in Hsh1; destruct Hsh1; discriminate].
    destruct HRl2 as (_ & [Happ2 | (_ & _ & Hsh2)]); [| rewrite HA in Hsh2; specialize (Hsh2 (uE E b1 + z1) ltac:(lia)); rewrite (Hnsh (uE E b1 + z1) ltac:(lia)) in Hsh2; destruct Hsh2; discriminate].
    intros w Hw. destruct (Z_lt_le_dec w (uE E b1 + z1)) as [X|X]; [apply Happ1; lia | apply Happ2; rewrite HA; lia].
  - intros p Hp w Hw. destruct (Hfrz p Hp w Hw) as (X1 & X2 & X3). split; [exact X1|]. split; [exact (proj1 (Hout _) X2) | exact X3].
  - intros p Hp w Hw. destruct (Hown p Hp w Hw) as [Hv Hm]. split; [exact Hv|]. intros Ho'. exact (Hm (proj2 (Hout _) Ho')).
Qed.

End Carve.
(* [comment removed for export] *)
