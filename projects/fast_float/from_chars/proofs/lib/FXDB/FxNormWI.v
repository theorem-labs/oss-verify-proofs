(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxImg.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.

Module FxNormW.
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
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition cbyte (fs : list fact) (k : rkind) (c : tree bval) (p : positive) : option Z :=
  match tget p c with
  | Some (BK b) => Some (b mod 256)
  | Some (BV l j) => let '(lo, hi) := irange fs l in      (* [comment removed for export] *)
                     if (Z.eqb lo hi && Z.leb 0 j)%bool then Some (Z.shiftr lo (8 * j) mod 256) else None
  | None => match k with RZ => Some 0 | _ => None end
  end.
Fixpoint cword (fs : list fact) (k : rkind) (c : tree bval) (k0 : positive) (n : nat) : option Z :=
  match n with
  | O => Some 0
  | Datatypes.S n' => match cword fs k c k0 n', cbyte fs k c (Pos.of_nat (Pos.to_nat k0 + n')) with
                      | Some w, Some b => Some (w + b * 2 ^ (8 * Z.of_nat n'))
                      | _, _ => None
                      end
  end.
Definition cword_ok (fs : list fact) (R : region) (k0 : positive) (C : Z) : bool :=
  (Z.leb 0 C && Z.ltb C two64 &&
   match is_const (rg_size R) with Some z => Z.leb (Zpos k0 + 7) z | None => false end &&
   forallb (fun j => match cbyte fs (rg_kind R) (rg_cont R) (Pos.of_nat (Pos.to_nat k0 + j)) with
                     | Some b => Z.eqb b (Z.shiftr C (8 * Z.of_nat j) mod 256)
                     | None => false end) (List.seq 0 8))%bool.
Definition normw_rg (fs : list fact) (R : region) (k0 : positive) : option region :=
  match cword fs (rg_kind R) (rg_cont R) k0 8 with
  | Some C => if cword_ok fs R k0 C then Some (RG (rg_base R) (rg_size R) (rg_kind R) (put_bv (rg_cont R) k0 C 8)) else None
  | None => None
  end.
Definition normw_at (S : sst) (i : nat) (k0 : positive) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match normw_rg (s_facts S) R k0 with
              | Some R' => Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.

Lemma bv8_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma normw_rg_ok : forall segs E m fs R k0 R', Forall (fact_ok E) fs -> normw_rg fs R k0 = Some R' -> rg_ok segs E m R -> rg_ok segs E m R'.
Proof.
  intros segs E m fs R k0 R' HF Hr Hok. unfold normw_rg in Hr. destruct (cword fs (rg_kind R) (rg_cont R) k0 8) as [C|]; [|discriminate].
  destruct (cword_ok fs R k0 C) eqn:Hb; [|discriminate]. injection Hr as <-. unfold cword_ok in Hb.
  apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hb Hsz]. apply andb_prop in Hb as [Hc0 Hc1].
  apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. rewrite forallb_forall in Hall.
  destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|discriminate]. apply Z.leb_le in Hsz.
  destruct (is_const_sound E _ z Hz) as [Hzv Hzr].
  assert (Hrsz : rsz E R = z) by (unfold rsz; rewrite Hzv; apply u_small64; exact Hzr).
  assert (HT : forall p, tget p (put_bv (rg_cont R) k0 C 8) = None -> tget p (rg_cont R) = None).
  { intros p Hn. rewrite tget_put_bv in Hn. destruct (existsb _ _) eqn:He; [discriminate | exact Hn]. }
  assert (HS : forall p v, tget p (put_bv (rg_cont R) k0 C 8) = Some v ->
             (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 8) = true /\ v = BV (lconst C) (Z.of_nat (Pos.to_nat p - Pos.to_nat k0))) \/
             tget p (rg_cont R) = Some v).
  { intros p v Hp. rewrite tget_put_bv in Hp. destruct (existsb _ _) eqn:He; [left; split; [reflexivity | injection Hp as <-; reflexivity] | right; exact Hp]. }
  destruct Hok as (Hs & Hw & Hbytes & Hc). cbn [rg_base rg_size rg_kind rg_cont] in *. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont].
  unfold rsz in *. cbn [rg_size] in *.
  split; [exact Hs|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try exact Hbytes.
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
  - intros p v Hp. destruct (HS p v Hp) as [[He ->]|Hp']; [|exact (Hc p v Hp')].
    apply existsb_exists in He as (j & Hj & Hpj). apply Pos.eqb_eq in Hpj. subst p. specialize (Hall j Hj). apply in_seq in Hj.
    pose proof (Pos2Nat.is_pos k0) as Hk0.
    assert (Hpz : Zpos (Pos.of_nat (Pos.to_nat k0 + j)) = Zpos k0 + Z.of_nat j).
    { rewrite <- (Pos2Nat.id k0) at 2. rewrite <- !positive_nat_Z. rewrite Nat2Pos.id by lia. rewrite Pos2Nat.id. lia. }
    rewrite Nat2Pos.id by lia. replace (Pos.to_nat k0 + j - Pos.to_nat k0)%nat with j by lia.
    assert (Hbd : bden E (BV (lconst C) (Z.of_nat j)) = Z_to_bv 8 (Z.shiftr C (8 * Z.of_nat j))).
    { cbn [bden]. rewrite lden_lconst, u_small64 by lia. reflexivity. }
    rewrite Hbd. split; [rewrite Hpz; lia|].
    unfold cbyte in Hall. destruct (tget (Pos.of_nat (Pos.to_nat k0 + j)) (rg_cont R)) as [[b|l j']|] eqn:Ht.
    + apply Z.eqb_eq in Hall. destruct (Hc _ _ Ht) as [_ Hv]. rewrite Hv. cbn [bden]. f_equal. apply bv8_mod. exact Hall.
    + destruct (irange fs l) as [lo hi] eqn:Hir. destruct (Z.eqb lo hi && Z.leb 0 j')%bool eqn:Hj'; [|discriminate]. apply andb_prop in Hj' as [Hlh _].
      apply Z.eqb_eq in Hlh. apply Z.eqb_eq in Hall. pose proof (irange_sound E fs l HF) as Rl. rewrite Hir in Rl. cbn [fst snd] in Rl.
      destruct (Hc _ _ Ht) as [_ Hv]. rewrite Hv. cbn [bden]. replace (bv_unsigned (lden E l)) with lo by lia.
      f_equal. apply bv8_mod. exact Hall.
    + destruct (rg_kind R) eqn:Hk; try discriminate. apply Z.eqb_eq in Hall.
      assert (Hi : 0 <= Zpos (Pos.of_nat (Pos.to_nat k0 + j)) - 1 < bv_unsigned (lden E (rg_size R))) by (rewrite Hpz, Hrsz; lia).
      specialize (Hbytes _ Hi). cbn beta iota in Hbytes. destruct Hbytes as [_ H2].
      assert (Hok' : okey (Zpos (Pos.of_nat (Pos.to_nat k0 + j)) - 1) = Pos.of_nat (Pos.to_nat k0 + j)) by (unfold okey; rewrite Z.sub_add; reflexivity).
      rewrite Hok' in H2. rewrite (H2 Ht). f_equal. apply bv8_mod. rewrite <- Hall. reflexivity.
Qed.

Section NormW.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_normw : forall model0 E S M ms model i k0 S', DEN segs LIMIT model0 mem0 E S M ms model -> normw_at S i k0 = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i k0 S' Hd Hp. unfold normw_at in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (normw_rg (s_facts S) R k0) as [R'|] eqn:Hr; [|discriminate].
  injection Hp as <-.
  assert (HR' : rg_base R' = rg_base R /\ rg_size R' = rg_size R /\ rg_kind R' = rg_kind R).
  { unfold normw_rg in Hr. destruct (cword (s_facts S) (rg_kind R) (rg_cont R) k0 8); [|discriminate]. destruct (cword_ok (s_facts S) R k0 z); [|discriminate]. injection Hr as <-. cbn. tauto. }
  destruct HR' as (Hb' & Hs' & Hk').
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) i R' R Hi Hb' Hs')).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        exact (normw_rg_ok segs E'' _ (s_facts S) R k0 R' HF Hr (proj1 (Forall_nth' _ _) HG i R Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
    + eapply rgs_disj_upd; [exact Hi | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (j & Hj). cbn [S2 s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R0 (nth_error_In _ _ Hj)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
Qed.
End NormW.
(* [comment removed for export] *)
End FxNormW.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxNormWI.FxNormW.

Module FxSplitW32.
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
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxNormWI.FxNormW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition key_at (k0 : positive) (j : nat) : positive := Pos.of_nat (Pos.to_nat k0 + j).
Definition is_word_of (c : tree bval) (k0 : positive) (f : lin) : bool :=
  forallb (fun j => match tget (key_at k0 j) c with Some (BV f' j') => (lin_eqb f' f && Z.eqb j' (Z.of_nat j))%bool | _ => false end) (List.seq 0 8).
Definition new_cell (r : Z) (g : lin) (j : nat) : bval :=
  if Nat.ltb j 4 then BK (Z.shiftr r (8 * Z.of_nat j) mod 256) else BV g (Z.of_nat (j - 4)).
Fixpoint put_cells (t : tree bval) (k0 : positive) (r : Z) (g : lin) (j : nat) : tree bval :=
  match j with
  | O => t
  | Datatypes.S j' => put_cells (tset (key_at k0 j') (new_cell r g j') t) k0 r g j'
  end.
Definition splitw32_rg (fs : list fact) (R : region) (k0 : positive) : option region :=
  match tget k0 (rg_cont R) with
  | Some (BV f 0) =>
      if is_word_of (rg_cont R) k0 f then
        match lowb fs f 32, srl_lin fs 32 f with
        | Some r, Some g => Some (RG (rg_base R) (rg_size R) (rg_kind R) (put_cells (rg_cont R) k0 r g 8))
        | _, _ => None
        end
      else None
  | _ => None
  end.
Definition splitw32_at (S : sst) (i : nat) (k0 : positive) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match splitw32_rg (s_facts S) R k0 with
              | Some R' => if match (match tget k0 (rg_cont R) with Some (BV f _) => srl_lin (s_facts S) 32 f | _ => None end) with
                              | Some g => lwf (s_next S) g | None => false end
                           then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)) else None
              | None => None
              end
  | None => None
  end.

Lemma tget_put_cells : forall j t k0 r g p, tget p (put_cells t k0 r g j) =
  if existsb (fun i => Pos.eqb p (key_at k0 i)) (List.seq 0 j)
  then Some (new_cell r g (Pos.to_nat p - Pos.to_nat k0)) else tget p t.
Proof.
  induction j as [|j IH]; intros t k0 r g p; cbn [put_cells]; [reflexivity|].
  rewrite IH. rewrite seq_S, existsb_app. cbn [existsb]. rewrite orb_false_r, Nat.add_0_l.
  destruct (existsb (fun i => Pos.eqb p (key_at k0 i)) (List.seq 0 j)) eqn:He; [reflexivity|].
  cbn [orb]. destruct (Pos.eqb p (key_at k0 j)) eqn:Hp.
  - apply Pos.eqb_eq in Hp. subst p. rewrite tget_tset_same. unfold key_at. rewrite Nat2Pos.id by (pose proof (Pos2Nat.is_pos k0); lia).
    replace (Pos.to_nat k0 + j - Pos.to_nat k0)%nat with j by lia. reflexivity.
  - rewrite tget_tset_other; [reflexivity|]. intros X. subst. rewrite Pos.eqb_refl in Hp. discriminate.
Qed.

Lemma low_byte : forall F r j, 0 <= F -> F mod 2 ^ 32 = r -> 0 <= j < 4 -> Z.shiftr F (8 * j) mod 256 = (Z.shiftr r (8 * j) mod 256) mod 256.
Proof.
  intros F r j HF Hr Hj. rewrite Z.mod_mod by lia. subst r. change 256 with (2 ^ 8). rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec by lia. rewrite Z.land_spec.
  destruct (Z.ltb n 8) eqn:H8.
  - apply Z.ltb_lt in H8. rewrite (Z.ones_spec_low 8 n) by lia. rewrite (Z.ones_spec_low 32 (n + 8 * j)) by lia. rewrite !andb_true_r. reflexivity.
  - apply Z.ltb_ge in H8. rewrite (Z.ones_spec_high 8 n) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma splitw32_rg_ok : forall segs E m fs R k0 R', Forall (fact_ok E) fs -> splitw32_rg fs R k0 = Some R' -> rg_ok segs E m R -> rg_ok segs E m R'.
Proof.
  intros segs E m fs R k0 R' HF Hr Hok. unfold splitw32_rg in Hr.
  destruct (tget k0 (rg_cont R)) as [[b|f j0]|] eqn:H0; try discriminate. destruct j0; try discriminate.
  destruct (is_word_of (rg_cont R) k0 f) eqn:Hw; [|discriminate].
  destruct (lowb fs f 32) as [r|] eqn:Hlow; [|discriminate]. destruct (srl_lin fs 32 f) as [g|] eqn:Hsrl; [|discriminate]. injection Hr as <-.
  pose proof (lowb_sound E fs f 32 r HF Hlow) as Hr32. pose proof (srl_lin_sound E fs 32 f g HF ltac:(lia) Hsrl) as Hg.
  set (F := bv_unsigned (lden E f)) in *. assert (HF0 : 0 <= F) by (unfold F; pose proof (bv_unsigned_in_range _ (lden E f)); lia).
  unfold is_word_of in Hw. rewrite forallb_forall in Hw.
  assert (HT : forall p, tget p (put_cells (rg_cont R) k0 r g 8) = None -> tget p (rg_cont R) = None).
  { intros p Hn. rewrite tget_put_cells in Hn. destruct (existsb _ _) eqn:He; [discriminate | exact Hn]. }
  assert (HS : forall p v, tget p (put_cells (rg_cont R) k0 r g 8) = Some v ->
             (existsb (fun i => Pos.eqb p (key_at k0 i)) (List.seq 0 8) = true /\ v = new_cell r g (Pos.to_nat p - Pos.to_nat k0)) \/ tget p (rg_cont R) = Some v).
  { intros p v Hp. rewrite tget_put_cells in Hp. destruct (existsb _ _) eqn:He; [left; split; [reflexivity | injection Hp as <-; reflexivity] | right; exact Hp]. }
  destruct Hok as (Hs & Hwd & Hbytes & Hc). cbn [rg_base rg_size rg_kind rg_cont] in *. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont].
  split; [exact Hs|]. split; [exact Hwd|]. split.
  - intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try exact Hbytes.
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
  - intros p v Hp. destruct (HS p v Hp) as [[He ->]|Hp']; [|exact (Hc p v Hp')].
    apply existsb_exists in He as (j & Hj & Hpj). apply Pos.eqb_eq in Hpj. subst p.
    specialize (Hw j Hj). apply in_seq in Hj. pose proof (Pos2Nat.is_pos k0) as Hk0.
    destruct (tget (key_at k0 j) (rg_cont R)) as [[b|f' j']|] eqn:Ht; try discriminate.
    apply andb_prop in Hw as [Hf' Hj']. apply lin_eqb_eq in Hf'. apply Z.eqb_eq in Hj'. subst f' j'.
    destruct (Hc _ _ Ht) as [Hpos Hv]. split; [exact Hpos|]. rewrite Hv. f_equal.
    unfold key_at. rewrite Nat2Pos.id by lia. replace (Pos.to_nat k0 + j - Pos.to_nat k0)%nat with j by lia.
    cbn [bden]. fold F. unfold new_cell. destruct (Nat.ltb j 4) eqn:Hj4.
    + apply Nat.ltb_lt in Hj4. cbn [bden]. apply bv8_mod. apply low_byte; [exact HF0 | exact Hr32 | lia].
    + apply Nat.ltb_ge in Hj4. cbn [bden]. rewrite Hg. fold F. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Section SplitW32.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_splitw32 : forall model0 E S M ms model i k0 S', DEN segs LIMIT model0 mem0 E S M ms model -> splitw32_at S i k0 = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros model0 E S M ms model i k0 S' Hd Hp. unfold splitw32_at in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (splitw32_rg (s_facts S) R k0) as [R'|] eqn:Hr; [|discriminate].
  match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hgw; [|discriminate] end. injection Hp as <-.
  assert (HR' : rg_base R' = rg_base R /\ rg_size R' = rg_size R /\ rg_kind R' = rg_kind R).
  { unfold splitw32_rg in Hr. destruct (tget k0 (rg_cont R)) as [[b|f j0]|]; try discriminate. destruct j0; try discriminate.
    destruct (is_word_of (rg_cont R) k0 f); [|discriminate]. destruct (lowb (s_facts S) f 32); [|discriminate]. destruct (srl_lin (s_facts S) 32 f); [|discriminate].
    injection Hr as <-. cbn. tauto. }
  destruct HR' as (Hb' & Hs' & Hk').
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) i R' R Hi Hb' Hs')).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        exact (splitw32_rg_ok segs E'' _ (s_facts S) R k0 R' HF Hr (proj1 (Forall_nth' _ _) HG i R Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
    + eapply rgs_disj_upd; [exact Hi | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (j & Hj). cbn [S2 s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R0 (nth_error_In _ _ Hj)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
Qed.
End SplitW32.
(* [comment removed for export] *)
End FxSplitW32.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition wcell (lit : bool) (C : Z) (j : nat) : bval := if lit then BK (Z.land (Z.shiftr C (8 * Z.of_nat j)) 255) else BV (lconst C) (Z.of_nat j).
Fixpoint put_w (lit : bool) (t : tree bval) (k0 : positive) (C : Z) (j : nat) : tree bval :=
  match j with
  | O => t
  | Datatypes.S j' => put_w lit (tset (kadd k0 j') (wcell lit C j') t) k0 C j'
  end.
Lemma tget_put_w : forall lit j t k0 c p, tget p (put_w lit t k0 c j) =
  if existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 j)
  then Some (wcell lit c (Pos.to_nat p - Pos.to_nat k0)) else tget p t.
Proof.
  intros lit. induction j as [|j IH]; intros t k0 c p; cbn [put_w]; [reflexivity|].
  rewrite kadd_eq, IH. rewrite seq_S, existsb_app. cbn [existsb]. rewrite orb_false_r, Nat.add_0_l.
  destruct (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 j)) eqn:He; [reflexivity|].
  cbn [orb]. destruct (Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + j))) eqn:Hp.
  - apply Pos.eqb_eq in Hp. subst p. rewrite tget_tset_same. rewrite Nat2Pos.id by (pose proof (Pos2Nat.is_pos k0); lia).
    replace (Pos.to_nat k0 + j - Pos.to_nat k0)%nat with j by lia. reflexivity.
  - rewrite tget_tset_other; [reflexivity|]. intros X. subst. rewrite Pos.eqb_refl in Hp. discriminate.
Qed.
Lemma bden_wcell : forall E lit C j, 0 <= C < two64 -> bden E (wcell lit C j) = Z_to_bv 8 (Z.shiftr C (8 * Z.of_nat j)).
Proof.
  intros E lit C j HC. destruct lit; cbn [wcell bden].
  - apply bv8_mod. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. apply Z.mod_mod. lia.
  - rewrite lden_lconst, u_small64 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition cbytei (img : tree Z) (oA : option Z) (fs : list fact) (k : rkind) (c : tree bval) (p : positive) : option Z :=
  match tget p c with
  | Some (BK b) => Some (b mod 256)
  | Some (BV l j) => let '(lo, hi) := irange fs l in      (* [comment removed for export] *)
                     if (Z.eqb lo hi && Z.leb 0 j)%bool then Some (Z.shiftr lo (8 * j) mod 256)
                     (* [comment removed for export] *)
                     else if (Z.leb 0 lo && Z.leb 0 j && Z.ltb hi (2 ^ (8 * j)))%bool then Some 0 else None
  | None => match k with
            | RZ => Some 0
            | RI => match oA with
                    | Some A => match img_bytes img (A + (Zpos p - 1)) 1 with Some [b] => if Z.leb 0 A then Some (b mod 256) else None | _ => None end
                    | None => None
                    end
            | _ => None
            end
  end.
Fixpoint cwordi (img : tree Z) (oA : option Z) (fs : list fact) (k : rkind) (c : tree bval) (k0 : positive) (n : nat) : option Z :=
  match n with
  | O => Some 0
  | Datatypes.S n' => match cwordi img oA fs k c k0 n', cbytei img oA fs k c (Pos.of_nat (Pos.to_nat k0 + n')) with
                      | Some w, Some b => Some (w + b * 2 ^ (8 * Z.of_nat n'))
                      | _, _ => None
                      end
  end.
Definition cwordi_ok (img : tree Z) (fs : list fact) (R : region) (k0 : positive) (C : Z) : bool :=
  (Z.leb 0 C && Z.ltb C two64 &&
   match is_const (rg_size R) with Some z => Z.leb (Zpos k0 + 7) z | None => false end &&
   forallb (fun j => match cbytei img (is_const (rg_base R)) fs (rg_kind R) (rg_cont R) (Pos.of_nat (Pos.to_nat k0 + j)) with
                     | Some b => Z.eqb b (Z.shiftr C (8 * Z.of_nat j) mod 256)
                     | None => false end) (List.seq 0 8))%bool.
Definition normwi_rg (img : tree Z) (lit : bool) (fs : list fact) (R : region) (k0 : positive) : option region :=
  match cwordi img (is_const (rg_base R)) fs (rg_kind R) (rg_cont R) k0 8 with
  | Some C => if cwordi_ok img fs R k0 C then Some (RG (rg_base R) (rg_size R) (rg_kind R) (put_w lit (rg_cont R) k0 C 8)) else None
  | None => None
  end.
Definition normwi_at (img : tree Z) (lit : bool) (S : sst) (i : nat) (k0 : positive) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match normwi_rg img lit (s_facts S) R k0 with
              | Some R' => Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S))
              | None => None
              end
  | None => None
  end.


Lemma normwi_rg_ok : forall segs img lit E m fs R k0 R', img_ok segs img -> Forall (fact_ok E) fs -> normwi_rg img lit fs R k0 = Some R' -> rg_ok segs E m R -> rg_ok segs E m R'.
Proof.
  intros segs img lit E m fs R k0 R' Himg HF Hr Hok. unfold normwi_rg in Hr. destruct (cwordi img (is_const (rg_base R)) fs (rg_kind R) (rg_cont R) k0 8) as [C|]; [|discriminate].
  destruct (cwordi_ok img fs R k0 C) eqn:Hb; [|discriminate]. injection Hr as <-. unfold cwordi_ok in Hb.
  apply andb_prop in Hb as [Hb Hall]. apply andb_prop in Hb as [Hb Hsz]. apply andb_prop in Hb as [Hc0 Hc1].
  apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. rewrite forallb_forall in Hall.
  destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|discriminate]. apply Z.leb_le in Hsz.
  destruct (is_const_sound E _ z Hz) as [Hzv Hzr].
  assert (Hrsz : rsz E R = z) by (unfold rsz; rewrite Hzv; apply u_small64; exact Hzr).
  assert (HT : forall p, tget p (put_w lit (rg_cont R) k0 C 8) = None -> tget p (rg_cont R) = None).
  { intros p Hn. rewrite tget_put_w in Hn. destruct (existsb _ _) eqn:He; [discriminate | exact Hn]. }
  assert (HS : forall p v, tget p (put_w lit (rg_cont R) k0 C 8) = Some v ->
             (existsb (fun i => Pos.eqb p (Pos.of_nat (Pos.to_nat k0 + i))) (List.seq 0 8) = true /\ v = wcell lit C (Pos.to_nat p - Pos.to_nat k0)) \/
             tget p (rg_cont R) = Some v).
  { intros p v Hp. rewrite tget_put_w in Hp. destruct (existsb _ _) eqn:He; [left; split; [reflexivity | injection Hp as <-; reflexivity] | right; exact Hp]. }
  destruct Hok as (Hs & Hw & Hbytes & Hc). cbn [rg_base rg_size rg_kind rg_cont] in *. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont].
  unfold rsz in *. cbn [rg_size] in *.
  split; [exact Hs|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hbytes i Hi). destruct (rg_kind R); try exact Hbytes.
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
    + destruct Hbytes as [H1 H2]. split; [exact H1|]. intros Hn. apply H2. exact (HT _ Hn).
  - intros p v Hp. destruct (HS p v Hp) as [[He ->]|Hp']; [|exact (Hc p v Hp')].
    apply existsb_exists in He as (j & Hj & Hpj). apply Pos.eqb_eq in Hpj. subst p. specialize (Hall j Hj). apply in_seq in Hj.
    pose proof (Pos2Nat.is_pos k0) as Hk0.
    assert (Hpz : Zpos (Pos.of_nat (Pos.to_nat k0 + j)) = Zpos k0 + Z.of_nat j).
    { rewrite <- (Pos2Nat.id k0) at 2. rewrite <- !positive_nat_Z. rewrite Nat2Pos.id by lia. rewrite Pos2Nat.id. lia. }
    rewrite Nat2Pos.id by lia. replace (Pos.to_nat k0 + j - Pos.to_nat k0)%nat with j by lia.
    assert (Hbd : bden E (wcell lit C j) = Z_to_bv 8 (Z.shiftr C (8 * Z.of_nat j))) by (apply bden_wcell; lia).
    rewrite Hbd. split; [rewrite Hpz; lia|].
    unfold cbytei in Hall. destruct (tget (Pos.of_nat (Pos.to_nat k0 + j)) (rg_cont R)) as [[b|l j']|] eqn:Ht.
    + apply Z.eqb_eq in Hall. destruct (Hc _ _ Ht) as [_ Hv]. rewrite Hv. cbn [bden]. f_equal. apply bv8_mod. exact Hall.
    + destruct (irange fs l) as [lo hi] eqn:Hir. pose proof (irange_sound E fs l HF) as Rl. rewrite Hir in Rl. cbn [fst snd] in Rl.
      destruct (Hc _ _ Ht) as [_ Hv]. rewrite Hv. cbn [bden].
      destruct (Z.eqb lo hi && Z.leb 0 j')%bool eqn:Hj'.
      * apply andb_prop in Hj' as [Hlh _]. apply Z.eqb_eq in Hlh. apply Z.eqb_eq in Hall. replace (bv_unsigned (lden E l)) with lo by lia.
        f_equal. apply bv8_mod. exact Hall.
      * destruct (Z.leb 0 lo && Z.leb 0 j' && Z.ltb hi (2 ^ (8 * j')))%bool eqn:Hsm; [|discriminate].
        apply andb_prop in Hsm as [Hsm Hs3]. apply andb_prop in Hsm as [Hs1 Hs2]. apply Z.leb_le in Hs1, Hs2. apply Z.ltb_lt in Hs3. apply Z.eqb_eq in Hall.
        assert (Hsh0 : Z.shiftr (bv_unsigned (lden E l)) (8 * j') = 0).
        { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
        rewrite Hsh0. f_equal. apply bv8_mod. exact Hall.
    + assert (Hi : 0 <= Zpos (Pos.of_nat (Pos.to_nat k0 + j)) - 1 < bv_unsigned (lden E (rg_size R))) by (rewrite Hpz, Hrsz; lia).
      assert (Hok' : okey (Zpos (Pos.of_nat (Pos.to_nat k0 + j)) - 1) = Pos.of_nat (Pos.to_nat k0 + j)) by (unfold okey; rewrite Z.sub_add; reflexivity).
      destruct (rg_kind R) eqn:Hk; try discriminate.
      * (* [comment removed for export] *) apply Z.eqb_eq in Hall.
        specialize (Hbytes _ Hi). cbn beta iota in Hbytes. destruct Hbytes as [_ H2].
        rewrite Hok' in H2. rewrite (H2 Ht). f_equal. apply bv8_mod. rewrite <- Hall. reflexivity.
      * (* [comment removed for export] *)
        destruct (is_const (rg_base R)) as [A|] eqn:HA; [|discriminate].
        destruct (img_bytes img (A + (Zpos (Pos.of_nat (Pos.to_nat k0 + j)) - 1)) 1) as [[|b [|b' r]]|] eqn:Hib; try discriminate.
        destruct (Z.leb 0 A) eqn:HA0; [|discriminate]. apply Z.leb_le in HA0. apply Z.eqb_eq in Hall.
        destruct (is_const_sound E _ A HA) as [HAv HAr].
        assert (HbA : bv_unsigned (lden E (rg_base R)) = A) by (rewrite HAv; apply u_small64; exact HAr).
        specialize (Hbytes _ Hi). cbn beta iota in Hbytes. destruct Hbytes as [_ H2].
        rewrite Hok' in H2. rewrite (H2 Ht). rewrite HbA.
        assert (Hge : 0 <= A + (Zpos (Pos.of_nat (Pos.to_nat k0 + j)) - 1)) by lia.
        destruct (img_bytes_spec segs img 1 _ _ Himg Hge Hib) as [_ Hn]. specialize (Hn O b eq_refl). rewrite Z.add_0_r in Hn.
        rewrite Hn. f_equal. apply bv8_mod. exact Hall.
Qed.

Section NormWI.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Himg : img_ok segs img.

#[using="Himg"] Theorem den_normwi : forall lit model0 E S M ms model i k0 S', DEN segs LIMIT model0 mem0 E S M ms model -> normwi_at img lit S i k0 = Some S' ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros lit model0 E S M ms model i k0 S' Hd Hp. unfold normwi_at in Hp.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (normwi_rg img lit (s_facts S) R k0) as [R'|] eqn:Hr; [|discriminate].
  injection Hp as <-.
  assert (HR' : rg_base R' = rg_base R /\ rg_size R' = rg_size R /\ rg_kind R' = rg_kind R).
  { unfold normwi_rg in Hr. destruct (cwordi img (is_const (rg_base R)) (s_facts S) (rg_kind R) (rg_cont R) k0 8); [|discriminate]. destruct (cwordi_ok img (s_facts S) R k0 z); [|discriminate]. injection Hr as <-. cbn. tauto. }
  destruct HR' as (Hb' & Hs' & Hk').
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (S2 := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i R') (s_facts S) (s_next S) (s_resv S)).
  assert (Hshape : shape (s_rgs S2) = shape (s_rgs S)) by (cbn [S2 s_rgs]; exact (shape_upd (s_rgs S) i R' R Hi Hb' Hs')).
  constructor; try assumption.
  - intros E'' Ha''. destruct (Hsd E'' Ha'') as (H1 & H2 & H3 & H4 & HG & HD & HF & H8).
    unfold sden0. cbn [S2 s_pc s_regs s_rgs s_facts s_resv].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|split; [|split; [exact HF | exact H8]]].
    + apply Forall_forall. intros R0 HR0. destruct (In_nth_error _ _ HR0) as (j & Hj).
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-.
        exact (normwi_rg_ok segs img lit E'' _ (s_facts S) R k0 R' Himg HF Hr (proj1 (Forall_nth' _ _) HG i R Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. rewrite Forall_forall in HG. exact (HG R0 (nth_error_In _ _ Hj)).
    + eapply rgs_disj_upd; [exact Hi | exact Hb' | exact Hs' | exact HD].
  - eapply bases_wf_shape; [|exact Hshape|exact Hbw]. cbn [S2 s_next]. lia.
  - intros w Hw Hout' Hnow. apply (Hzr w Hw); [|exact Hnow].
    exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Hout').
  - exact (rl_ok_agree_shape (s_next S) E E model model (s_rgs S) _ Hbw (agree_refl _ _) Hshape eq_refl Hrl).
  - apply (frz_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl eq_refl); [| | exact Hfrz].
    + intros w _ Ho'. unfold outside in *. rewrite Forall_forall in *. intros R0 HR0.
      destruct (In_nth_error _ _ HR0) as (j & Hj). cbn [S2 s_rgs] in Hj.
      destruct (Nat.eq_dec j i) as [->|Hne].
      * rewrite (nth_upd_same _ _ _ _ Hi) in Hj. injection Hj as <-. unfold rsz in *. rewrite Hb', Hs'. exact (Ho' R (nth_error_In _ _ Hi)).
      * rewrite (nth_upd_other _ _ _ _ (not_eq_sym Hne)) in Hj. exact (Ho' R0 (nth_error_In _ _ Hj)).
    + intros w _ _. reflexivity.
  - apply (own_keep mem0 E E S S2 M M ms ms model model Hwf (agree_refl _ _) eq_refl); [| | | exact Hown].
    + intros w Ho'. exact (outside_agree_shape (s_next S) E E (s_rgs S) _ _ Hbw (agree_refl _ _) Hshape Ho').
    + intros w _. reflexivity.
    + intros x Hx. exact Hx.
Qed.
End NormWI.
(* [comment removed for export] *)
