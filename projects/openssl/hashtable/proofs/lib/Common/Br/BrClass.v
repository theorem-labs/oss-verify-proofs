(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxDrive FxDrive3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound CxOpt.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrRevLedger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive rclass : Set := RCHull | RCTop | RCEnt (i : nat) | RCSpan.

Definition class_neq (c1 c2 : rclass) : bool :=
  match c1, c2 with
  | RCEnt i, RCEnt j => negb (Nat.eqb i j)
  | RCHull, RCHull | RCTop, RCTop | RCSpan, RCSpan => false
  | _, _ => true
  end.

(* [comment removed for export] *)
Definition span_lit (am : CAP.amap) : option (Z * Z) :=
  match CAP.am_base am, CAP.am_len am with
  | AX2.ELit b, AX2.ELit l =>
      if (span_lo <=? b) && (b <? span_hi) && (0 <=? l) && (b + l <? 2 ^ 64) then Some (b, b + l) else None
  | _, _ => None
  end.
Definition is_span_lit (am : CAP.amap) : bool := match span_lit am with Some _ => true | None => false end.
Definition span_lits (ms : list CAP.amap) : list (Z * Z) :=
  flat_map (fun am => match span_lit am with Some p => [p] | None => [] end) ms.
Fixpoint span_cover (l : list (Z * Z)) (fuel : nat) (pos hi : Z) : bool :=
  if hi <=? pos then true else
  match fuel with
  | O => false
  | Datatypes.S f => match List.find (fun p => (fst p <=? pos) && (pos <? snd p)) l with
                     | Some p => span_cover l f (snd p) hi
                     | None => false
                     end
  end.
Lemma span_cover_sound : forall l fuel pos hi, span_cover l fuel pos hi = true ->
  forall z, pos <= z < hi -> exists p, In p l /\ fst p <= z < snd p.
Proof.
  intros l. induction fuel as [|f IH]; intros pos hi Hc z Hz; cbn [span_cover] in Hc;
    (destruct (hi <=? pos) eqn:Eh; [apply Z.leb_le in Eh; lia|]); [discriminate|].
  destruct (List.find (fun p => (fst p <=? pos) && (pos <? snd p)) l) as [p|] eqn:Ef; [|discriminate].
  destruct (List.find_some _ _ Ef) as [Hin Hp]. apply andb_prop in Hp as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Z_lt_dec z (snd p)) as [Hlt|Hge].
  - exists p. split; [exact Hin | lia].
  - apply (IH (snd p) hi Hc z). lia.
Qed.

Section Class.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Hypothesis HULL_ok : CXS.hull_ok A.
Variable TT : ttab_e.

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).

(* [comment removed for export] *)
Definition span_chk : bool :=
  span_cover (span_lits (CAP.a_maps CS)) (Datatypes.S (length (CAP.a_maps CS))) span_lo span_hi.

(* [comment removed for export] *)
Definition class_chk (t lo len : int) (c : rclass) : bool :=
  match c with
  | RCHull => (t =? 0)%uint63 && (CAP.img_lo A <=? to_Z lo) && (to_Z len <=? CAP.img_hi A)
  | RCTop =>
      let lt := AX2.lin_of (tte TT t) in let ls := AX2.lin_of CAP.e_spw in
      let delta := AX2.snorm (fst lt - fst ls) in
      lin_match lt ls delta && (- 8388608 <=? delta) && (delta <? 2 ^ 62)
  | RCEnt i =>
      match nth_error (CAP.a_maps CS) i with
      | Some am =>
          match CAP.am_len am with
          | AX2.ELit l =>
              let lt := AX2.lin_of (tte TT t) in let lm := AX2.lin_of (CAP.am_base am) in
              let delta := AX2.snorm (fst lt - fst lm) in
              ((lin_match lt lm delta && (0 <=? delta + to_Z lo) && (delta + to_Z len <=? l))
               || CAP.xinsideJ (CAP.kn CS) (tte TT t) (to_Z lo) (AX2.ELit (to_Z len - to_Z lo)) (CAP.am_base am) 0 (CAP.am_len am))
              && (0 <=? l) && (l <? 2 ^ 63) && negb (is_span_lit am)
          | _ => false
          end
      | None => false
      end
  | RCSpan =>
      span_chk && (CAP.img_hi A <=? span_lo)
      && match AX2.base_range (CAP.kn CS) (tte TT t) with
         | Some (blo, bhi) => (span_lo <=? blo + to_Z lo) && (bhi + to_Z len <=? span_hi)
         | None => false
         end
  end.

Definition class_sem (c : rclass) (x : Z) : Prop :=
  match c with
  | RCHull => CAP.img_lo A <= x < CAP.img_hi A
  | RCTop => alloc_top V <= x
  | RCEnt i => exists p am, nth_error (vm_maps V) i = Some p /\ nth_error (CAP.a_maps CS) i = Some am
                            /\ is_span_lit am = false /\ e_lo p <= x < e_hi p
  | RCSpan => span_lo <= x < span_hi /\ span_chk = true /\ CAP.img_hi A <= span_lo
  end.

Lemma maps_nth i am : nth_error (CAP.a_maps CS) i = Some am -> nth_error (vm_maps V) i = Some (CXS.amap_den E am).
Proof.
  intros Hn. rewrite (CxOpt.maps_exact_D1 E _ _ Hlx (CXS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)).
  rewrite nth_error_map, Hn. reflexivity.
Qed.

Lemma rho_lin t : AX2S.eqm (AX2S.lden E (AX2.lin_of (tte TT t))) (bv_unsigned (rho t)).
Proof. rewrite (rho_tte E TT t). apply AX2S.lin_of_sound. Qed.

Theorem class_chk_sound t lo len c :
  class_chk t lo len c = true ->
  bv_unsigned (rho t) + to_Z len < 2 ^ 63 ->
  forall x, bv_unsigned (rho t) + to_Z lo <= x < bv_unsigned (rho t) + to_Z len -> class_sem c x.
Proof.
  intros Hc Hnw x Hx. pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range lo) as Hlo0. pose proof (i63_range len) as Hl0.
  destruct c as [| |i|]; cbn [class_chk class_sem] in *.
  4:{ apply andb_prop in Hc as [Hc Hb]. apply andb_prop in Hc as [Hsp Hih]. apply Z.leb_le in Hih.
      destruct (AX2.base_range (CAP.kn CS) (tte TT t)) as [[blo bhi]|] eqn:Hr; [|discriminate].
      apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
      destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ blo bhi (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hr) as [Hblo Hbhi].
      rewrite <- (rho_tte E TT t) in Hblo, Hbhi. split; [lia|]. split; [exact Hsp | exact Hih]. }
  - apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Ht H1]. apply Uint63.eqb_spec in Ht. subst t.
    apply Z.leb_le in H1, H2. rewrite (rho_of_0 TT E) in Hx. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hx. lia.
  - cbv zeta in Hc. apply andb_prop in Hc as [Hc Hd2]. apply andb_prop in Hc as [Hlm Hd1].
    apply Z.leb_le in Hd1. apply Z.ltb_lt in Hd2.
    pose proof (lin_match_sound E _ _ _ Hlm) as Hq.
    pose proof (AX2S.lin_of_sound E CAP.e_spw) as Hs. pose proof (rho_lin t) as Hr.
    destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Hisp Hspw].
    destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 Htop2].
    unfold alloc_top, stack_max_size in *. rewrite Hisp in *. unfold CAP.CEIL, CAP.TOPMAX in *.
    set (delta := AX2.snorm (fst (AX2.lin_of (tte TT t)) - fst (AX2.lin_of CAP.e_spw))) in *.
    assert (Er : bv_unsigned (rho t) = ISP + delta).
    { apply br_eqm_small; [|exact Hu|lia].
      destruct Hq as [q1 Hq1]. destruct Hs as [q2 Hs2]. destruct Hr as [q3 Hr3].
      change (AX2S.uE E CAP.e_spw) with (CXS.uE E CAP.e_spw) in Hs2. rewrite Hspw in Hs2.
      exists (q1 + q2 - q3). lia. }
    lia.
  - destruct (nth_error (CAP.a_maps CS) i) as [am|] eqn:Hn; [|discriminate].
    destruct (CAP.am_len am) as [l| | | | | | |] eqn:El; try discriminate. cbv zeta in Hc.
    apply andb_prop in Hc as [Hc Hns]. apply negb_true_iff in Hns.
    apply andb_prop in Hc as [Hc Hl2]. apply andb_prop in Hc as [Hways Hl1]. apply Z.leb_le in Hl1. apply Z.ltb_lt in Hl2.
    pose proof (maps_nth i am Hn) as Hv.
    pose proof (proj1 (Forall_forall _ _) (CXS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ (nth_error_In _ _ Hv)) as Hb.
    cbv beta in Hb. unfold CXS.amap_den in Hb. cbn [fst snd] in Hb. rewrite El in Hb. cbn [AX2.edenot] in Hb.
    rewrite (br_lit_small l) in Hb by lia. destruct Hb as (_ & _ & _ & _ & Htop).
    destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [_ Htop2]. unfold CAP.TOPMAX in Htop2.
    set (b := bv_unsigned (AX2.edenot E (CAP.am_base am))) in *. pose proof (br_u64 (AX2.edenot E (CAP.am_base am))) as Hbu. fold b in Hbu.
    unfold alloc_top, stack_max_size in Htop, Htop2.
    assert (Hin : b <= x < b + l).
    { apply orb_prop in Hways as [Hlin|Hxi].
      - apply andb_prop in Hlin as [Hlin Hd2]. apply andb_prop in Hlin as [Hlm Hd1]. apply Z.leb_le in Hd1, Hd2.
        pose proof (lin_match_sound E _ _ _ Hlm) as Hq.
        pose proof (AX2S.lin_of_sound E (CAP.am_base am)) as Hs. pose proof (rho_lin t) as Hr.
        set (delta := AX2.snorm (fst (AX2.lin_of (tte TT t)) - fst (AX2.lin_of (CAP.am_base am)))) in *.
        assert (Er : bv_unsigned (rho t) + to_Z lo = b + (delta + to_Z lo)).
        { apply br_eqm_small; [|lia|].
          2:{ assert (H1 : to_Z lo < to_Z len) by lia. assert (H2 : delta + to_Z lo < l) by lia.
              assert (H3 : b + l <= 140737479966720) by lia. lia. }
          destruct Hq as [q1 Hq1]. destruct Hs as [q2 Hs2]. destruct Hr as [q3 Hr3]. unfold AX2S.uE in Hs2. fold b in Hs2.
          exists (q1 + q2 - q3). lia. }
        lia.
      - destruct (CXS.xinsideJ_sound segs E _ (CAP.kn CS) _ _ _ _ _ _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hxi) as [X1 X2].
        unfold AX2S.estart, AX2S.elenZ in X1, X2. cbn [AX2.a_base AX2.a_off] in X1, X2. rewrite ?El in X2. cbn [AX2.edenot] in X2.
        rewrite <- (rho_tte E TT t) in X1, X2. fold b in X1, X2.
        assert (Hlt : to_Z lo < to_Z len) by lia.
        rewrite (br_lit_small (to_Z len - to_Z lo)), (br_lit_small l) in X2 by lia. lia. }
    exists (CXS.amap_den E am), am. split; [exact Hv|]. split; [reflexivity|]. split; [exact Hns|].
    unfold e_hi, e_sz, e_lo, CXS.amap_den. cbn [fst snd]. rewrite El. cbn [AX2.edenot]. rewrite (br_lit_small l) by lia.
    fold b. exact Hin.
Qed.

(* [comment removed for export] *)
Definition top_delta (t : int) : Z := AX2.snorm (fst (AX2.lin_of (tte TT t)) - fst (AX2.lin_of CAP.e_spw)).

Lemma class_top_rho t lo len : class_chk t lo len RCTop = true -> bv_unsigned (rho t) = ISP + top_delta t.
Proof.
  intros Hc. pose proof (br_u64 (rho t)) as Hu. cbn [class_chk] in Hc. cbv zeta in Hc.
  apply andb_prop in Hc as [Hc Hd2]. apply andb_prop in Hc as [Hlm Hd1].
  apply Z.leb_le in Hd1. apply Z.ltb_lt in Hd2.
  pose proof (lin_match_sound E _ _ _ Hlm) as Hq.
  pose proof (AX2S.lin_of_sound E CAP.e_spw) as Hs. pose proof (rho_lin t) as Hr.
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Hisp Hspw].
  destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 Htop2].
  unfold alloc_top, stack_max_size in *. rewrite Hisp in *. unfold CAP.CEIL, CAP.TOPMAX in *.
  unfold top_delta. set (delta := AX2.snorm (fst (AX2.lin_of (tte TT t)) - fst (AX2.lin_of CAP.e_spw))) in *.
  apply br_eqm_small; [|exact Hu|lia].
  destruct Hq as [q1 Hq1]. destruct Hs as [q2 Hs2]. destruct Hr as [q3 Hr3].
  change (AX2S.uE E CAP.e_spw) with (CXS.uE E CAP.e_spw) in Hs2. rewrite Hspw in Hs2.
  exists (q1 + q2 - q3). lia.
Qed.

(* [comment removed for export] *)
Lemma span_lit_in q : In q (span_lits (CAP.a_maps CS)) ->
  exists j am, nth_error (CAP.a_maps CS) j = Some am /\ span_lit am = Some q
               /\ nth_error (vm_maps V) j = Some (CXS.amap_den E am)
               /\ e_lo (CXS.amap_den E am) = fst q /\ e_hi (CXS.amap_den E am) = snd q.
Proof.
  unfold span_lits. intros Hq. apply in_flat_map in Hq as (am & Ham & Hq).
  destruct (span_lit am) as [q'|] eqn:Esl; [|destruct Hq]. destruct Hq as [<-|[]].
  destruct (In_nth_error _ _ Ham) as [j Hj]. exists j, am. split; [exact Hj|]. split; [exact Esl|].
  split; [exact (maps_nth j am Hj)|].
  unfold span_lit in Esl. destruct (CAP.am_base am) as [b| | | | | | |] eqn:Eb; try discriminate.
  destruct (CAP.am_len am) as [l| | | | | | |] eqn:El; try discriminate.
  destruct ((span_lo <=? b) && (b <? span_hi) && (0 <=? l) && (b + l <? 2 ^ 64)) eqn:Ec; [|discriminate]. injection Esl as <-.
  apply andb_prop in Ec as [Ec E4]. apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2].
  apply Z.leb_le in E1, E3. apply Z.ltb_lt in E2, E4. unfold span_lo in E1.
  unfold e_hi, e_sz, e_lo, CXS.amap_den. cbn [fst snd]. rewrite Eb, El. cbn [AX2.edenot].
  rewrite (br_lit_small b), (br_lit_small l) by lia. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seps_nth : forall (l : list (word * word)) i j p q,
  CXS.seps l -> i <> j -> nth_error l i = Some p -> nth_error l j = Some q -> CXS.iv_disjoint p q.
Proof.
  intros l i j p q Hs. revert i j. induction Hs as [|p0 l Hp _ IH]; intros i j Hne Hi Hj; [destruct i; discriminate|].
  destruct i as [|i], j as [|j]; cbn [nth_error] in Hi, Hj.
  - contradiction.
  - injection Hi as <-. exact (proj1 (Forall_forall _ _) Hp q (nth_error_In _ _ Hj)).
  - injection Hj as <-. pose proof (proj1 (Forall_forall _ _) Hp p (nth_error_In _ _ Hi)) as Hd.
    unfold CXS.iv_disjoint in *. lia.
  - apply (IH i j); [lia | exact Hi | exact Hj].
Qed.

Theorem class_apart c1 c2 x : class_neq c1 c2 = true -> class_sem c1 x -> class_sem c2 x -> False.
Proof.
  destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 _]. unfold CAP.CEIL in Htop1.
  destruct HULL_ok as (_ & _ & _ & Hkhi). unfold CAP.KHI in Hkhi.
  assert (Hent : forall i, class_sem (RCEnt i) x ->
            (x < CAP.img_lo A \/ CAP.img_hi A <= x) /\ x < alloc_top V).
  { intros i (p & am & Hp & _ & _ & Hx). 
    pose proof (proj1 (Forall_forall _ _) (CXS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ (nth_error_In _ _ Hp)) as Hb.
    cbv beta in Hb. unfold e_hi, e_sz, e_lo in Hx. destruct Hb as (_ & _ & _ & Hh & Ht). lia. }
  assert (Hse : forall i, class_sem (RCEnt i) x -> class_sem RCSpan x -> False).
  { intros i (p & am & Hp & Ham & Hns & Hxp) (Hx & Hsc & _).
    destruct (span_cover_sound _ _ _ _ Hsc x Hx) as (q & Hq & Hxq).
    destruct (span_lit_in q Hq) as (j & am' & Hj & Esl & Hvj & Elo & Ehi).
    assert (Hij : i <> j).
    { intros <-. rewrite Ham in Hj. injection Hj as <-. unfold is_span_lit in Hns. rewrite Esl in Hns. discriminate. }
    pose proof (seps_nth _ i j p _ (CXS.co_seps _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hij Hp Hvj) as Hd.
    unfold CXS.iv_disjoint in Hd. unfold e_hi, e_sz, e_lo in Hxp, Elo, Ehi. lia. }
  destruct c1 as [| |i|], c2 as [| |j|]; cbn [class_neq] in *; try discriminate; intros Hneq H1 H2;
    try (exact (Hse _ H1 H2)); try (exact (Hse _ H2 H1));
    try (cbn [class_sem] in H1, H2; unfold span_hi, span_lo in *; lia);
    try (destruct (Hent _ H1) as [Ha Hb]; cbn [class_sem] in H2; lia);
    try (destruct (Hent _ H2) as [Ha Hb]; cbn [class_sem] in H1; lia).
  (* [comment removed for export] *)
  destruct (Nat.eqb i j) eqn:Eij; [discriminate|]. apply Nat.eqb_neq in Eij.
  cbn [class_sem] in H1, H2. destruct H1 as (p & _ & Hp & _ & _ & Hxp). destruct H2 as (q & _ & Hq & _ & _ & Hxq).
  pose proof (seps_nth _ i j p q (CXS.co_seps _ _ _ _ _ _ _ _ _ _ _ _ HCS) Eij Hp Hq) as Hd.
  unfold CXS.iv_disjoint in Hd. unfold e_hi, e_sz, e_lo in Hxp, Hxq. lia.
Qed.

(* [comment removed for export] *)
Hypothesis RES_cover : forall z, CAP.img_lo A <= z < CAP.img_hi A -> CXS.in_ivs z (segments_reserved segs) = true.

Theorem class_covered c x : class_sem c x -> covered V x.
Proof.
  destruct c as [| |i|]; cbn [class_sem]; intros Hx.
  4:{ destruct Hx as (Hx & Hsc & _). destruct (span_cover_sound _ _ _ _ Hsc x Hx) as (q & Hq & Hxq).
      destruct (span_lit_in q Hq) as (j & am' & _ & _ & Hvj & Elo & Ehi).
      left. exists (CXS.amap_den E am'). split; [apply in_or_app; right; exact (nth_error_In _ _ Hvj) | lia]. }
  - left. pose proof (RES_cover x Hx) as Hin. unfold CXS.in_ivs in Hin. apply existsb_exists in Hin as (r & Hr & Hz).
    apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2.
    exists r. split.
    + apply in_or_app. left. rewrite (CXS.co_res _ _ _ _ _ _ _ _ _ _ _ _ HCS). exact Hr.
    + unfold e_hi, e_sz, e_lo. lia.
  - right. exact Hx.
  - left. destruct Hx as (p & _ & Hp & _ & _ & Hxp). exists p. split; [apply in_or_app; right; exact (nth_error_In _ _ Hp) | exact Hxp].
Qed.
End Class.
