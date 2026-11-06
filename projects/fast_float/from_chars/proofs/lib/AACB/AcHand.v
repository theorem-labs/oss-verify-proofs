(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW.

Module AcMrg0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan FxFrame.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Theorem mrg_check0 : forall t img depth p L finals S E ms,
  tbl_ok segs t -> img_ok segs img -> check t img (pvars L) depth p L = Some finals ->
  state_wf L = true -> (s_next S <= s_next L)%positive ->
  sden segs E (mrg L S) ms ->
  exists L' ms' E', In L' finals /\ isteps segs ms ms' /\ sden segs E' (mrg L' S) ms' /\
    agree (s_next L) E E' /\
    (forall x, outside E (s_rgs (mrg L S)) x -> ms_mem ms' x = ms_mem ms x) /\
    shape (s_rgs (mrg L' S)) = shape (s_rgs (mrg L S)) /\
    (s_next L <= s_next L')%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p L finals S E ms Ht Himg Hck HwL HnS Hd.
  assert (HdL : sden segs E L ms).
  { intros E' Ha. destruct (Hd E' Ha) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    cbn [mrg s_pc s_regs s_rgs s_facts s_resv] in *. apply Forall_app in A5 as [A5 _]. apply Forall_app in A7 as [A7 _].
    apply rgs_disj_app_iff in A6 as (A6 & _ & _). unfold sden0. tauto. }
  assert (Hbw : bases_wf (s_next L) (s_rgs L) = true).
  { unfold state_wf in HwL. apply andb_prop in HwL as [HwL _]. apply andb_prop in HwL as [HwL _]. apply andb_prop in HwL as [_ Hg].
    unfold bases_wf. rewrite forallb_forall in *. intros R HR. specialize (Hg R HR). unfold rwf in Hg.
    apply andb_prop in Hg as [Hg _]. exact Hg. }
  assert (Hbi : bases_ins (pvars L) (s_rgs L) = true).
  { unfold bases_ins. rewrite forallb_forall. intros R HR. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw.
    specialize (Hbw R HR). apply andb_prop in Hbw as [Hb Hs]. rewrite forallb_forall. intros [y c] Hy.
    apply existsb_exists. exists y. split; [|apply Pos.eqb_refl]. apply in_pvars.
    apply in_app_iff in Hy as [Hy|Hy]; [unfold lwf in Hb; rewrite forallb_forall in Hb; specialize (Hb _ Hy) |
      unfold lwf in Hs; rewrite forallb_forall in Hs; specialize (Hs _ Hy)]; cbn in *; apply Pos.ltb_lt; assumption. }
  destruct (check_frame segs t img (pvars L) depth p L finals Ht Himg Hck E ms HdL Hbw Hbi)
    as (L' & ms' & E1 & HL' & Hst & Hd1 & Hins & Hfr & Hsh & Hn).
  assert (Ha : agree (s_next L) E E1) by (intros y Hy; symmetry; apply Hins; apply in_pvars; exact Hy).
  assert (Hfr' : forall x, outside E (s_rgs (mrg L S)) x -> ms_mem ms' x = ms_mem ms x).
  { intros x Hx. apply Hfr. unfold outside in *. cbn [mrg s_rgs] in Hx. apply Forall_app in Hx as [Hx _]. exact Hx. }
  exists L', ms', E1. split; [exact HL'|]. split; [exact Hst|]. split; [|split; [exact Ha|split; [exact Hfr'|split; [|exact Hn]]]].
  2: { cbn [mrg s_rgs]. unfold shape in *. rewrite !map_app. f_equal. exact Hsh. }
  intros E'' Ha''.
  assert (Ha0 : agree (s_next L) E E'') by (intros x Hx; rewrite (Ha x Hx); apply Ha''; cbn [mrg s_next]; lia).
  destruct (Hd E'' Ha0) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). cbn [mrg s_pc s_regs s_rgs s_facts s_resv] in B5, B6, B7.
  apply Forall_app in B5 as [B5L B5S]. apply Forall_app in B7 as [_ B7S]. apply rgs_disj_app_iff in B6 as (_ & B6S & B6X).
  destruct (Hd1 E'' ltac:(cbn [mrg s_next] in Ha''; exact Ha'')) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  (* [comment removed for export] *)
  assert (HbL : forall R', In R' (s_rgs L') -> exists R, In R (s_rgs L) /\
            bv_unsigned (lden E'' (rg_base R')) = bv_unsigned (lden E'' (rg_base R)) /\ rsz E'' R' = rsz E'' R).
  { intros R' HR'. unfold shape in Hsh. destruct (In_nth_error _ _ HR') as [k Hk].
    assert (Hk' : nth_error (List.map (fun R : region => (rg_base R, rg_size R)) (s_rgs L')) k = Some (rg_base R', rg_size R'))
      by (rewrite nth_error_map, Hk; reflexivity).
    rewrite Hsh, nth_error_map in Hk'. destruct (nth_error (s_rgs L) k) as [R|] eqn:HkL; [|discriminate].
    cbn [option_map] in Hk'. injection Hk' as Eb Ez. exists R. split; [exact (nth_error_In _ _ HkL)|].
    unfold rsz. rewrite Eb, Ez. split; reflexivity. }
  unfold sden0. cbn [mrg s_pc s_regs s_rgs s_facts s_resv].
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
  split; [|split; [|split; [|exact C8]]].
  - apply Forall_app. split; [exact C5|]. rewrite Forall_forall in B5S |- *. intros R HR.
    apply (rg_ok_mem_eq' segs E'' (ms_mem ms)); [exact (B5S R HR)|]. intros i Hi.
    destruct (B5S R HR) as (Hz & Hw & _).
    apply Hfr. apply (proj1 (outside_agree (s_next L) E'' E (s_rgs L) _ Hbw (fun y Hy => eq_sym (Ha0 y Hy)))).
    unfold outside. rewrite Forall_forall. intros R0 HR0. rewrite Forall_forall in B6X.
    pose proof (B6X _ HR0) as HX0. rewrite Forall_forall in HX0. pose proof (HX0 R HR) as HX.
    unfold rg_disj in HX. cbv zeta in HX.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
    pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as BB. change (bv_modulus 64) with two64 in BB.
    rewrite Z.mod_small by lia. lia.
  - apply rgs_disj_app_iff. split; [exact C6|]. split; [exact B6S|].
    rewrite Forall_forall. intros R' HR'. destruct (HbL R' HR') as (R & HR & Eb & Ez).
    rewrite Forall_forall in B6X. pose proof (B6X _ HR) as HX. rewrite Forall_forall in HX |- *.
    intros R2 HR2. specialize (HX R2 HR2). unfold rg_disj in HX |- *. cbv zeta in HX |- *. rewrite Eb, Ez. exact HX.
  - apply Forall_app. split; [exact C7 | exact B7S].
Qed.
End WithSegs.

Section Seg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_mrg_seg0 : forall t img depth p L finals S E M ms model T,
  tbl_ok segs t -> img_ok segs img -> check t img (pvars L) depth p L = Some finals -> state_wf L = true ->
  (s_next S <= s_next L)%positive ->
  DEN segs LIMIT model0 mem0 E (mrg L S) M ms model ->
  (forall L' E' ms' model', In L' finals -> DEN segs LIMIT model0 mem0 E' (mrg L' S) M ms' model' ->
     agree (s_next L) E E' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros t img depth p L finals S E M ms model T Ht Himg Hck HwL HnS Hd Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  destruct (mrg_check0 segs t img depth p L finals S E (restrict (Hof E M model) ms) Ht Himg Hck HwL HnS Hsd)
    as (L' & msr' & E1 & HL' & Hst & Hd' & Ha & Hfr & Hsh & Hn).
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E (mrg L S) M ms model T (mrg L' S) msr' E1
           Hd Hst Hd' Ha ltac:(cbn [mrg s_next]; lia) Hfr Hsh).
  intros E2 ms2 model2 HD2 Ha2. exact (Hk L' E2 ms2 model2 HL' HD2 Ha2).
Qed.
End Seg.
(* [comment removed for export] *)
End AcMrg0.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition empty_rg (R : region) : region :=
  RG (rg_base R) (rg_size R) (match rg_kind R with RT => RT | RO => RO | _ => RW end) TEmpty.
Fixpoint empty_at (W : list nat) (i : nat) (rgs : list region) : list region :=
  match rgs with [] => [] | R :: rs => (if existsb (Nat.eqb i) W then empty_rg R else R) :: empty_at W (Datatypes.S i) rs end.
Fixpoint hregs (R : tree lin) (K : list positive) (nx : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | Datatypes.S k' => let key := Pos.of_succ_nat k in
            hregs R K nx k' (rset acc key (if existsb (Pos.eqb key) K then rget R key else lvar (nx + key)))
  end.
Definition hand_post (L : sst) (q : Z) (K : list positive) (W : list nat) : sst :=
  SST q (hregs (s_regs L) K (s_next L) 31 TEmpty) (empty_at W 0 (s_rgs L)) (s_facts L) (s_next L + 33) RNone.

Lemma hregs_get : forall R K nx k acc key, (1 <= Pos.to_nat key - 1 <= k)%nat -> key <> xH ->
  rget (hregs R K nx k acc) key = if existsb (Pos.eqb key) K then rget R key else lvar (nx + key).
Proof.
  intros R K nx k. induction k as [|k IH]; intros acc key Hk Hne; [lia|]. cbn [hregs].
  destruct (Nat.eq_dec (Pos.to_nat key - 1) (Datatypes.S k)) as [He|He].
  - assert (Hkey : key = Pos.of_succ_nat (Datatypes.S k)) by (apply Pos2Nat.inj; rewrite SuccNat2Pos.id_succ; lia). subst key.
    (* [comment removed for export] *)
    assert (Hpres : forall k0 acc0 key0, (Pos.to_nat key0 - 1 > k0)%nat -> rget (hregs R K nx k0 acc0) key0 = rget acc0 key0).
    { intros k0. induction k0 as [|k0 IH0]; intros acc0 key0 H0; [reflexivity|]. cbn [hregs]. rewrite IH0 by lia.
      apply rget_rset_other. intros Hc. subst key0. rewrite SuccNat2Pos.id_succ in H0. lia. }
    rewrite Hpres by (rewrite SuccNat2Pos.id_succ; lia). apply rget_rset_same. exact Hne.
  - apply IH; [lia | exact Hne].
Qed.

Lemma empty_at_nth : forall W rgs i j R, nth_error (empty_at W i rgs) j = Some R ->
  exists R0, nth_error rgs j = Some R0 /\ R = (if existsb (Nat.eqb (i + j)) W then empty_rg R0 else R0).
Proof.
  intros W rgs. induction rgs as [|R0 rs IH]; intros i j R H; [destruct j; discriminate|].
  destruct j as [|j]; cbn [empty_at nth_error] in H.
  - injection H as <-. exists R0. split; [reflexivity|]. rewrite Nat.add_0_r. reflexivity.
  - destruct (IH (Datatypes.S i) j R H) as (R1 & H1 & H2). exists R1. split; [exact H1|]. rewrite H2.
    replace (Datatypes.S i + j)%nat with (i + Datatypes.S j)%nat by lia. reflexivity.
Qed.
Lemma empty_at_shape : forall W rgs i, shape (empty_at W i rgs) = shape rgs.
Proof. intros W rgs. induction rgs as [|R rs IH]; intros i; [reflexivity|]. cbn [empty_at shape List.map]. f_equal; [|exact (IH (Datatypes.S i))]. destruct (existsb _ W); reflexivity. Qed.
Lemma length_empty_at : forall W rgs i, length (empty_at W i rgs) = length rgs.
Proof. intros W rgs. induction rgs as [|R rs IH]; intros i; [reflexivity|]. cbn. f_equal. apply IH. Qed.

Lemma rkey_reg : forall r : reg, Z_to_bv 5 (Zpos (rkey r) - 1) = r.
Proof.
  intros r. unfold rkey, bv_key. pose proof (bv_unsigned_in_range _ r) as Hr. rewrite Z2Pos.id by lia.
  replace (bv_unsigned r + 1 - 1) with (bv_unsigned r) by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rgs_disj_same_shape : forall E l l', List.map (fun R => (rg_base R, rg_size R)) l' = List.map (fun R => (rg_base R, rg_size R)) l ->
  rgs_disj E l -> rgs_disj E l'.
Proof.
  intros E l. induction l as [|R rs IH]; intros [|R' rs'] Hs Hd; cbn in Hs; try discriminate; [exact I|].
  injection Hs as Hb Hz Hrs. destruct Hd as [Hx Hrd]. split; [|exact (IH rs' Hrs Hrd)].
  assert (Hm : forall l1 l2, List.map (fun R => (rg_base R, rg_size R)) l1 = List.map (fun R => (rg_base R, rg_size R)) l2 ->
             Forall (rg_disj E R) l2 -> Forall (rg_disj E R') l1).
  { intros l1. induction l1 as [|A l1 IH1]; intros [|B l2] H12 HF; cbn in H12; try discriminate; [constructor|].
    injection H12 as Eb Ez Er. inversion HF as [|? ? HB HF']; subst. constructor; [|exact (IH1 l2 Er HF')].
    unfold rg_disj, rsz in *. rewrite Hb, Hz, Eb, Ez. exact HB. }
  exact (Hm rs' rs Hrs Hx).
Qed.

Section Hand.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition hval (n : positive) (nL : positive) (E : valu) (regs' : bvmap 5 word) : valu :=
  fun x : positive => if Pos.ltb x (n + nL) then E x else getr regs' (Z_to_bv 5 (Zpos (x - (n + nL)) - 1)).

#[using="Type"] Lemma hand_sden : forall n L S E msr msr' q K W,
  sden segs E (mrg (sst_shift n L) S) msr ->
  state_wf L = true -> bases_wf (n + s_next L) (s_rgs S) = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  ms_pc_val msr' = Z_to_bv 64 q -> ms_svc_pending msr' = None -> ms_resv msr' = None -> ms_fcsr msr' = ms_fcsr msr ->
  (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs msr) r) ->
  (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg (vshift n E) R x) ->
     (exists R, In R (s_rgs (mrg (sst_shift n L) S)) /\ in_rg E R x) -> ms_mem msr' x = ms_mem msr x) ->
  (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz (vshift n E) R ->
     rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (vshift n E) (rg_base R)) + j)) <> None /\
     (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (vshift n E) (rg_base R)) + j)) <> None)) ->
  sden segs (hval n (s_next L) E (ms_regs msr')) (mrg (sst_shift n (hand_post L q K W)) S) msr'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n L S E msr msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep Hmem Hrw.
  set (nL := s_next L) in *.
  set (E' := hval n nL E (ms_regs msr')).
  assert (Ha : agree (n + nL) E E') by (intros x Hx; unfold E', hval; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  assert (HbW : forall R, In R (s_rgs L) -> forall E1 E2, agree (n + nL) E1 E2 ->
            lden (vshift n E1) (rg_base R) = lden (vshift n E2) (rg_base R) /\ rsz (vshift n E1) R = rsz (vshift n E2) R).
  { intros R HR E1 E2 H12. unfold state_wf in HwL. apply andb_prop in HwL as [HwL _]. apply andb_prop in HwL as [HwL _].
    apply andb_prop in HwL as [_ Hg]. rewrite forallb_forall in Hg. specialize (Hg R HR). unfold rwf in Hg.
    apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hb Hs].
    assert (Hv : agree nL (vshift n E1) (vshift n E2)) by (intros y Hy; unfold vshift; apply H12; lia).
    unfold rsz. rewrite (lden_agree nL _ _ _ Hb Hv), (lden_agree nL _ _ _ Hs Hv). split; reflexivity. }
  intros E'' Ha''.
  assert (Ha0 : agree (n + nL) E E'') by (intros x Hx; rewrite (Ha x Hx); apply Ha''; cbn [mrg sst_shift hand_post s_next]; fold nL; lia).
  pose proof (Hsd E'' Ha0) as HdE.
  destruct HdE as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). cbn [mrg s_pc s_regs s_rgs s_facts s_resv sst_shift] in B5, B6, B7, B4.
  unfold sden0. cbn [mrg sst_shift hand_post s_pc s_regs s_rgs s_facts s_resv].
  split; [rewrite Hpc; reflexivity|]. split; [exact Hsvc|]. split; [cbn [rsv_shift rsv_ok]; exact Hrsv|].
  split; [|split; [|split; [|split]]].
  + (* [comment removed for export] *)
    intros r. rewrite rget_shift, lden_shift. destruct (decide (r = 0%bv)) as [->|Hr0].
    * unfold getr. rewrite bv_eqb_refl. change (rkey 0%bv) with xH. cbn [rget]. reflexivity.
    * destruct (rkey_succ r Hr0) as (k & Hk1 & Ek).
      assert (Hkk : (1 <= Pos.to_nat (rkey r) - 1 <= 31)%nat) by (rewrite Ek, SuccNat2Pos.id_succ; lia).
      assert (Hnx : rkey r <> xH) by (intros Hc; apply Hr0; apply rkey_1; exact Hc).
      rewrite (hregs_get _ _ _ 31 _ (rkey r) Hkk Hnx).
      destruct (existsb (Pos.eqb (rkey r)) K) eqn:HK.
      -- rewrite (Hkeep r HK). specialize (B4 r). rewrite rget_shift, lden_shift in B4. exact B4.
      -- rewrite lden_lvar. unfold vshift. rewrite <- (Ha'' (n + (s_next L + rkey r))%positive) by (cbn [mrg sst_shift hand_post s_next]; lia).
         unfold E', hval. rewrite (proj2 (Pos.ltb_ge _ _)) by (unfold nL; lia).
         replace (n + (s_next L + rkey r) - (n + nL))%positive with (rkey r) by (unfold nL; lia). rewrite rkey_reg. reflexivity.
  + (* [comment removed for export] *)
    apply Forall_app. split.
    * apply Forall_forall. intros R' HR'. apply in_map_iff in HR' as (R1 & <- & HR1). apply In_nth_error in HR1 as (j & Hj).
      destruct (empty_at_nth W (s_rgs L) 0 j R1 Hj) as (R0 & HR0 & ER). cbn [Nat.add] in ER.
      assert (HR0in : In R0 (s_rgs L)) by exact (nth_error_In _ _ HR0).
      apply Forall_app in B5 as [B5L B5S]. rewrite Forall_map, Forall_forall in B5L. pose proof (B5L R0 HR0in) as Hok0.
      apply rg_ok_shift in Hok0. apply rg_ok_shift.
      destruct (HbW R0 HR0in E E'' Ha0) as [Eb Ez].
      destruct (existsb (Nat.eqb j) W) eqn:HjW.
      -- subst R1. apply existsb_exists in HjW as (i & Hi & Hij). apply Nat.eqb_eq in Hij. subst i.
         pose proof (HnRO j R0 Hi HR0) as HnR.
         destruct Hok0 as (H1 & H2 & _ & _). unfold rg_ok, empty_rg. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size] in *.
         split; [exact H1|]. split; [exact H2|]. split.
         ++ intros i Hi'. rewrite <- Ez in Hi'. destruct (Hrw j R0 i Hi HR0 Hi') as [Hr1 Hr2]. rewrite <- Eb.
            destruct (rg_kind R0); try (split; [exact Hr1 | apply Hr2; discriminate]); try exact Hr1; try (split; [split; [exact Hr1 | apply Hr2; discriminate] | intros; rewrite tget_empty in *; discriminate]).
            all: exfalso; apply HnR; reflexivity.
         ++ intros p v Hp. rewrite tget_empty in Hp. discriminate.
      -- subst R1. apply (rg_ok_mem_eq' segs _ (ms_mem msr)); [exact Hok0|]. intros i Hi. apply Hmem.
         2: { exists (rshift n R0). split; [cbn [mrg s_rgs sst_shift]; apply in_or_app; left; apply in_map; exact HR0in|].
              unfold in_rg. rewrite base_shift, rsz_shift, Eb, Ez. destruct Hok0 as (_ & H2 & _).
              rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
              pose proof (bv_unsigned_in_range _ (lden (vshift n E'') (rg_base R0))) as BB. change (bv_modulus 64) with two64 in BB.
              rewrite Z.mod_small by lia. lia. }
         intros (i0 & R2 & Hi0 & HR2 & Hin). assert (Hne : i0 <> j).
         { intros ->. assert (Hc : existsb (Nat.eqb j) W = true) by (apply existsb_exists; exists j; split; [exact Hi0 | apply Nat.eqb_refl]). congruence. }
         pose proof (rgs_disj_nth E'' _ i0 j _ _ (proj1 (proj1 (rgs_disj_app_iff E'' _ _) B6)) Hne
                       ltac:(rewrite nth_error_map, HR2; reflexivity) ltac:(rewrite nth_error_map, HR0; reflexivity)) as HD.
         rewrite rg_disj_shift in HD. unfold rg_disj in HD. cbv zeta in HD.
         destruct (HbW R2 (nth_error_In _ _ HR2) E E'' Ha0) as [Eb2 Ez2]. unfold in_rg in Hin. rewrite Eb2, Ez2 in Hin.
         destruct Hok0 as (_ & H2 & _). rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with two64 in Hin.
         pose proof (bv_unsigned_in_range _ (lden (vshift n E'') (rg_base R0))) as BB. change (bv_modulus 64) with two64 in BB.
         rewrite Z.mod_small in Hin by lia. lia.
    * apply Forall_app in B5 as [_ B5S]. rewrite Forall_forall in B5S |- *. intros R HR.
      apply (rg_ok_mem_eq' segs _ (ms_mem msr)); [exact (B5S R HR)|]. intros i Hi. apply Hmem.
      2: { exists R. split; [cbn [mrg s_rgs sst_shift]; apply in_or_app; right; exact HR|].
           unfold bases_wf in HbS. rewrite forallb_forall in HbS. destruct (andb_prop _ _ (HbS R HR)) as [Hb1 Hb2].
           unfold in_rg, rsz in *. rewrite (lden_agree (n + nL) E E'' _ Hb1 Ha0), (lden_agree (n + nL) E E'' _ Hb2 Ha0).
           destruct (B5S R HR) as (_ & H2 & _). unfold rsz in H2.
           rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
           pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as BB. change (bv_modulus 64) with two64 in BB.
           rewrite Z.mod_small by lia. lia. }
      intros (i0 & R2 & Hi0 & HR2 & Hin).
      apply rgs_disj_app_iff in B6 as (_ & _ & BX). rewrite Forall_map, Forall_forall in BX.
      pose proof (BX R2 (nth_error_In _ _ HR2)) as BX2. rewrite Forall_forall in BX2. specialize (BX2 R HR).
      unfold rg_disj in BX2. cbv zeta in BX2. rewrite base_shift, rsz_shift in BX2.
      destruct (HbW R2 (nth_error_In _ _ HR2) E E'' Ha0) as [Eb2 Ez2]. unfold in_rg in Hin. rewrite Eb2, Ez2 in Hin.
      destruct (B5S R HR) as (_ & H2 & _). rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with two64 in Hin.
      pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as BB. change (bv_modulus 64) with two64 in BB.
      rewrite Z.mod_small in Hin by lia. lia.
  + (* [comment removed for export] *)
    apply (rgs_disj_same_shape E'' (List.map (rshift n) (s_rgs L) ++ s_rgs S)); [|exact B6].
    rewrite !map_app, !map_map. f_equal. pose proof (empty_at_shape W (s_rgs L) 0) as Hs. unfold shape in Hs.
    apply (f_equal (List.map (fun p : lin * lin => (lshift n (fst p), lshift n (snd p))))) in Hs. rewrite !map_map in Hs. exact Hs.
  + exact B7.
  + rewrite Hfcsr. exact B8.
Qed.

#[using="Hwx"] Theorem den_hand : forall n L S E M ms model T q K W,
  DEN segs LIMIT model0 mem0 E (mrg (sst_shift n L) S) M ms model ->
  state_wf L = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  (exists msr', isteps segs (restrict (Hof E M model) ms) msr' /\ ms_pc_val msr' = Z_to_bv 64 q /\ ms_svc_pending msr' = None /\
     ms_resv msr' = None /\ ms_fcsr msr' = ms_fcsr ms /\
     (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs ms) r) /\
     (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg (vshift n E) R x) ->
        ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) /\
     (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz (vshift n E) R ->
        rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (vshift n E) (rg_base R)) + j)) <> None /\
        (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (vshift n E) (rg_base R)) + j)) <> None))) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (mrg (sst_shift n (hand_post L q K W)) S) M ms' model' ->
     agree (n + s_next L) E E' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros n L S E M ms model T q K W Hd HwL HnRO (msr' & Hst & Hpc & Hsvc & Hrsv & Hfcsr & Hkeep & Hmem & Hrw) Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  assert (Ha : agree (n + s_next L) E (hval n (s_next L) E (ms_regs msr'))) by (intros x Hx; unfold hval; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E (mrg (sst_shift n L) S) M ms model T (mrg (sst_shift n (hand_post L q K W)) S) msr'
           (hval n (s_next L) E (ms_regs msr')) Hd Hst).
  - assert (HbS : bases_wf (n + s_next L) (s_rgs S) = true).
    { pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hb. cbn [mrg sst_shift s_next s_rgs] in Hb. unfold bases_wf in *.
      rewrite forallb_app in Hb. apply andb_prop in Hb as [_ Hb]. exact Hb. }
    apply (hand_sden n L S E _ msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep); [|exact Hrw].
    intros x Hx _. exact (Hmem x Hx).
  - exact Ha.
  - cbn [mrg sst_shift hand_post s_next]. lia.
  - intros x Hx. apply Hmem. intros (i0 & R2 & Hi0 & HR2 & Hin). unfold outside in Hx. cbn [mrg s_rgs sst_shift] in Hx.
    apply Forall_app in Hx as [Hx _]. rewrite Forall_map, Forall_forall in Hx. specialize (Hx R2 (nth_error_In _ _ HR2)).
    unfold in_rg in Hin. unfold rsz in Hx, Hin. cbn [rshift rg_base rg_size] in Hx. rewrite !lden_shift in Hx. lia.
  - cbn [mrg s_rgs sst_shift hand_post]. unfold shape. rewrite !map_app, !map_map. f_equal.
    pose proof (empty_at_shape W (s_rgs L) 0) as Hs. unfold shape in Hs.
    apply (f_equal (List.map (fun p : lin * lin => (lshift n (fst p), lshift n (snd p))))) in Hs. rewrite !map_map in Hs. exact Hs.
  - intros E2 ms2 model2 HD2 Ha2. exact (Hk E2 ms2 model2 HD2 Ha2).
Qed.
End Hand.

(* [comment removed for export] *)
Section HandW.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_hand_w : forall mem0 n L S E M ms model T q K W (QM : (word -> option byte) -> Prop),
  DEN segs LIMIT model0 mem0 E (mrg (sst_shift n L) S) M ms model ->
  state_wf L = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  (exists msr', isteps segs (restrict (Hof E M model) ms) msr' /\ ms_pc_val msr' = Z_to_bv 64 q /\ ms_svc_pending msr' = None /\
     ms_resv msr' = None /\ ms_fcsr msr' = ms_fcsr ms /\
     (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs ms) r) /\
     (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg (vshift n E) R x) ->
        (exists R, In R (s_rgs (mrg (sst_shift n L) S)) /\ in_rg E R x) ->
        ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) /\
     (forall w, 0 <= w < two64 -> outside E (s_rgs (mrg (sst_shift n L) S)) (Z_to_bv 64 w) -> ~ own_pt E M w ->
        ms_mem msr' (Z_to_bv 64 w) = ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w)) /\
     (forall w, frz_pt E M w -> ms_mem msr' (Z_to_bv 64 w) = ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w)) /\
     (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz (vshift n E) R ->
        rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (vshift n E) (rg_base R)) + j)) <> None /\
        (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (vshift n E) (rg_base R)) + j)) <> None)) /\
     QM (ms_mem msr')) ->
  (forall E' ms' model', DEN segs LIMIT model0 (ms_mem ms') E' (mrg (sst_shift n (hand_post L q K W)) S) M ms' model' ->
     agree (n + s_next L) E E' -> (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     (exists mr, QM mr /\ forall x, Hof E M model x = false -> ms_mem ms' x = mr x) ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 n L S E M ms model T q K W QM Hd HwL HnRO (msr' & Hst & Hpc & Hsvc & Hrsv & Hfcsr & Hkeep & Hmem & Hown & Hfz & Hrw & HQ) Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  assert (Ha : agree (n + s_next L) E (hval n (s_next L) E (ms_regs msr'))) by (intros x Hx; unfold hval; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  assert (HbS : bases_wf (n + s_next L) (s_rgs S) = true).
  { pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hb. cbn [mrg sst_shift s_next s_rgs] in Hb. unfold bases_wf in *.
    rewrite forallb_app in Hb. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  apply (den_isteps_w segs cfg LIMIT model0 Hwx mem0 E (mrg (sst_shift n L) S) M ms model T (mrg (sst_shift n (hand_post L q K W)) S) msr'
           (hval n (s_next L) E (ms_regs msr')) Hd Hst).
  - exact (hand_sden segs n L S E _ msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep Hmem Hrw).
  - exact Ha.
  - cbn [mrg sst_shift hand_post s_next]. lia.
  - exact Hown.
  - exact Hfz.
  - cbn [mrg s_rgs sst_shift hand_post]. unfold shape. rewrite !map_app, !map_map. f_equal.
    pose proof (empty_at_shape W (s_rgs L) 0) as Hs. unfold shape in Hs.
    apply (f_equal (List.map (fun p : lin * lin => (lshift n (fst p), lshift n (snd p))))) in Hs. rewrite !map_map in Hs. exact Hs.
  - intros E2 ms2 model2 HD2 Ha2 Hf2 Hv2. exact (Hk E2 ms2 model2 HD2 Ha2 Hf2 (ex_intro _ (ms_mem msr') (conj HQ Hv2))).
Qed.
End HandW.
(* [comment removed for export] *)
