(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSound FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan FxFrame.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mrg (L S : sst) : sst := SST (s_pc L) (s_regs L) (s_rgs L ++ s_rgs S) (s_facts L ++ s_facts S) (s_next L) (s_resv L).

(* [comment removed for export] *)
Definition pvars (L : sst) : list positive := List.map Pos.of_nat (seq 1 (Pos.to_nat (s_next L) - 1)).
Lemma in_pvars : forall L x, (x < s_next L)%positive -> In x (pvars L).
Proof. intros L x H. unfold pvars. apply in_map_iff. exists (Pos.to_nat x). split; [apply Pos2Nat.id|]. apply in_seq. lia. Qed.

(* [comment removed for export] *)
Definition vmerge (n : positive) (E E1 : valu) : valu := fun x => if Pos.ltb n x then E1 (x - n)%positive else E x.
Lemma vshift_vmerge : forall n E E1, forall y, vshift n (vmerge n E E1) y = E1 y.
Proof.
  intros n E E1 y. unfold vshift, vmerge. rewrite (proj2 (Pos.ltb_lt n (n + y))) by lia. f_equal. lia.
Qed.
Lemma vmerge_low : forall n E E1 x, (x <= n)%positive -> vmerge n E E1 x = E x.
Proof. intros n E E1 x H. unfold vmerge. rewrite (proj2 (Pos.ltb_ge n x)) by lia. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ok_mem_eq' : forall E m m' R, rg_ok segs E m R ->
  (forall i, 0 <= i < rsz E R -> m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R (Hs & Hw & Hb & Hc) Heq. split; [exact Hs|]. split; [exact Hw|]. split.
  - intros i Hi. specialize (Hb i Hi). specialize (Heq i Hi). unfold rd1, wview in *. rewrite Heq. exact Hb.
  - intros p v Hp. destruct (Hc p v Hp) as [Hp1 Hp2]. split; [exact Hp1|].
    assert (Hi : 0 <= Zpos p - 1 < rsz E R) by lia. specialize (Heq _ Hi). unfold rd1 in *. rewrite Heq. exact Hp2.
Qed.

#[using="Type"] Lemma rgs_disj_app_iff : forall E l1 l2, rgs_disj E (l1 ++ l2) <-> rgs_disj E l1 /\ rgs_disj E l2 /\ Forall (fun R => Forall (rg_disj E R) l2) l1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E l1 l2. induction l1 as [|R l1 IH]; cbn [app rgs_disj].
  - split; [intros H; split; [exact I | split; [exact H | constructor]] | tauto].
  - rewrite IH, Forall_app. split.
    + intros ((H1 & H2) & H3 & H4 & H5). split; [split; assumption|]. split; [exact H4|]. constructor; assumption.
    + intros ((H1 & H3) & H4 & H5). inversion H5 as [|? ? H6 H7]; subst. split; [split; assumption|]. split; [exact H3|]. split; assumption.
Qed.

#[using="Type"] Lemma rg_disj_sym : forall E R1 R2, rg_disj E R1 R2 -> rg_disj E R2 R1.
Proof. LiaFast.lf_pins LiaFast.u0. intros E R1 R2 H. unfold rg_disj in *. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma outside_of_disj : forall E rgs R, Forall (fun R' => rg_disj E R' R) rgs -> 0 <= rsz E R ->
  forall i, 0 <= i < rsz E R -> bv_unsigned (lden E (rg_base R)) + i < two64 ->
  outside E rgs (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs R HF Hz i Hi Hw. unfold outside. rewrite Forall_forall in *. intros R' HR'. specialize (HF R' HR').
  unfold rg_disj in HF. cbv zeta in HF. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as B. change (bv_modulus 64) with two64 in B.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem mrg_check : forall t img depth p L finals n S E ms,
  tbl_ok segs t -> img_ok segs img -> check t img (pvars L) depth p L = Some finals ->
  state_wf L = true -> (s_next S <= n)%positive ->
  sden segs E (mrg (sst_shift n L) S) ms ->
  exists L' ms' E', In L' finals /\ isteps segs ms ms' /\ sden segs E' (mrg (sst_shift n L') S) ms' /\
    agree (n + s_next L) E E' /\
    (forall x, outside E (s_rgs (mrg (sst_shift n L) S)) x -> ms_mem ms' x = ms_mem ms x) /\
    shape (s_rgs (mrg (sst_shift n L') S)) = shape (s_rgs (mrg (sst_shift n L) S)) /\
    (s_next L <= s_next L')%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p L finals n S E ms Ht Himg Hck HwL HnS Hd.
  pose proof (Hd E (agree_refl _ _)) as Hd0.
  (* [comment removed for export] *)
  assert (HdL : sden segs (vshift n E) L ms).
  { apply (sden_shift_fwd segs n E L ms HwL). destruct Hd0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    cbn [mrg s_pc s_regs s_rgs s_facts s_resv] in *. apply Forall_app in A5 as [A5 _]. apply Forall_app in A7 as [A7 _].
    apply rgs_disj_app_iff in A6 as (A6 & _ & _).
    unfold sden0; cbn [sst_shift s_pc s_regs s_rgs s_facts s_resv]. tauto. }
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
  destruct (check_frame segs t img (pvars L) depth p L finals Ht Himg Hck (vshift n E) ms HdL Hbw Hbi)
    as (L' & ms' & E1 & HL' & Hst & Hd1 & Hins & Hfr & Hsh & Hn).
  assert (HaL : agree (s_next L) E1 (vshift n E)) by (intros y Hy; apply Hins; apply in_pvars; exact Hy).
  set (E' := vmerge n E E1).
  assert (Ha : agree (n + s_next L) E E').
  { intros x Hx. unfold E'. destruct (Pos.ltb n x) eqn:Hlt.
    - apply Pos.ltb_lt in Hlt. unfold vmerge. rewrite (proj2 (Pos.ltb_lt n x) Hlt). rewrite (HaL (x - n)%positive) by lia.
      unfold vshift. f_equal. lia.
    - apply Pos.ltb_ge in Hlt. rewrite vmerge_low by exact Hlt. reflexivity. }
  (* [comment removed for export] *)
  assert (Hfr' : forall x, outside E (s_rgs (mrg (sst_shift n L) S)) x -> ms_mem ms' x = ms_mem ms x).
  { intros x Hx. apply Hfr. unfold outside in *. cbn [mrg s_rgs sst_shift] in Hx. apply Forall_app in Hx as [Hx _].
    rewrite Forall_map in Hx. eapply Forall_impl; [|exact Hx]. intros R HR. unfold rsz in *. cbn [rshift rg_base rg_size] in HR.
    rewrite !lden_shift in HR. exact HR. }
  exists L', ms', E'. split; [exact HL'|]. split; [exact Hst|]. split; [|split; [exact Ha|split; [exact Hfr'|split; [|exact Hn]]]].
  2: { cbn [mrg s_rgs sst_shift]. unfold shape. rewrite !map_app, !map_map. f_equal. unfold shape in Hsh.
       apply (f_equal (List.map (fun p : lin * lin => (lshift n (fst p), lshift n (snd p))))) in Hsh. rewrite !map_map in Hsh. exact Hsh. }
  (* [comment removed for export] *)
  intros E'' Ha''.
  assert (Ha0 : agree (n + s_next L) E E'').
  { intros x Hx. rewrite (Ha x Hx). apply Ha''. cbn [mrg sst_shift s_next]. lia. }
  pose proof (Hd E'' Ha0) as HdE.
  destruct HdE as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). cbn [mrg s_pc s_regs s_rgs s_facts s_resv sst_shift] in B5, B6, B7.
  apply Forall_app in B5 as [B5L B5S]. apply Forall_app in B7 as [_ B7S]. apply rgs_disj_app_iff in B6 as (_ & B6S & B6X).
  assert (HaS : agree (s_next L') E1 (vshift n E'')).
  { intros y Hy. rewrite <- (vshift_vmerge n E E1 y). unfold vshift. apply Ha''. cbn [mrg sst_shift s_next]. lia. }
  pose proof (sden_shift_bwd segs n E'' E1 L' ms' Hd1 HaS) as HdL'.
  destruct HdL' as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). cbn [sst_shift s_pc s_regs s_rgs s_facts s_resv] in C1, C3, C4, C5, C6, C7.
  (* [comment removed for export] *)
  assert (HbL : forall R', In R' (s_rgs L') -> exists R, In R (s_rgs L) /\
            bv_unsigned (lden E'' (rg_base (rshift n R'))) = bv_unsigned (lden E'' (rg_base (rshift n R))) /\
            rsz E'' (rshift n R') = rsz E'' (rshift n R)).
  { intros R' HR'. unfold shape in Hsh.
    destruct (In_nth_error _ _ HR') as [k Hk].
    assert (Hk' : nth_error (List.map (fun R : region => (rg_base R, rg_size R)) (s_rgs L')) k = Some (rg_base R', rg_size R'))
      by (rewrite nth_error_map, Hk; reflexivity).
    rewrite Hsh, nth_error_map in Hk'. destruct (nth_error (s_rgs L) k) as [R|] eqn:HkL; [|discriminate].
    cbn [option_map] in Hk'. injection Hk' as Eb Ez. exists R. split; [exact (nth_error_In _ _ HkL)|].
    rewrite !base_shift, !rsz_shift. unfold rsz. rewrite Eb, Ez. split; reflexivity. }
  unfold sden0. cbn [mrg sst_shift s_pc s_regs s_rgs s_facts s_resv].
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
  split; [|split; [|split; [|exact C8]]].
  - apply Forall_app. split; [exact C5|]. rewrite Forall_forall in B5S |- *. intros R HR.
    apply (rg_ok_mem_eq' E'' (ms_mem ms)); [exact (B5S R HR)|]. intros i Hi.
    destruct (B5S R HR) as (Hz & Hw & _).
    apply Hfr. apply (proj1 (outside_agree (s_next L) (vshift n E'') (vshift n E) (s_rgs L) _ Hbw
                                (fun y Hy => eq_sym (Ha0 (n + y)%positive ltac:(lia))))).
    unfold outside. rewrite Forall_forall. intros R0 HR0. rewrite Forall_forall in B6X.
    pose proof (B6X _ (in_map _ _ _ HR0)) as HX0. rewrite Forall_forall in HX0. pose proof (HX0 R HR) as HX.
    unfold rg_disj in HX. cbv zeta in HX. rewrite base_shift, rsz_shift in HX.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
    pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as BB. change (bv_modulus 64) with two64 in BB.
    rewrite Z.mod_small by lia. lia.
  - apply rgs_disj_app_iff. split; [exact C6|]. split; [exact B6S|].
    rewrite Forall_map. rewrite Forall_forall. intros R' HR'. destruct (HbL R' HR') as (R & HR & Eb & Ez).
    rewrite Forall_forall in B6X. pose proof (B6X _ (in_map _ _ _ HR)) as HX. rewrite Forall_forall in HX |- *.
    intros R2 HR2. specialize (HX R2 HR2). unfold rg_disj in HX |- *. cbv zeta in HX |- *. rewrite Eb, Ez. exact HX.
  - apply Forall_app. split; [exact C7 | exact B7S].
Qed.
End WithSegs.
