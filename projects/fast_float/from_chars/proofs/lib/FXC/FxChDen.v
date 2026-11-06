(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.

Module FxAcct.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Acct.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Type"] Lemma munrestrict_twice : forall full m1 m2, munrestrict H (munrestrict H full m1) m2 = munrestrict H full m2.
Proof. LiaFast.lf_pins LiaFast.u0. intros full m1 m2. apply functional_extensionality. intros a. unfold munrestrict. destruct (H a); reflexivity. Qed.

#[using="Type"] Lemma unrestrict_twice : forall full ms1 ms2, unrestrict H (ms_mem (unrestrict H full ms1)) ms2 = unrestrict H full ms2.
Proof. LiaFast.lf_pins LiaFast.u0. intros full ms1 ms2. unfold unrestrict. cbn [ms_mem]. rewrite munrestrict_twice. reflexivity. Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Theorem rzc_fx_isteps : forall A msr msr' ms model T,
  restrict H ms = msr ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  FxStep.isteps segs msr msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' -> hclean H msr' ->
      realizes_cfg segs cfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (HH Hwx : LiaFast.U) => LiaFast.u0).
  intros A msr msr' ms model T Hr Hcov Hwf Hinv Hh Hst. revert ms model Hr Hcov Hinv Hh.
  induction Hst as [msr | msr msr1 msr'' Hsvc Hs Hst IH]; intros ms model Hr Hcov Hinv Hh Hk.
  - subst msr. pose proof (Hk model Hinv (same_but_materialized_refl model) (restrict_hclean H ms)) as Hc.
    rewrite unrestrict_restrict in Hc. exact Hc.
  - subst msr. assert (Hsvc' : ms_svc_pending ms = None) by exact Hsvc.
    destruct (node_instr_restricted segs H HH Hwx A ms msr1 model Hcov Hwf Hinv Hh Hsvc' Hs)
      as (model1 & Hinv1 & Hsb1 & Hcl1 & Hacc & _).
    eapply rzc_step_acct; [exact Hh | exact Hsvc' | exact Hacc |].
    destruct (same_but_materialized_frame model model1 Hsb1) as (_ & _ & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhl & _).
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + apply restrict_unrestrict_clean. exact Hcl1.
    + rewrite Hlz. exact Hcov.
    + exact Hinv1.
    + rewrite Hhl. exact Hh.
    + intros model' Hinv' Hsb' Hcl'. rewrite unrestrict_twice.
      apply Hk; [exact Hinv' | eapply same_but_materialized_trans; [exact Hsb1 | exact Hsb'] | exact Hcl'].
Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Corollary rzc_fx_leaves : forall A ms model T (S : sst) E (leaves : list sst),
  (forall E0 msr, sden segs E0 S msr -> exists L msr' E', In L leaves /\ FxStep.isteps segs msr msr' /\ sden segs E' L msr') ->
  sden segs E S (restrict H ms) ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  (forall L E' msr' model', In L leaves -> sden segs E' L msr' -> MInv A model' -> same_but_materialized model model' ->
      hclean H msr' -> realizes_cfg segs cfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (HH Hwx : LiaFast.U) => LiaFast.u0).
  intros A ms model T S E leaves Hcert Hden Hcov Hwf Hinv Hh Hk.
  destruct (Hcert E (restrict H ms) Hden) as (L & msr' & E' & HL & Hst & HdL).
  apply (rzc_fx_isteps A (restrict H ms) msr' ms model T eq_refl Hcov Hwf Hinv Hh Hst).
  intros model' Hinv' Hsb' Hcl'. exact (Hk L E' msr' model' HL HdL Hinv' Hsb' Hcl').
Qed.
End Acct.
End FxAcct.

From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking.

Module AcMrg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSound FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan FxFrame.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.AcShift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

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
(* [comment removed for export] *)
End AcMrg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rom_tac :=
  repeat match goal with x := _ |- ms_rom _ = _ => subst x end;
  cbn [ms_rom advance_past_svc apply_effect svc_set unrestrict restrict] in *;
  first [assumption | reflexivity].

(* [comment removed for export] *)
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity).
Notation "a &&& b" := (if a then b else false) (at level 40, left associativity).
(* [comment removed for export] *)
Fixpoint existsb_lz {A} (f : A -> bool) (l : list A) : bool := match l with nil => false | cons x r => if f x then true else existsb_lz f r end.
Fixpoint forallb_lz {A} (f : A -> bool) (l : list A) : bool := match l with nil => true | cons x r => if f x then forallb_lz f r else false end.
Lemma existsb_lz_eq : forall A (f : A -> bool) l, existsb_lz f l = existsb f l.
Proof. induction l as [|x r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma forallb_lz_eq : forall A (f : A -> bool) l, forallb_lz f l = forallb f l.
Proof. induction l as [|x r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.

Inductive gkind : Type := GE | GL | GN.   (* [comment removed for export] *)
Definition gkind_eqb (a b : gkind) : bool := match a, b with GE, GE | GL, GL | GN, GN => true | _, _ => false end.

Record smodel : Type := SM {
  sm_maps  : list (lin * lin * gkind); (* [comment removed for export] *)
  sm_allow : list (lin * Z);           (* [comment removed for export] *)
  sm_zr    : list (Z * Z);             (* [comment removed for export] *)
  sm_tid   : option lin;
  sm_brk   : lin;
  sm_sbrk  : lin;
  sm_sp    : lin;                      (* [comment removed for export] *)
  sm_frz   : list (lin * lin) ;        (* [comment removed for export] *)
  sm_own   : list (lin * lin)          (* [comment removed for export] *)
}.

Definition uE (E : valu) (l : lin) : Z := bv_unsigned (lden E l).
Definition gden (E : valu) (g : lin * lin * gkind) : word * word := (lden E (fst (fst g)), lden E (snd (fst g))).
(* [comment removed for export] *)
Definition gsz (E : valu) (g : lin * lin * gkind) : Z := uE E (snd (fst g)).
Definition gsz_c (g : lin * lin * gkind) : option Z := is_const (snd (fst g)).
Definition allow1 (E : valu) (p : lin * Z) : Z * Z :=
  ((uE E (fst p) / 4096) * 4096, ((uE E (fst p) + snd p + 4095) / 4096) * 4096).
Definition allowA (E : valu) (M : smodel) : list (Z * Z) := List.map (allow1 E) (sm_allow M).
Definition Hof (E : valu) (M : smodel) (model : Model) : word -> bool := mkH (m_vm_lazy model) (allowA E M).

(* [comment removed for export] *)
Definition sm_wf (n : positive) (M : smodel) : bool :=
  (forallb (fun g => lwf n (fst (fst g)) && lwf n (snd (fst g))) (sm_maps M) && forallb (fun g => lwf n (fst g)) (sm_allow M) &&
   match sm_tid M with Some l => lwf n l | None => true end && lwf n (sm_brk M) && lwf n (sm_sbrk M) && lwf n (sm_sp M) &&
   forallb (fun p => lwf n (fst p) && lwf n (snd p)) (sm_frz M) && forallb (fun p => lwf n (fst p) && lwf n (snd p)) (sm_own M))%bool.

(* [comment removed for export] *)
Definition SH_LO : Z := 0x7fff7000.        (* [comment removed for export] *)
Definition SH_HI : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition SH_OFF : Z := 0x7fff8000.       (* [comment removed for export] *)
Definition in_shadow (w : Z) : bool := (SH_LO <=? w) && (w <? SH_HI).

(* [comment removed for export] *)
Definition atop_pg (h : VmMaps) : Z := 4096 * (alloc_top h / 4096).
Lemma atop_pg_le : forall h, atop_pg h <= alloc_top h.
Proof. intros h. unfold atop_pg. apply Z.mul_div_le. lia. Qed.
Lemma atop_pg_eq : forall h h', alloc_top h' = alloc_top h -> atop_pg h' = atop_pg h.
Proof. intros h h' H. unfold atop_pg. rewrite H. reflexivity. Qed.
Lemma grant_le_atop_pg : forall h (a n : Z), a mod 4096 = 0 -> n mod 4096 = 0 -> a + n <= alloc_top h -> a + n <= atop_pg h.
Proof.
  intros h a n Ha Hn H. unfold atop_pg.
  assert (Han : (a + n) mod 4096 = 0) by (rewrite Z.add_mod by lia; rewrite Ha, Hn; reflexivity).
  pose proof (Z.div_mod (a + n) 4096 ltac:(lia)) as E1. rewrite Han, Z.add_0_r in E1.
  assert (Hd : (a + n) / 4096 <= alloc_top h / 4096) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Definition app_pt (model : Model) (w : Z) : Prop :=
  (covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) w = true \/ atop_pg (m_vmmaps model) <= w)
  /\ in_shadow w = false /\ 0 <= w < 0x800000000000.

(* [comment removed for export] *)
Definition rl_ok (E : valu) (model : Model) (R : region) : Prop :=
  let A := uE E (rg_base R) in
  0 < rsz E R /\
  ((forall w, A <= w < A + rsz E R -> app_pt model w)
  \/ (SH_OFF <= A /\ (forall x, 8 * (A - SH_OFF) <= x < 8 * (A - SH_OFF + rsz E R) -> app_pt model x)
      /\ (forall w, A <= w < A + rsz E R -> in_shadow w = true /\ covered (vm_maps (m_vmmaps model)) w = true))).

Definition in_zr (zr : list (Z * Z)) (w : Z) : bool := existsb (fun p => (fst p <=? w) && (w <? snd p)) zr.

(* [comment removed for export] *)
Definition iv_disj (p q : word * word) : Prop := B p + S p <= B q \/ B q + S q <= B p.
Fixpoint pdisj (l : list (word * word)) : Prop :=
  match l with [] => True | p :: r => Forall (iv_disj p) r /\ pdisj r end.

(* [comment removed for export] *)
Definition kind_ok (E : valu) (model : Model) (g : lin * lin * gkind) : Prop :=
  (snd g <> GE -> forall x, in_iv (gden E g) x = true -> covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true) /\
  (snd g = GN -> In (gden E g) (vm_noaccess (m_vmmaps model))).

(* [comment removed for export] *)
Definition gshape_ok (E : valu) (g : lin * lin * gkind) : Prop :=
  0 < gsz E g /\ gsz E g mod 4096 = 0 /\ uE E (fst (fst g)) mod 4096 = 0 /\ uE E (fst (fst g)) + gsz E g <= 0x800000000000 /\
  0 < uE E (fst (fst g)).

(* [comment removed for export] *)
Definition own_pt (E : valu) (M : smodel) (w : Z) : Prop :=
  exists p, In p (sm_own M) /\ uE E (fst p) <= w < uE E (fst p) + uE E (snd p).
Lemma own_pt_nil : forall E M w, sm_own M = [] -> ~ own_pt E M w.
Proof. intros E M w H (p & Hp & _). rewrite H in Hp. destruct Hp. Qed.
Lemma own_pt_same : forall E M M' w, sm_own M' = sm_own M -> own_pt E M' w -> own_pt E M w.
Proof. intros E M M' w H (p & Hp & Hw). rewrite H in Hp. exists p. split; [exact Hp | exact Hw]. Qed.

(* [comment removed for export] *)
Definition MARKB : Z := 4096.
Definition is_mark (g : lin * lin * gkind) : bool :=
  match is_const (fst (fst g)) with
  | Some b => Z.eqb b MARKB &&& match is_const (snd (fst g)) with None => true | Some _ => false end
  | None => false
  end.   (* [comment removed for export] *)
Lemma is_mark_csize : forall b z k, is_mark (b, lconst z, k) = false.
Proof. intros b z k. unfold is_mark. cbn [fst snd]. destruct (is_const b) as [c|]; [|reflexivity]. destruct (Z.eqb c MARKB); reflexivity. Qed.
Definition nomark (gs : list (lin * lin * gkind)) : bool := forallb (fun g => negb (is_mark g)) gs.
Fixpoint lden_maps (E : valu) (BL : list (word * word)) (gs : list (lin * lin * gkind)) : list (word * word) :=
  match gs with
  | [] => []
  | g :: r => if is_mark g then BL ++ lden_maps E BL r else gden E g :: lden_maps E BL r
  end.
Definition blob_of (model0 : Model) : list (word * word) := vm_maps (m_vmmaps model0).
Definition SHz (x : Z) : Z := SH_OFF + x / 8.
Definition blob_sh (BL : list (word * word)) (w : Z) : Prop :=
  exists p, In p BL /\ SHz (bv_unsigned (fst p)) <= w < SHz (bv_unsigned (fst p) + bv_unsigned (snd p)).
Definition blobA1 (p : word * word) : Z * Z :=
  (SHz (bv_unsigned (fst p)) / 4096 * 4096, (SHz (bv_unsigned (fst p) + bv_unsigned (snd p)) + 4095) / 4096 * 4096).
Definition blobA (BL : list (word * word)) : list (Z * Z) := List.map blobA1 BL.
Definition blob_ent_ok (model : Model) (p : word * word) : Prop :=
  MARKB <= bv_unsigned (fst p) /\ bv_unsigned (fst p) mod 4096 = 0 /\ 0 < bv_unsigned (snd p) /\
  bv_unsigned (snd p) mod 4096 = 0 /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= alloc_top (m_vmmaps model).
Definition blob_ok (E : valu) (M : smodel) (model : Model) (BL : list (word * word)) : Prop :=
  Forall (blob_ent_ok model) BL /\ (nomark (sm_maps M) = true -> BL = []) /\
  (forall g, In g (sm_maps M) -> is_mark g = true -> snd g = GE /\ 4 * ledger_size BL <= gsz E g).   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma lden_maps_nomark : forall E BL gs, nomark gs = true -> lden_maps E BL gs = List.map (gden E) gs.
Proof.
  intros E BL gs. induction gs as [|g r IH]; intros H; [reflexivity|]. cbn [nomark forallb] in H. apply andb_prop in H as [H1 H2].
  cbn [lden_maps List.map]. apply negb_true_iff in H1. rewrite H1. f_equal. exact (IH H2).
Qed.
Lemma lden_maps_in : forall E BL gs g, In g gs -> is_mark g = false -> In (gden E g) (lden_maps E BL gs).
Proof.
  intros E BL gs g. induction gs as [|g0 r IH]; intros Hin Hm; [destruct Hin|]. cbn [lden_maps].
  destruct Hin as [->|Hin].
  - rewrite Hm. left. reflexivity.
  - destruct (is_mark g0); [apply in_or_app; right | right]; exact (IH Hin Hm).
Qed.
Lemma lden_maps_inv : forall E BL gs q, In q (lden_maps E BL gs) ->
  (exists g, In g gs /\ is_mark g = false /\ q = gden E g) \/ (In q BL /\ nomark gs = false).
Proof.
  intros E BL gs q. induction gs as [|g0 r IH]; intros Hin; [destruct Hin|]. cbn [lden_maps] in Hin.
  destruct (is_mark g0) eqn:Hm.
  - apply in_app_or in Hin as [Hin|Hin].
    + right. split; [exact Hin|]. cbn [nomark forallb]. rewrite Hm. reflexivity.
    + destruct (IH Hin) as [(g & Hg & Hgm & ->) | (Hq & Hn)].
      * left. exists g. split; [right; exact Hg | split; [exact Hgm | reflexivity]].
      * right. split; [exact Hq|]. cbn [nomark forallb]. rewrite Hm. reflexivity.
  - destruct Hin as [<-|Hin].
    + left. exists g0. split; [left; reflexivity | split; [exact Hm | reflexivity]].
    + destruct (IH Hin) as [(g & Hg & Hgm & ->) | (Hq & Hn)].
      * left. exists g. split; [right; exact Hg | split; [exact Hgm | reflexivity]].
      * right. split; [exact Hq|]. cbn [nomark forallb]. rewrite Hm. cbn [negb andb]. exact Hn.
Qed.
Lemma lden_maps_blob_in : forall E BL gs q, nomark gs = false -> In q BL -> In q (lden_maps E BL gs).
Proof.
  intros E BL gs q. induction gs as [|g r IH]; intros Hn Hq; [discriminate|]. cbn [nomark forallb] in Hn. cbn [lden_maps].
  destruct (is_mark g); [apply in_or_app; left; exact Hq|]. cbn [negb andb] in Hn. right. exact (IH Hn Hq).
Qed.
(* [comment removed for export] *)
Lemma blob_in_maps : forall E M model BL q, blob_ok E M model BL -> In q BL -> In q (lden_maps E BL (sm_maps M)).
Proof.
  intros E M model BL q (_ & Hnil & _) Hq. apply lden_maps_blob_in; [|exact Hq].
  destruct (nomark (sm_maps M)) eqn:Hn; [|reflexivity]. rewrite (Hnil eq_refl) in Hq. destruct Hq.
Qed.
Lemma lden_maps_ext : forall E E' BL gs, (forall g, In g gs -> gden E' g = gden E g) -> lden_maps E' BL gs = lden_maps E BL gs.
Proof.
  intros E E' BL gs. induction gs as [|g r IH]; intros H; [reflexivity|]. cbn [lden_maps].
  rewrite (IH (fun g' Hg' => H g' (or_intror Hg'))). destruct (is_mark g); [reflexivity|]. rewrite (H g (or_introl eq_refl)). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma blob_nil_of_nomark : forall E M model BL, blob_ok E M model BL -> nomark (sm_maps M) = true -> BL = [].
Proof. intros E M model BL (_ & H & _) Hn. exact (H Hn). Qed.
Lemma nomark_in : forall gs g, nomark gs = true -> In g gs -> is_mark g = false.
Proof. intros gs g H Hin. unfold nomark in H. rewrite forallb_forall in H. apply negb_true_iff. exact (H g Hin). Qed.
(* [comment removed for export] *)
Lemma blob_len_le : forall model BL, Forall (blob_ent_ok model) BL -> 4096 * Z.of_nat (length BL) <= ledger_size BL.
Proof.
  intros model BL H. induction H as [|[b n] r Hp Hr IH]; [cbn; lia|]. cbn [length ledger_size]. destruct Hp as (_ & _ & Hpos & Hal & _). cbn [snd] in *.
  assert (4096 <= bv_unsigned n) by (pose proof (Z.div_mod (bv_unsigned n) 4096 ltac:(lia)); pose proof (Z.mod_pos_bound (bv_unsigned n) 4096 ltac:(lia)); nia). lia.
Qed.
Lemma blob_sh_nil : forall w, ~ blob_sh [] w.
Proof. intros w (p & Hp & _). destruct Hp. Qed.
Lemma A_wf_blobA : forall BL, A_wf (blobA BL).
Proof.
  intros BL. unfold A_wf, blobA. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (p & <- & _). unfold blobA1. cbn [fst snd].
  pose proof (bv_unsigned_in_range _ (fst p)) as U1. pose proof (bv_unsigned_in_range _ (snd p)) as U2.
  set (a := SHz (bv_unsigned (fst p))). set (b := SHz (bv_unsigned (fst p) + bv_unsigned (snd p))).
  assert (Hab : a <= b) by (unfold a, b, SHz; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  unfold page_size. split; [|split].
  - pose proof (Z.mul_div_le a 4096 ltac:(lia)). pose proof (Z.mul_div_le (b + 4095) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (b + 4095) 4096 ltac:(lia)). pose proof (Z.div_mod (b + 4095) 4096 ltac:(lia)). lia.
  - rewrite Z.mod_mul by lia. reflexivity.
  - rewrite Z.mod_mul by lia. reflexivity.
Qed.
Lemma A_wf_app : forall A1 A2, A_wf A1 -> A_wf A2 -> A_wf (A1 ++ A2).
Proof. intros A1 A2 H1 H2. unfold A_wf in *. apply Forall_app. split; assumption. Qed.
Lemma page_allowedb_app_l : forall A1 A2 p, page_allowedb A1 p = true -> page_allowedb (A1 ++ A2) p = true.
Proof. intros A1 A2 p H. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
Lemma lazy_cover_mkH_app : forall L A A' lazy, incl lazy L -> lazy_cover (mkH L A) lazy (A ++ A').
Proof. intros L A A' lazy Hi w Hl Hw. apply page_allowedb_app_l. exact (lazy_cover_mkH L A lazy Hi w Hl Hw). Qed.

Section Den.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
Definition AM (E : valu) (M : smodel) : list (Z * Z) := allowA E M ++ blobA (blob_of model0).

(* [comment removed for export] *)
Definition own_ok (E : valu) (S : sst) (M : smodel) (ms : machine_state) (model : Model) : Prop :=
  forall p, In p (sm_own M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
    Hof E M model (Z_to_bv 64 w) = false /\
    (outside E (s_rgs S) (Z_to_bv 64 w) -> ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).

Record DEN (E : valu) (S : sst) (M : smodel) (ms : machine_state) (model : Model) : Prop := mkDEN {
  dn_sden   : sden segs E S (restrict (Hof E M model) ms);
  dn_wf     : sm_wf (s_next S) M = true;
  dn_bases  : bases_wf (s_next S) (s_rgs S) = true;
  dn_halt   : m_halted model = None;
  dn_awf    : A_wf (allowA E M);
  dn_anz    : Forall (fun p => 0 <= snd p) (sm_allow M);
  dn_minv   : MInv (AM E M) model;                        (* [comment removed for export] *)
  dn_hoff   : H_off_segments segs (Hof E M model);
  dn_res    : vm_reserved (m_vmmaps model) = segments_reserved segs;
  dn_lim    : vm_limit (m_vmmaps model) = LIMIT;
  dn_sp     : vm_init_sp (m_vmmaps model) = lden E (sm_sp M);
  dn_spok   : init_sp_ok (m_vmmaps model) /\ bv_unsigned (vm_init_sp (m_vmmaps model)) <= sp_window_hi;
  dn_brk    : vm_brk (m_vmmaps model) = lden E (sm_brk M);
  dn_sbrk   : vm_start_brk (m_vmmaps model) = lden E (sm_sbrk M);
  dn_tid    : m_tid model = option_map (lden E) (sm_tid M);
  dn_maps   : vm_maps (m_vmmaps model) = lden_maps E (blob_of model0) (sm_maps M);   (* [comment removed for export] *)
  dn_gsh    : Forall (gshape_ok E) (sm_maps M);
  dn_gtop   : Forall (fun g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) (sm_maps M);
  dn_ivwf   : ivs_wf (vm_noaccess (m_vmmaps model)) /\ ivs_wf (m_vm_lazy model);
  dn_pd     : pdisj (vm_maps (m_vmmaps model));
  dn_mres   : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_reserved (m_vmmaps model)) x = false;
  dn_kind   : Forall (kind_ok E model) (sm_maps M);
  dn_lzm    : forall x, covered (m_vm_lazy model) x = true -> covered (vm_maps (m_vmmaps model)) x = true;
  dn_zrsh   : forall w, in_zr (sm_zr M) w = true -> in_shadow w = true;
  dn_zrm    : forall w, in_zr (sm_zr M) w = true -> covered (vm_maps (m_vmmaps model)) w = true;
  dn_zr     : forall w, in_zr (sm_zr M) w = true -> outside E (s_rgs S) (Z_to_bv 64 w) -> ~ own_pt E M w ->
                ~ blob_sh (blob_of model0) w ->
                ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0);     (* [comment removed for export] *)
  dn_rl     : Forall (rl_ok E model) (s_rgs S);
  dn_other  : m_fd model = m_fd model0 /\ m_io model = m_io model0 /\ m_fsys model = m_fsys model0 /\
              m_lim model = m_lim model0 /\ m_time model = m_time model0;
  dn_proc   : m_proc model = match m_tid model with Some t => m_proc (with_tid t model0) | None => m_proc model0 end;
  dn_frz    : forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
                alloc_top (m_vmmaps model) <= w < 0x800000000000 /\ outside E (s_rgs S) (Z_to_bv 64 w) /\
                ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w);
  dn_rom    : ms_rom ms = seg_rom segs ;               (* [comment removed for export] *)
  dn_own    : own_ok E S M ms model;                   (* [comment removed for export] *)
  dn_blob   : blob_ok E M model (blob_of model0)       (* [comment removed for export] *)
}.

#[using="Type"] Lemma alloc_top_lo : forall h, init_sp_ok h -> 0x7fff7f800000 <= alloc_top h.
Proof. LiaFast.lf_pins LiaFast.u0. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, stack_max_size. lia. Qed.

#[using="Type"] Lemma covered_below_top : forall E St M ms model x, DEN E St M ms model -> covered (vm_maps (m_vmmaps model)) x = true ->
  x < alloc_top (m_vmmaps model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E St M ms model x Hd Hc.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  rewrite Hmaps in Hc. unfold covered in Hc. apply existsb_exists in Hc as (q & Hq & Hin).
  apply lden_maps_inv in Hq as [(g & Hg & _ & ->) | (Hq & _)].
  - rewrite Forall_forall in Hgtop, Hgsh. specialize (Hgtop g Hg). destruct (Hgsh g Hg) as (H1 & H2 & H3 & H4 & H5).
    unfold in_iv, in_rng, gden, B, S in Hin. cbn [fst snd] in Hin. apply andb_prop in Hin as [_ Hin]. apply Z.ltb_lt in Hin.
    unfold gsz, uE in *. lia.
  - destruct Hblob as [Hbe _]. rewrite Forall_forall in Hbe. destruct (Hbe q Hq) as (_ & _ & _ & _ & Ht).
    unfold in_iv, in_rng, B, S in Hin. apply andb_prop in Hin as [_ Hin]. apply Z.ltb_lt in Hin. lia.
Qed.

#[using="Type"] Lemma frz_keep : forall E E' S S' M M' ms ms' model model',
  sm_wf (s_next S) M = true -> agree (s_next S) E E' ->
  sm_frz M' = sm_frz M ->
  alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) ->
  (forall w, alloc_top (m_vmmaps model) <= w < 0x800000000000 -> outside E (s_rgs S) (Z_to_bv 64 w) -> outside E' (s_rgs S') (Z_to_bv 64 w)) ->
  (forall w, alloc_top (m_vmmaps model) <= w < 0x800000000000 -> outside E (s_rgs S) (Z_to_bv 64 w) -> ms_mem ms' (Z_to_bv 64 w) = ms_mem ms (Z_to_bv 64 w)) ->
  (forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
     alloc_top (m_vmmaps model) <= w < 0x800000000000 /\ outside E (s_rgs S) (Z_to_bv 64 w) /\ ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  (forall p, In p (sm_frz M') -> forall w, uE E' (fst p) <= w < uE E' (fst p) + uE E' (snd p) ->
     alloc_top (m_vmmaps model') <= w < 0x800000000000 /\ outside E' (s_rgs S') (Z_to_bv 64 w) /\ ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E E' S S' M M' ms ms' model model' Hwf Ha HM Hat Hout Hmem Hfrz p Hp w Hw. rewrite HM in Hp.
  unfold sm_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [_ Hwz]. rewrite forallb_forall in Hwz. specialize (Hwz p Hp).
  apply andb_prop in Hwz as [Hf1 Hf2].
  assert (Hw0 : uE E (fst p) <= w < uE E (fst p) + uE E (snd p)).
  { unfold uE in *. rewrite (lden_agree (s_next S) E E' _ Hf1 Ha), (lden_agree (s_next S) E E' _ Hf2 Ha). exact Hw. }
  destruct (Hfrz p Hp w Hw0) as (Htp & Ho & Hm). rewrite Hat. split; [exact Htp|]. split; [exact (Hout w Htp Ho)|].
  rewrite (Hmem w Htp Ho). exact Hm.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma own_keep : forall E E' S S' M M' ms ms' model model',
  sm_wf (s_next S) M = true -> agree (s_next S) E E' -> sm_own M' = sm_own M ->
  (forall w, outside E' (s_rgs S') (Z_to_bv 64 w) -> outside E (s_rgs S) (Z_to_bv 64 w)) ->
  (forall w, outside E (s_rgs S) (Z_to_bv 64 w) -> ms_mem ms' (Z_to_bv 64 w) = ms_mem ms (Z_to_bv 64 w)) ->
  (forall x, Hof E M model x = false -> Hof E' M' model' x = false) ->
  own_ok E S M ms model -> own_ok E' S' M' ms' model'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E E' S S' M M' ms ms' model model' Hwf Ha HM Hout Hmem Hvis Hown p Hp w Hw. rewrite HM in Hp.
  unfold sm_wf in Hwf. apply andb_prop in Hwf as [_ Hwz]. rewrite forallb_forall in Hwz. specialize (Hwz p Hp).
  apply andb_prop in Hwz as [Hf1 Hf2].
  assert (Hw0 : uE E (fst p) <= w < uE E (fst p) + uE E (snd p)).
  { unfold uE in *. rewrite (lden_agree (s_next S) E E' _ Hf1 Ha), (lden_agree (s_next S) E E' _ Hf2 Ha). exact Hw. }
  destruct (Hown p Hp w Hw0) as [Hv Hm]. split; [exact (Hvis _ Hv)|]. intros Ho'.
  pose proof (Hout w Ho') as Ho. rewrite (Hmem w Ho). exact (Hm Ho).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma own_keep2 : forall E E' S S' M M' ms ms' model model',
  sm_wf (s_next S) M = true -> agree (s_next S) E E' -> sm_own M' = sm_own M ->
  (forall w, own_pt E M w -> outside E' (s_rgs S') (Z_to_bv 64 w) ->
     outside E (s_rgs S) (Z_to_bv 64 w) /\ ms_mem ms' (Z_to_bv 64 w) = ms_mem ms (Z_to_bv 64 w)) ->
  (forall w, own_pt E M w -> Hof E M model (Z_to_bv 64 w) = false -> Hof E' M' model' (Z_to_bv 64 w) = false) ->
  own_ok E S M ms model -> own_ok E' S' M' ms' model'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E E' S S' M M' ms ms' model model' Hwf Ha HM Hout Hvis Hown p Hp w Hw. rewrite HM in Hp.
  unfold sm_wf in Hwf. apply andb_prop in Hwf as [_ Hwz]. rewrite forallb_forall in Hwz. specialize (Hwz p Hp).
  apply andb_prop in Hwz as [Hf1 Hf2].
  assert (Hw0 : uE E (fst p) <= w < uE E (fst p) + uE E (snd p)).
  { unfold uE in *. rewrite (lden_agree (s_next S) E E' _ Hf1 Ha), (lden_agree (s_next S) E E' _ Hf2 Ha). exact Hw. }
  assert (Hop : own_pt E M w) by (exists p; split; [exact Hp | exact Hw0]).
  destruct (Hown p Hp w Hw0) as [Hv Hm]. split; [exact (Hvis _ Hop Hv)|]. intros Ho'.
  destruct (Hout w Hop Ho') as [Ho Hme]. rewrite Hme. exact (Hm Ho).
Qed.
(* [comment removed for export] *)
Definition own_avoid (E : valu) (M : smodel) (lo hi : Z) : Prop :=
  forall w, own_pt E M w -> ~ (lo <= bv_unsigned (Z_to_bv 64 w) < hi).
#[using="Type"] Lemma own_avoid_nil : forall E M lo hi, sm_own M = [] -> own_avoid E M lo hi.
Proof. LiaFast.lf_pins LiaFast.u0. intros E M lo hi H w Hw. exfalso. exact (own_pt_nil E M w H Hw). Qed.
#[using="Type"] Lemma own_avoid_pt : forall E M lo hi y, own_avoid E M lo hi -> 0 <= y < 18446744073709551616 -> lo <= y < hi -> ~ own_pt E M y.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M lo hi y H Hy Hr Ho. apply (H y Ho). rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.mod_small by exact Hy. exact Hr.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma own_nil : forall E S M ms model, sm_own M = [] -> own_ok E S M ms model.
Proof. LiaFast.lf_pins LiaFast.u0. intros E S M ms model H p Hp. rewrite H in Hp. destruct Hp. Qed.
End Den.

Lemma lden_agree_wf : forall n E E' l, lwf n l = true -> agree n E E' -> lden E' l = lden E l.
Proof. intros n E E' l H Ha. symmetry. exact (lden_agree n E E' l H Ha). Qed.

Lemma sm_wf_mono : forall n n' M, (n <= n')%positive -> sm_wf n M = true -> sm_wf n' M = true.
Proof.
  intros n n' M Hn H. unfold sm_wf in *.
  apply andb_prop in H as [H Hown]. apply andb_prop in H as [H Hfz]. apply andb_prop in H as [H Hsp]. apply andb_prop in H as [H Hsb]. apply andb_prop in H as [H Hb].
  apply andb_prop in H as [H Ht]. apply andb_prop in H as [Hg Ha].
  repeat (apply andb_true_intro; split); try (eapply lwf_mono; eassumption).
  - rewrite forallb_forall in *. intros g Hg'. specialize (Hg g Hg'). apply andb_prop in Hg as [H1 H2].
    apply andb_true_intro; split; eapply lwf_mono; eassumption.
  - rewrite forallb_forall in *. intros g Hg'. eapply lwf_mono; [exact Hn | auto].
  - destruct (sm_tid M); [eapply lwf_mono; eassumption | reflexivity].
  - rewrite forallb_forall in Hfz |- *. intros p Hp. specialize (Hfz p Hp). apply andb_prop in Hfz as [H1 H2].
    apply andb_true_intro; split; eapply lwf_mono; eassumption.
  - rewrite forallb_forall in Hown |- *. intros p Hp. specialize (Hown p Hp). apply andb_prop in Hown as [H1 H2].
    apply andb_true_intro; split; eapply lwf_mono; eassumption.
Qed.

Lemma sm_wf_parts : forall n M, sm_wf n M = true ->
  Forall (fun g => lwf n (fst (fst g)) = true) (sm_maps M) /\ Forall (fun g => lwf n (fst g) = true) (sm_allow M) /\
  match sm_tid M with Some l => lwf n l = true | None => True end /\
  lwf n (sm_brk M) = true /\ lwf n (sm_sbrk M) = true /\ lwf n (sm_sp M) = true.
Proof.
  intros n M H. unfold sm_wf in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H Hsp]. apply andb_prop in H as [H Hsb]. apply andb_prop in H as [H Hb].
  apply andb_prop in H as [H Ht]. apply andb_prop in H as [Hg Ha].
  split; [apply Forall_forall; intros g Hin; rewrite forallb_forall in Hg; pose proof (Hg g Hin) as X; apply andb_prop in X; exact (proj1 X)|].
  split; [apply Forall_forall; intros g Hin; rewrite forallb_forall in Ha; exact (Ha g Hin)|].
  split; [destruct (sm_tid M); [exact Ht | exact I]|]. auto.
Qed.
Lemma sm_wf_sizes : forall n M, sm_wf n M = true -> Forall (fun g => lwf n (snd (fst g)) = true) (sm_maps M).
Proof.
  intros n M H. unfold sm_wf in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [Hg _].
  apply Forall_forall; intros g Hin; rewrite forallb_forall in Hg; pose proof (Hg g Hin) as X; apply andb_prop in X; exact (proj2 X).
Qed.

Lemma sm_wf_frz : forall n M, sm_wf n M = true -> Forall (fun p => lwf n (fst p) = true /\ lwf n (snd p) = true) (sm_frz M).
Proof.
  intros n M H. unfold sm_wf in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Forall_forall. intros p Hp.
  rewrite forallb_forall in H. specialize (H p Hp). apply andb_prop in H. exact H.
Qed.
Lemma forallb_nil_t : forall {A} (f : A -> bool), forallb f [] = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sm_wf_noown : forall n M, sm_wf n M = true ->
  (forallb (fun g => lwf n (fst (fst g)) && lwf n (snd (fst g))) (sm_maps M) && forallb (fun g => lwf n (fst g)) (sm_allow M) &&
   match sm_tid M with Some l => lwf n l | None => true end && lwf n (sm_brk M) && lwf n (sm_sbrk M) && lwf n (sm_sp M) &&
   forallb (fun p => lwf n (fst p) && lwf n (snd p)) (sm_frz M))%bool = true.
Proof. intros n M H. unfold sm_wf in H. apply andb_prop in H as [H _]. exact H. Qed.
Lemma sm_wf_own : forall n M, sm_wf n M = true -> Forall (fun p => lwf n (fst p) = true /\ lwf n (snd p) = true) (sm_own M).
Proof.
  intros n M H. unfold sm_wf in H. apply andb_prop in H as [_ H]. apply Forall_forall. intros p Hp.
  rewrite forallb_forall in H. specialize (H p Hp). apply andb_prop in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma own_pt_agree : forall n E E' M w, sm_wf n M = true -> agree n E E' -> (own_pt E' M w <-> own_pt E M w).
Proof.
  intros n E E' M w Hwf Ha. pose proof (sm_wf_own n M Hwf) as Hw. rewrite Forall_forall in Hw.
  split; intros (p & Hp & Hr); exists p; split; [exact Hp| |exact Hp|]; destruct (Hw p Hp) as [H1 H2]; unfold uE in *;
    rewrite ?(lden_agree n E E' _ H1 Ha), ?(lden_agree n E E' _ H2 Ha) in *; exact Hr.
Qed.
Lemma own_pt_keep : forall n E E' M M' w, sm_wf n M = true -> agree n E E' -> sm_own M' = sm_own M ->
  ~ own_pt E' M' w -> ~ own_pt E M w.
Proof. intros n E E' M M' w Hwf Ha HM Hno Ho. apply Hno. apply (own_pt_same E' M' M w (eq_sym HM)). apply (own_pt_agree n E E' M w Hwf Ha). exact Ho. Qed.

Lemma sm_wf_maps_mono : forall n n' M, sm_wf n M = true -> (n <= n')%positive ->
  Forall (fun g => lwf n' (fst (fst g)) = true /\ lwf n' (snd (fst g)) = true) (sm_maps M).
Proof.
  intros n n' M H Hn. destruct (sm_wf_parts n M H) as (Hg & _). pose proof (sm_wf_sizes n M H) as Hs.
  rewrite Forall_forall in *. intros g Hin. split; [exact (lwf_mono n n' _ Hn (Hg g Hin)) | exact (lwf_mono n n' _ Hn (Hs g Hin))].
Qed.
Lemma sm_wf_intro : forall n M,
  Forall (fun g => lwf n (fst (fst g)) = true /\ lwf n (snd (fst g)) = true) (sm_maps M) -> Forall (fun g => lwf n (fst g) = true) (sm_allow M) ->
  match sm_tid M with Some l => lwf n l = true | None => True end ->
  lwf n (sm_brk M) = true -> lwf n (sm_sbrk M) = true -> lwf n (sm_sp M) = true ->
  Forall (fun p => lwf n (fst p) = true /\ lwf n (snd p) = true) (sm_frz M) ->
  Forall (fun p => lwf n (fst p) = true /\ lwf n (snd p) = true) (sm_own M) -> sm_wf n M = true.
Proof.
  intros n M Hg Ha Ht Hb Hsb Hsp Hf Ho. unfold sm_wf. rewrite Hb, Hsb, Hsp.
  repeat (apply andb_true_intro; split); try reflexivity.
  - apply forallb_forall. intros g Hin. rewrite Forall_forall in Hg. destruct (Hg g Hin) as [H1 H2]. rewrite H1, H2. reflexivity.
  - apply forallb_forall. intros g Hin. rewrite Forall_forall in Ha. exact (Ha g Hin).
  - destruct (sm_tid M); [exact Ht | reflexivity].
  - apply forallb_forall. intros p Hin. rewrite Forall_forall in Hf. destruct (Hf p Hin) as [H1 H2]. rewrite H1, H2. reflexivity.
  - apply forallb_forall. intros p Hin. rewrite Forall_forall in Ho. destruct (Ho p Hin) as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

Lemma Forall_lwf_mono : forall {A} (f : A -> lin) n n' l, (n <= n')%positive -> Forall (fun g => lwf n (f g) = true) l -> Forall (fun g => lwf n' (f g) = true) l.
Proof. intros A f n n' l Hn H. rewrite Forall_forall in *. intros g Hg. exact (lwf_mono n n' _ Hn (H g Hg)). Qed.

Lemma Forall_frz_mono : forall n n' l, (n <= n')%positive -> Forall (fun p : lin * lin => lwf n (fst p) = true /\ lwf n (snd p) = true) l ->
  Forall (fun p : lin * lin => lwf n' (fst p) = true /\ lwf n' (snd p) = true) l.
Proof. intros n n' l Hn H. rewrite Forall_forall in *. intros g Hg. destruct (H g Hg) as [H1 H2]. split; [exact (lwf_mono n n' _ Hn H1) | exact (lwf_mono n n' _ Hn H2)]. Qed.

Lemma allowA_agree : forall n E E' M, sm_wf n M = true -> agree n E E' -> allowA E' M = allowA E M.
Proof.
  intros n E E' M Hw Ha. destruct (sm_wf_parts n M Hw) as (_ & Hal & _).
  unfold allowA. apply map_ext_in. intros [b k] Hin. rewrite Forall_forall in Hal. specialize (Hal _ Hin). cbn [fst] in Hal.
  unfold allow1, uE. cbn [fst snd]. rewrite (lden_agree_wf n E E' b Hal Ha). reflexivity.
Qed.

Lemma gden_agree : forall n E E' M, sm_wf n M = true -> agree n E E' -> List.map (gden E') (sm_maps M) = List.map (gden E) (sm_maps M).
Proof.
  intros n E E' M Hw Ha. destruct (sm_wf_parts n M Hw) as (Hg & _). pose proof (sm_wf_sizes n M Hw) as Hs.
  apply map_ext_in. intros g Hin. rewrite Forall_forall in Hg, Hs. specialize (Hg _ Hin). specialize (Hs _ Hin).
  unfold gden. rewrite (lden_agree_wf n E E' _ Hg Ha), (lden_agree_wf n E E' _ Hs Ha). reflexivity.
Qed.

Lemma lden_maps_agree : forall n E E' BL M, sm_wf n M = true -> agree n E E' -> lden_maps E' BL (sm_maps M) = lden_maps E BL (sm_maps M).
Proof.
  intros n E E' BL M Hw Ha. destruct (sm_wf_parts n M Hw) as (Hg & _). pose proof (sm_wf_sizes n M Hw) as Hs.
  apply lden_maps_ext. intros g Hin. rewrite Forall_forall in Hg, Hs. specialize (Hg _ Hin). specialize (Hs _ Hin).
  unfold gden. rewrite (lden_agree_wf n E E' _ Hg Ha), (lden_agree_wf n E E' _ Hs Ha). reflexivity.
Qed.
Lemma blob_ok_agree : forall n E E' M model model' BL, sm_wf n M = true -> agree n E E' ->
  alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) -> blob_ok E M model BL -> blob_ok E' M model' BL.
Proof.
  intros n E E' M model model' BL Hw Ha Ht (H1 & H2 & H3). split; [|split].
  - unfold blob_ent_ok in *. rewrite Ht. exact H1.
  - exact H2.
  - intros g Hg Hm. pose proof (sm_wf_sizes n M Hw) as Hs. rewrite Forall_forall in Hs.
    unfold gsz, uE. rewrite (lden_agree_wf n E E' _ (Hs _ Hg) Ha). exact (H3 g Hg Hm).
Qed.
(* [comment removed for export] *)
Lemma blob_ok_same : forall E M M' model model' BL, sm_maps M' = sm_maps M ->
  alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) -> blob_ok E M model BL -> blob_ok E M' model' BL.
Proof. intros E M M' model model' BL HM Ht (H1 & H2 & H3). split; [unfold blob_ent_ok in *; rewrite Ht; exact H1 | rewrite HM; split; [exact H2 | exact H3]]. Qed.
(* [comment removed for export] *)
Lemma blob_ok_nil : forall E M model, nomark (sm_maps M) = true -> blob_ok E M model [].
Proof.
  intros E M model Hn. split; [constructor | split; [reflexivity|]]. intros g Hg Hm. rewrite (nomark_in _ g Hn Hg) in Hm. discriminate.
Qed.
Lemma AM_nil : forall model0 E M, blob_of model0 = [] -> AM model0 E M = allowA E M.
Proof. intros model0 E M H. unfold AM. rewrite H. cbn [blobA List.map]. apply app_nil_r. Qed.
(* [comment removed for export] *)
Lemma den_blob_nil : forall segs LIMIT model0 mem0 E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  nomark (sm_maps M) = true -> blob_of model0 = [].
Proof. intros segs LIMIT model0 mem0 E S M ms model Hd Hn. exact (blob_nil_of_nomark E M model _ (dn_blob _ _ _ _ _ _ _ _ _ Hd) Hn). Qed.
Lemma den_old_maps : forall segs LIMIT model0 mem0 E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  nomark (sm_maps M) = true -> vm_maps (m_vmmaps model) = List.map (gden E) (sm_maps M).
Proof. intros segs LIMIT model0 mem0 E S M ms model Hd Hn. rewrite (dn_maps _ _ _ _ _ _ _ _ _ Hd). exact (lden_maps_nomark E _ _ Hn). Qed.
Lemma den_old_minv : forall segs LIMIT model0 mem0 E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  nomark (sm_maps M) = true -> MInv (allowA E M) model.
Proof.
  intros segs LIMIT model0 mem0 E S M ms model Hd Hn. rewrite <- (AM_nil model0 E M (den_blob_nil _ _ _ _ _ _ _ _ _ Hd Hn)).
  exact (dn_minv _ _ _ _ _ _ _ _ _ Hd).
Qed.
Lemma den_old_zr : forall segs LIMIT model0 mem0 E S M ms model, DEN segs LIMIT model0 mem0 E S M ms model ->
  nomark (sm_maps M) = true ->
  forall w, in_zr (sm_zr M) w = true -> outside E (s_rgs S) (Z_to_bv 64 w) -> ~ own_pt E M w -> ms_mem ms (Z_to_bv 64 w) = Some (Z_to_bv 8 0).
Proof.
  intros segs LIMIT model0 mem0 E S M ms model Hd Hn w Hw Ho Hno. apply (dn_zr _ _ _ _ _ _ _ _ _ Hd w Hw Ho Hno).
  rewrite (den_blob_nil _ _ _ _ _ _ _ _ _ Hd Hn). apply blob_sh_nil.
Qed.

(* [comment removed for export] *)
Ltac den_noblob Hnm :=
  match goal with
  | Hblob : blob_ok ?E ?M ?model (blob_of ?m0) |- _ =>
      let Hb0 := fresh "Hblob0" in
      pose proof (blob_nil_of_nomark E M model _ Hblob Hnm) as Hb0;
      match goal with Hmaps : vm_maps _ = lden_maps E _ (sm_maps M) |- _ => rewrite (lden_maps_nomark E _ _ Hnm) in Hmaps end;
      match goal with Hminv : MInv (AM m0 E M) _ |- _ => rewrite (AM_nil m0 E M Hb0) in Hminv end;
      match goal with Hzr : forall w, in_zr _ w = true -> _ |- _ =>
        let Hzr' := fresh "Hzr0" in
        assert (Hzr' := fun w Hw Ho Hno => Hzr w Hw Ho Hno ltac:(rewrite Hb0; apply blob_sh_nil)); clear Hzr; rename Hzr' into Hzr end
  end.

Lemma AM_agree : forall n model0 E E' M, sm_wf n M = true -> agree n E E' -> AM model0 E' M = AM model0 E M.
Proof. intros n model0 E E' M Hw Ha. unfold AM. rewrite (allowA_agree n E E' M Hw Ha). reflexivity. Qed.
(* [comment removed for export] *)
Lemma blob_ok_step : forall n E E' M M' model model' BL, sm_wf n M = true -> agree n E E' -> sm_maps M' = sm_maps M ->
  alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) -> blob_ok E M model BL -> blob_ok E' M' model' BL.
Proof.
  intros n E E' M M' model model' BL Hw Ha HM Ht Hb. apply (blob_ok_same E' M M' model' model' BL HM eq_refl).
  exact (blob_ok_agree n E E' M model model' BL Hw Ha Ht Hb).
Qed.
Lemma AM_step : forall n model0 E E' M M', sm_wf n M = true -> agree n E E' -> sm_allow M' = sm_allow M -> AM model0 E' M' = AM model0 E M.
Proof. intros n model0 E E' M M' Hw Ha HM. rewrite <- (AM_agree n model0 E E' M Hw Ha). unfold AM, allowA. rewrite HM. reflexivity. Qed.
Lemma lden_maps_step : forall n E E' BL M M', sm_wf n M = true -> agree n E E' -> sm_maps M' = sm_maps M ->
  lden_maps E' BL (sm_maps M') = lden_maps E BL (sm_maps M).
Proof. intros n E E' BL M M' Hw Ha HM. rewrite HM. exact (lden_maps_agree n E E' BL M Hw Ha). Qed.


Lemma Forall_agree_maps : forall n E E' M (P : valu -> lin * lin * gkind -> Prop),
  sm_wf n M = true -> agree n E E' ->
  (forall g, lwf n (fst (fst g)) = true -> lwf n (snd (fst g)) = true -> P E g -> P E' g) ->
  Forall (P E) (sm_maps M) -> Forall (P E') (sm_maps M).
Proof.
  intros n E E' M P Hw Ha HP HF. destruct (sm_wf_parts n M Hw) as (Hg & _). pose proof (sm_wf_sizes n M Hw) as Hs.
  rewrite Forall_forall in *. intros g Hin. apply HP; [exact (Hg g Hin) | exact (Hs g Hin) | exact (HF g Hin)].
Qed.

Lemma outside_agree_shape : forall n E E' rgs rgs' x, bases_wf n rgs = true -> agree n E E' -> shape rgs' = shape rgs ->
  outside E' rgs' x -> outside E rgs x.
Proof.
  intros n E E' rgs rgs' x Hb Ha Hs H. apply (outside_agree n E E' rgs x Hb Ha).
  apply (outside_shape E' rgs' rgs x); [symmetry; exact Hs | exact H].
Qed.

Lemma rl_ok_agree_shape : forall n E E' model model' rgs rgs',
  bases_wf n rgs = true -> agree n E E' -> shape rgs' = shape rgs -> m_vmmaps model' = m_vmmaps model ->
  Forall (rl_ok E model) rgs -> Forall (rl_ok E' model') rgs'.
Proof.
  intros n E E' model model' rgs. induction rgs as [|R rs IH]; intros [|R' rs'] Hb Ha Hs Hm HF; cbn in Hs; try discriminate; [constructor|].
  injection Hs as Hbs Hsz Hrs. inversion HF as [|? ? HR HRs]; subst. cbn [bases_wf forallb] in Hb. unfold bases_wf in Hb. cbn in Hb.
  apply andb_prop in Hb as [Hb1 Hb2]. apply andb_prop in Hb1 as [Hb1 Hb1s]. constructor; [|exact (IH rs' Hb2 Ha Hrs Hm HRs)].
  assert (HA : uE E' (rg_base R') = uE E (rg_base R)) by (unfold uE; rewrite Hbs; rewrite (lden_agree_wf n E E' _ Hb1 Ha); reflexivity).
  assert (HS : rsz E' R' = rsz E R) by (unfold rsz; rewrite Hsz; rewrite (lden_agree_wf n E E' _ Hb1s Ha); reflexivity).
  unfold rl_ok, app_pt in *. rewrite HA, HS, Hm. exact HR.
Qed.

Section Seg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
#[using="Type"] Lemma munrestrict_outside : forall H full (msr msr' : machine_state) x,
  ms_mem msr = mrestrict H full -> (ms_mem msr' x = ms_mem msr x) -> munrestrict H full (ms_mem msr') x = full x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros H full msr msr' x Hm Hx. unfold munrestrict. destruct (H x) eqn:Hh; [reflexivity|].
  rewrite Hx, Hm. unfold mrestrict. rewrite Hh. reflexivity.
Qed.

#[using="Hwx"] Theorem den_isteps : forall E S M ms model T L msr' E',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  isteps segs (restrict (Hof E M model) ms) msr' ->
  sden segs E' L msr' -> agree (s_next S) E E' -> (s_next S <= s_next L)%positive ->
  (forall x, outside E (s_rgs S) x -> ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) ->
  shape (s_rgs L) = shape (s_rgs S) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' L M ms' model' -> agree (s_next S) E E' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T L msr' E' Hd Hst Hd' Ha Hn Hfr Hsh Hk.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  assert (Hcov : lazy_cover H (m_vm_lazy model) (AM model0 E M)) by (apply lazy_cover_mkH_app; intros x Hx; exact Hx).
  apply (rzc_fx_isteps segs cfg H Hhoff Hwx (AM model0 E M) (restrict H ms) msr' ms model T eq_refl Hcov (A_wf_app _ _ Hawf (A_wf_blobA _)) Hminv Hh Hst).
  intros model' Hinv' Hsb' Hcl'.
  destruct (same_but_materialized_frame model model' Hsb') as (Hfd & Hvm & Hlz & Hio & Hfs & Hpr & Hli & Htm & _ & _ & _ & _ & Hhl & Htd & _).
  assert (HA : allowA E' M = allowA E M) by exact (allowA_agree (s_next S) E E' M Hwf Ha).
  assert (HH : Hof E' M model' = H) by (unfold Hof, H; rewrite Hlz, HA; reflexivity).
  apply (Hk E' _ model'); [|exact Ha].
  assert (Hwf' : sm_wf (s_next L) M = true) by exact (sm_wf_mono _ _ M Hn Hwf).
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  constructor.
  - rewrite HH. rewrite restrict_unrestrict_clean by exact Hcl'. exact Hd'.
  - exact Hwf'.
  - exact (bases_wf_shape _ _ _ _ Hn Hsh Hbw).
  - rewrite Hhl. exact Hh.
  - rewrite HA. exact Hawf.
  - exact Hanz.
  - rewrite (AM_agree (s_next S) model0 E E' M Hwf Ha). exact Hinv'.
  - rewrite HH. exact Hhoff.
  - rewrite Hvm. exact Hres.
  - rewrite Hvm. exact Hlim.
  - rewrite Hvm, Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - rewrite Hvm. exact Hspok.
  - rewrite Hvm, Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hvm, Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htd, Htid. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - rewrite Hvm, Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha).
  - apply (Forall_agree_maps (s_next S) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
    intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model')) Hwf Ha).
    + intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + rewrite Hvm. exact Hgtop.
  - rewrite Hvm, Hlz. exact Hivwf.
  - rewrite Hvm. exact Hpd.
  - rewrite Hvm. exact Hmres.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => kind_ok E model' g) Hwf Ha).
    + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + unfold kind_ok. rewrite Hvm, Hlz. exact Hkind.
  - rewrite Hlz, Hvm. exact Hlzm.
  - exact Hzrsh.
  - rewrite Hvm. exact Hzrm.
  - intros w Hw Hout Hno Hnb. cbn [unrestrict ms_mem].
    assert (Hout0 : outside E (s_rgs S) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ Hbw Ha Hsh Hout).
    rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr _ Hout0)).
    exact (Hzr w Hw Hout0 (own_pt_keep _ E E' M M w Hwf Ha eq_refl Hno) Hnb).
  - exact (rl_ok_agree_shape _ E E' model model' (s_rgs S) (s_rgs L) Hbw Ha Hsh Hvm Hrl).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). rewrite Hfd, Hio, Hfs, Hli, Htm. repeat split; assumption.
  - rewrite Hpr, Htd. exact Hproc.
  - intros q Hq w Hw. pose proof (sm_wf_frz _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hfrz q Hq w Hw0) as (Htp & Hout & Hm). split; [unfold alloc_top in *; rewrite Hvm; exact Htp|]. split.
    + apply (outside_shape E' (s_rgs S) (s_rgs L) _ Hsh). apply (proj1 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha)). exact Hout.
    + cbn [unrestrict ms_mem]. rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr _ Hout)). exact Hm.
  - cbn [unrestrict ms_rom]. rewrite (fx_rom segs _ _ Hst). cbn [restrict ms_rom]. exact Hrom.
  - intros q Hq w Hw. pose proof (sm_wf_own _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hown q Hq w Hw0) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros Hout'.
    assert (Hout : outside E (s_rgs S) (Z_to_bv 64 w)).
    { apply (proj2 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha)). apply (outside_shape E' (s_rgs L) (s_rgs S) _ (eq_sym Hsh)). exact Hout'. }
    cbn [unrestrict ms_mem]. rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr _ Hout)). exact (Hm Hout).
  - apply (blob_ok_agree (s_next S) E E' M model model' _ Hwf Ha); [rewrite Hvm; reflexivity | exact Hblob].
Qed.

#[using="Hwx"] Theorem den_seg : forall t img ins depth p S finals E M ms model T,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p S = Some finals ->
  DEN segs LIMIT model0 mem0 E S M ms model -> bases_ins ins (s_rgs S) = true ->
  (forall x, (x < s_next S)%positive -> In x ins) ->
  (forall L E' ms' model', In L finals -> DEN segs LIMIT model0 mem0 E' L M ms' model' -> agree (s_next S) E E' ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros t img ins depth p S finals E M ms model T Ht Himg Hck Hd Hbi Hins Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (check_frame segs t img ins depth p S finals Ht Himg Hck E (restrict (Hof E M model) ms) Hsd Hbw Hbi)
    as (L & msr' & E' & HL & Hst & Hd' & Hi & Hfr & Hsh & Hn).
  assert (Ha : agree (s_next S) E E') by (intros x Hx; symmetry; exact (Hi x (Hins x Hx))).
  exact (den_isteps E S M ms model T L msr' E' Hd Hst Hd' Ha Hn Hfr Hsh (fun E2 ms2 model2 HD2 Ha2 => Hk L E2 ms2 model2 HL HD2 Ha2)).
Qed.
End Seg.
