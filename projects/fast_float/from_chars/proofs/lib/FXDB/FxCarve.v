(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxRunPostM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition carve_R2 (R : region) (o1 o2 : Z) (lj : lin) : region :=
  RG (ladd (laddc (rg_base R) o1) lj) (lsub (lconst (o2 - o1)) lj) RW TEmpty.
Definition carve_rgs (rgs : list region) (j0 : nat) (o1 o2 : Z) (lj : lin) : list region :=
  match nth_error rgs j0 with
  | Some R => split_rgs rgs j0 o1 o2 ++ [carve_R2 R o1 o2 lj]
  | None => rgs
  end.
Definition own_add (M : smodel) (p : lin * lin) : smodel :=
  SM (sm_maps M) (sm_allow M) (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (p :: sm_own M).
Definition carve_mem0 (mem0 mem : word -> option byte) (a L : Z) : word -> option byte :=
  fun w => if (Z.leb a (bv_unsigned w) && Z.ltb (bv_unsigned w) (a + L))%bool then mem w else mem0 w.

Definition in_rg (E : valu) (R : region) (x : Z) : Prop := uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R.

Lemma outside_nth_iff : forall E rgs (x : word),
  outside E rgs x <-> (forall k R, nth_error rgs k = Some R -> ~ in_rg E R (bv_unsigned x)).
Proof.
  intros E rgs x. unfold outside, in_rg, uE. rewrite Forall_nth'. split.
  - intros H k R Hk Hin. specialize (H k R Hk). cbv beta in H. lia.
  - intros H k R Hk. specialize (H k R Hk). cbv beta. lia.
Qed.

Section Carve.
Variable E : valu.
Variables (rgs : list region) (j0 : nat) (R : region) (o1 o2 sz : Z) (lj : lin).
Hypothesis Hj0 : nth_error rgs j0 = Some R.
Hypothesis Hsz : is_const (rg_size R) = Some sz.
Hypothesis Ho : 0 < o1 < o2 /\ o2 < sz.
Hypothesis HL : 0 <= uE E lj < o2 - o1.
Hypothesis HA : uE E (rg_base R) + sz <= two64.

Let A := uE E (rg_base R).
Let L := uE E lj.
Definition R1c : region := RGz (rg_base R) o1 RW (below_cont (rg_cont R) o1).
Definition R3c : region := RGz (laddc (rg_base R) o2) (csz R - o2) RW (rekey_acc (rg_cont R) o2 (Z.to_nat (csz R - o2)) TEmpty).

#[using="Hsz"] Lemma csz_R : csz R = sz. Proof. LiaFast.lf_pins (fun (Hsz : LiaFast.U) => LiaFast.u0). unfold csz. rewrite Hsz. reflexivity. Qed.
#[using="Hsz"] Lemma rsz_R : rsz E R = sz.
Proof. LiaFast.lf_pins (fun (Hsz : LiaFast.U) => LiaFast.u0). unfold rsz. destruct (is_const_sound E _ sz Hsz) as [-> Hr]. apply u_small64. exact Hr. Qed.

#[using="Type"] Lemma base_R1 : uE E (rg_base R1c) = A. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="o2 sz lj Ho HL HA A L"] Lemma rsz_R1 : rsz E R1c = o1.
Proof. LiaFast.lf_pins (fun (o2 sz lj Ho HL HA A L : LiaFast.U) => LiaFast.u0). unfold rsz, R1c, RGz. cbn [rg_size]. rewrite lden_lconst. apply u_small64. pose proof (uE_range E (rg_base R)). unfold A, two64 in *. lia. Qed.
#[using="o1 sz lj Ho HL HA L"] Lemma base_R3 : uE E (rg_base R3c) = A + o2.
Proof. LiaFast.lf_pins (fun (o1 sz lj Ho HL HA L : LiaFast.U) => LiaFast.u0). unfold R3c, RGz, uE. cbn [rg_base]. rewrite lden_laddc. rewrite u_small64; [reflexivity|]. pose proof (uE_range E (rg_base R)). unfold A, uE in *. lia. Qed.
#[using="o1 lj Hsz Ho HL HA A L"] Lemma rsz_R3 : rsz E R3c = sz - o2.
Proof. LiaFast.lf_pins (fun (o1 lj Hsz Ho HL HA A L : LiaFast.U) => LiaFast.u0). unfold rsz, R3c, RGz. cbn [rg_size]. rewrite lden_lconst, csz_R. apply u_small64. pose proof (uE_range E (rg_base R)). unfold A, two64 in *. lia. Qed.
#[using="sz Ho HL HA"] Lemma base_R2 : uE E (rg_base (carve_R2 R o1 o2 lj)) = A + o1 + L.
Proof. LiaFast.lf_pins (fun (sz Ho HL HA : LiaFast.U) => LiaFast.u0).
  unfold carve_R2, uE. cbn [rg_base]. rewrite lden_ladd, bv_add_unsigned, lden_laddc. rewrite u_small64 by (pose proof (uE_range E (rg_base R)); unfold A, uE in *; lia).
  fold (uE E lj). fold L. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. pose proof (uE_range E (rg_base R)). unfold A, L, uE in *. lia.
Qed.
#[using="sz Ho HL HA A"] Lemma rsz_R2 : rsz E (carve_R2 R o1 o2 lj) = o2 - o1 - L.
Proof. LiaFast.lf_pins (fun (sz Ho HL HA A : LiaFast.U) => LiaFast.u0).
  unfold rsz, carve_R2. cbn [rg_size]. rewrite lden_lsub, bv_sub_unsigned, lden_lconst. rewrite u_small64 by (pose proof (uE_range E (rg_base R)); unfold A, two64 in *; lia).
  fold (uE E lj). fold L. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. pose proof (uE_range E (rg_base R)). unfold L in *. lia.
Qed.

#[using="Hj0"] Lemma nth_carve : forall k R', nth_error (carve_rgs rgs j0 o1 o2 lj) k = Some R' ->
  (k = j0 /\ R' = R1c) \/ (k <> j0 /\ nth_error rgs k = Some R') \/ R' = R3c \/ R' = carve_R2 R o1 o2 lj.
Proof. LiaFast.lf_pins (fun (Hj0 : LiaFast.U) => LiaFast.u0).
  intros k R' Hk. unfold carve_rgs, split_rgs in Hk. rewrite Hj0 in Hk.
  pose proof (nth_error_Some rgs j0) as Hlen. rewrite Hj0 in Hlen. specialize (proj1 Hlen ltac:(discriminate)) as Hlj.
  destruct (Nat.lt_ge_cases k (length rgs)) as [Hlt|Hge].
  - rewrite <- app_assoc, nth_error_app1 in Hk by (rewrite length_upd; exact Hlt).
    destruct (Nat.eq_dec k j0) as [->|Hne].
    + left. rewrite (nth_upd_same rgs j0 _ R Hj0) in Hk. injection Hk as <-. split; reflexivity.
    + right; left. rewrite nth_upd_other in Hk by (intros Hc; apply Hne; symmetry; exact Hc). split; [exact Hne | exact Hk].
  - rewrite <- app_assoc, nth_error_app2 in Hk by (rewrite length_upd; exact Hge). rewrite length_upd in Hk.
    destruct (k - length rgs)%nat as [|[|kk]] eqn:Ek; cbn in Hk.
    + injection Hk as <-. right; right; left. reflexivity.
    + injection Hk as <-. right; right; right. reflexivity.
    + destruct kk; discriminate.
Qed.

#[using="E lj Hj0 HL A L"] Lemma nth_split : forall k R', nth_error (split_rgs rgs j0 o1 o2) k = Some R' ->
  (k = j0 /\ R' = R1c) \/ (k <> j0 /\ nth_error rgs k = Some R') \/ (k = length rgs /\ R' = R3c).
Proof. LiaFast.lf_pins (fun (E lj Hj0 HL A L : LiaFast.U) => LiaFast.u0).
  intros k R' Hk. unfold split_rgs in Hk. rewrite Hj0 in Hk.
  destruct (Nat.lt_ge_cases k (length rgs)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hk by (rewrite length_upd; exact Hlt).
    destruct (Nat.eq_dec k j0) as [->|Hne].
    + left. rewrite (nth_upd_same rgs j0 _ R Hj0) in Hk. injection Hk as <-. split; reflexivity.
    + right; left. rewrite nth_upd_other in Hk by (intros Hc; apply Hne; symmetry; exact Hc). split; [exact Hne | exact Hk].
  - rewrite nth_error_app2 in Hk by (rewrite length_upd; exact Hge). rewrite length_upd in Hk.
    destruct (k - length rgs)%nat as [|kk] eqn:Ek; cbn in Hk.
    + injection Hk as <-. right; right. split; [lia | reflexivity].
    + destruct kk; discriminate.
Qed.

#[using="R Hj0"] Lemma nth_carve_old : forall k R', k <> j0 -> nth_error rgs k = Some R' -> nth_error (carve_rgs rgs j0 o1 o2 lj) k = Some R'.
Proof. LiaFast.lf_pins (fun (R Hj0 : LiaFast.U) => LiaFast.u0).
  intros k R' Hne Hk. unfold carve_rgs, split_rgs. rewrite Hj0.
  pose proof (nth_error_Some rgs k) as Hlen. rewrite Hk in Hlen. specialize (proj1 Hlen ltac:(discriminate)) as Hlk.
  rewrite <- app_assoc, nth_error_app1 by (rewrite length_upd; exact Hlk).
  rewrite nth_upd_other by (intros Hc; apply Hne; symmetry; exact Hc). exact Hk.
Qed.
#[using="Hj0"] Lemma nth_carve_R1 : nth_error (carve_rgs rgs j0 o1 o2 lj) j0 = Some R1c.
Proof. LiaFast.lf_pins (fun (Hj0 : LiaFast.U) => LiaFast.u0).
  unfold carve_rgs, split_rgs. rewrite Hj0.
  pose proof (nth_error_Some rgs j0) as Hlen. rewrite Hj0 in Hlen. specialize (proj1 Hlen ltac:(discriminate)) as Hlj.
  rewrite <- app_assoc, nth_error_app1 by (rewrite length_upd; exact Hlj). exact (nth_upd_same rgs j0 _ R Hj0).
Qed.
#[using="E Hj0 HL A L"] Lemma nth_carve_R3 : nth_error (carve_rgs rgs j0 o1 o2 lj) (length rgs) = Some R3c.
Proof. LiaFast.lf_pins (fun (E Hj0 HL A L : LiaFast.U) => LiaFast.u0).
  unfold carve_rgs, split_rgs. rewrite Hj0. rewrite <- app_assoc, nth_error_app2 by (rewrite length_upd; lia).
  rewrite length_upd, Nat.sub_diag. reflexivity.
Qed.
#[using="E Hj0 HL A L"] Lemma nth_carve_R2 : nth_error (carve_rgs rgs j0 o1 o2 lj) (Datatypes.S (length rgs)) = Some (carve_R2 R o1 o2 lj).
Proof. LiaFast.lf_pins (fun (E Hj0 HL A L : LiaFast.U) => LiaFast.u0).
  unfold carve_rgs, split_rgs. rewrite Hj0. rewrite <- app_assoc, nth_error_app2 by (rewrite length_upd; lia).
  rewrite length_upd. replace (Datatypes.S (length rgs) - length rgs)%nat with 1%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="sz Hj0 Hsz Ho HL HA"] Theorem outside_carve_iff : forall x : word, rgs_disj E rgs ->
  (outside E (carve_rgs rgs j0 o1 o2 lj) x <-> (outside E rgs x \/ (A + o1 <= bv_unsigned x < A + o1 + L))).
Proof. LiaFast.lf_pins (fun (sz Hj0 Hsz Ho HL HA : LiaFast.U) => LiaFast.u0).
  intros x Hdj. pose proof rsz_R as HrR. pose proof rsz_R1 as Hr1. pose proof rsz_R3 as Hr3. pose proof rsz_R2 as Hr2.
  pose proof base_R3 as Hb3. pose proof base_R2 as Hb2. fold A L in Hb3, Hb2.
  rewrite !outside_nth_iff. split.
  - intros Hn. destruct (Z_lt_le_dec (bv_unsigned x) (A + o1 + L)) as [Hlt|Hge].
    + destruct (Z_lt_le_dec (bv_unsigned x) (A + o1)) as [Hlt1|Hge1]; [|right; lia].
      left. intros k R' Hk Hin. destruct (Nat.eq_dec k j0) as [->|Hne].
      * rewrite Hj0 in Hk. injection Hk as <-. apply (Hn j0 R1c nth_carve_R1). unfold in_rg in *. rewrite base_R1, Hr1. fold A in Hin |- *. lia.
      * exact (Hn k R' (nth_carve_old k R' Hne Hk) Hin).
    + left. intros k R' Hk Hin. destruct (Nat.eq_dec k j0) as [->|Hne].
      * rewrite Hj0 in Hk. injection Hk as <-. unfold in_rg in Hin. rewrite HrR in Hin. fold A in Hin.
        destruct (Z_lt_le_dec (bv_unsigned x) (A + o2)) as [Hlt2|Hge2].
        -- apply (Hn _ _ nth_carve_R2). unfold in_rg. rewrite Hb2, Hr2. lia.
        -- apply (Hn _ _ nth_carve_R3). unfold in_rg. rewrite Hb3, Hr3. lia.
      * exact (Hn k R' (nth_carve_old k R' Hne Hk) Hin).
  - intros [Hout|Hcp] k R' Hk Hin; destruct (nth_carve k R' Hk) as [(-> & ->)|[(Hne & Hk')|[->| ->]]].
    + apply (Hout j0 R Hj0). unfold in_rg in *. rewrite base_R1, Hr1 in Hin. rewrite HrR. fold A in Hin |- *. lia.
    + exact (Hout k R' Hk' Hin).
    + apply (Hout j0 R Hj0). unfold in_rg in *. rewrite Hb3, Hr3 in Hin. rewrite HrR. fold A in Hin |- *. lia.
    + apply (Hout j0 R Hj0). unfold in_rg in *. rewrite Hb2, Hr2 in Hin. rewrite HrR. fold A in Hin |- *. lia.
    + unfold in_rg in Hin. rewrite base_R1, Hr1 in Hin. fold A in Hin. lia.
    + pose proof (rgs_disj_nth E rgs k j0 R' R Hdj Hne Hk' Hj0) as Hd. unfold rg_disj in Hd. rewrite HrR in Hd.
      unfold in_rg, uE in Hin. fold (uE E (rg_base R)) A in Hd. lia.
    + unfold in_rg in Hin. rewrite Hb3, Hr3 in Hin. lia.
    + unfold in_rg in Hin. rewrite Hb2, Hr2 in Hin. lia.
Qed.
End Carve.

(* [comment removed for export] *)
Lemma rgs_disj_snoc : forall E l R2, rgs_disj E l -> Forall (fun R' => rg_disj E R' R2) l -> rgs_disj E (l ++ [R2]).
Proof.
  intros E l R2. induction l as [|x l IH]; intros Hd Hf; cbn [app rgs_disj]; [split; [constructor | exact I]|].
  destruct Hd as [Hx Hl]. inversion Hf as [|? ? Hx2 Hl2]; subst. split; [apply Forall_app; split; [exact Hx | constructor; [exact Hx2 | constructor]]|].
  exact (IH Hl Hl2).
Qed.
Lemma state_wf_bases : forall P, state_wf P = true -> bases_wf (s_next P) (s_rgs P) = true.
Proof.
  intros P H. unfold state_wf in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  unfold bases_wf. rewrite forallb_forall in *. intros R HR. specialize (H R HR). unfold rwf in H.
  apply andb_prop in H as [H _]. exact H.
Qed.
(* [comment removed for export] *)
Lemma rl_ok_sub : forall E model R R', rl_ok E model R -> 0 < rsz E R' ->
  uE E (rg_base R) <= uE E (rg_base R') -> uE E (rg_base R') + rsz E R' <= uE E (rg_base R) + rsz E R -> rl_ok E model R'.
Proof.
  intros E model R R' [Hs [Happ|(Hsh & Hap & Hpt)]] Hs' H1 H2; split; [exact Hs'| |exact Hs'|].
  - left. intros w Hw. apply Happ. lia.
  - right. split; [lia|]. split; [intros x Hx; apply Hap; lia | intros w Hw; apply Hpt; lia].
Qed.

Lemma state_wf_snoc : forall S l R2, state_wf (with_rgs S (l ++ [R2])) = true -> state_wf (with_rgs S l) = true.
Proof.
  intros S l R2 H. unfold state_wf in *. cbn [with_rgs s_next s_regs s_rgs s_facts s_resv] in *.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite forallb_app in H2. apply andb_prop in H2 as [H2 _]. rewrite H1, H2, H3, H4. reflexivity.
Qed.
Lemma uE_laddc : forall E l c, 0 <= c -> uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. intros E l c Hc H. unfold uE. rewrite lden_laddc. apply u_small64. pose proof (uE_range E l). unfold uE in *. lia. Qed.

Section CarveDen.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_carve : forall E S M ms model j0 R o1 o2 sz lj,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  nth_error (s_rgs S) j0 = Some R -> rk_wz (rg_kind R) = true -> is_const (rg_size R) = Some sz -> 0 < o1 < o2 /\ o2 < sz ->
  rg_sub_ok R (R1c R o1) 0 = true -> rg_sub_ok R (R3c R o2) o2 = true ->
  state_wf (with_rgs S (carve_rgs (s_rgs S) j0 o1 o2 lj)) = true -> lwf (s_next S) lj = true ->
  0 <= uE E lj < o2 - o1 ->
  DEN segs LIMIT model0 (carve_mem0 mem0 (ms_mem ms) (uE E (rg_base R) + o1) (uE E lj)) E
      (with_rgs S (carve_rgs (s_rgs S) j0 o1 o2 lj)) (own_add M (laddc (rg_base R) o1, lj)) ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model j0 R o1 o2 sz lj Hd Hj0 Hkd Hsz Ho Hs1 Hs3 Hswf Hwl HL.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  pose proof (proj1 (Forall_nth' _ _) HG j0 R Hj0) as HRok.
  pose proof (rsz_R E R sz Hsz) as HrR.
  pose proof HRok as HRok0. destruct HRok0 as (Hrs & Hrw & Hpts & Hcont). rewrite HrR in Hrs, Hrw, Hpts.
  set (A := uE E (rg_base R)) in *. set (L := uE E lj) in *.
  assert (HA' : uE E (rg_base R) + sz <= two64) by (unfold A, uE in *; lia).
  set (S' := with_rgs S (carve_rgs (s_rgs S) j0 o1 o2 lj)).
  set (M' := own_add M (laddc (rg_base R) o1, lj)).
  assert (HH : Hof E M' model = H) by reflexivity.
  assert (Hiff : forall x : word, outside E (s_rgs S') x <-> (outside E (s_rgs S) x \/ (A + o1 <= bv_unsigned x < A + o1 + L)))
    by (intros x; exact (outside_carve_iff E (s_rgs S) j0 R o1 o2 sz lj Hj0 Hsz Ho HL HA' x HD)).
  assert (Hpt : forall i, 0 <= i < sz -> rd1 segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (A + i)) <> None /\
                                        wview segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (A + i)) <> None).
  { intros i Hi. specialize (Hpts i Hi). unfold rk_wz in Hkd. destruct (rg_kind R); try discriminate; [exact Hpts | exact (proj1 Hpts)]. }
  assert (Hvis : forall i, 0 <= i < sz -> H (Z_to_bv 64 (A + i)) = false).
  { intros i Hi. apply (rg_ok_visible segs H (ms_mem ms) E R Hhoff HRok). rewrite HrR. exact Hi. }
  pose proof (uE_range E (rg_base R)) as RA. fold A in RA.
  assert (Hhd : uE E (laddc (rg_base R) o1) = A + o1) by (apply uE_laddc; unfold A in *; lia).
  (* [comment removed for export] *)
  assert (Hop : forall w, own_pt E M' w <-> (A + o1 <= w < A + o1 + L) \/ own_pt E M w).
  { intros w. unfold own_pt. cbn [sm_own M' own_add]. split.
    - intros (p & [<-|Hp] & Hw); [left; cbn [fst snd] in Hw; rewrite Hhd in Hw; exact Hw | right; exists p; split; assumption].
    - intros [Hw|(p & Hp & Hw)]; [exists (laddc (rg_base R) o1, lj); split; [left; reflexivity | cbn [fst snd]; rewrite Hhd; exact Hw]
                                | exists p; split; [right; exact Hp | exact Hw]]. }
  (* [comment removed for export] *)
  assert (Hswf1 : state_wf (with_rgs S (split_rgs (s_rgs S) j0 o1 o2)) = true).
  { unfold S', carve_rgs in Hswf. rewrite Hj0 in Hswf. exact (state_wf_snoc S _ _ Hswf). }
  destruct (rg_sub_sound segs E _ R (R1c R o1) 0 HRok Hs1) as (HR1ok & HA1 & _ & _ & HS1 & _).
  destruct (rg_sub_sound segs E _ R (R3c R o2) o2 HRok Hs3) as (HR3ok & HA3 & _ & _ & HS3 & _).
  rewrite HrR in HS1, HS3.
  assert (Hb1 : uE E (rg_base (R1c R o1)) = A) by reflexivity.
  assert (Hr1 : rsz E (R1c R o1) = o1) by (eapply rsz_R1; eassumption).
  assert (Hb3 : uE E (rg_base (R3c R o2)) = A + o2) by (eapply base_R3; eassumption).
  assert (Hr3 : rsz E (R3c R o2) = sz - o2) by (eapply rsz_R3; eassumption).
  assert (HG1 : Forall (rg_ok segs E (ms_mem (restrict H ms))) (split_rgs (s_rgs S) j0 o1 o2)).
  { apply Forall_nth'. intros k R' Hk.
    destruct (nth_split E (s_rgs S) j0 R o1 o2 lj Hj0 HL k R' Hk) as [(-> & ->)|[(Hne & Hko)|(-> & ->)]].
    - exact HR1ok.
    - exact (proj1 (Forall_nth' _ _) HG k R' Hko).
    - exact HR3ok. }
  (* [comment removed for export] *)
  assert (Hsub : forall Ra k' Rb, (bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base Ra))) ->
            bv_unsigned (lden E (rg_base Ra)) + rsz E Ra <= bv_unsigned (lden E (rg_base R)) + rsz E R ->
            k' <> j0 -> nth_error (s_rgs S) k' = Some Rb -> rg_disj E Ra Rb /\ rg_disj E Rb Ra).
  { intros Ra k' Rb X1 X2 Hne Hko. pose proof (rgs_disj_nth E (s_rgs S) k' j0 Rb R HD Hne Hko Hj0) as Hdd.
    unfold rg_disj in *. split; lia. }
  assert (HD1 : rgs_disj E (split_rgs (s_rgs S) j0 o1 o2)).
  { apply rgs_disj_nth_inv. intros k k' Ra Rb Hkk Ha Hb.
    pose proof (nth_error_Some (split_rgs (s_rgs S) j0 o1 o2) k') as Hlen'. rewrite Hb in Hlen'. specialize (proj1 Hlen' ltac:(discriminate)) as Hlk'.
    assert (Hlens : length (split_rgs (s_rgs S) j0 o1 o2) = Datatypes.S (length (s_rgs S))).
    { unfold split_rgs. rewrite Hj0, length_app, length_upd. cbn [length]. lia. }
    rewrite Hlens in Hlk'.
    destruct (nth_split E (s_rgs S) j0 R o1 o2 lj Hj0 HL k Ra Ha) as [(-> & ->)|[(Hne & Hko)|(-> & ->)]];
    destruct (nth_split E (s_rgs S) j0 R o1 o2 lj Hj0 HL k' Rb Hb) as [(-> & ->)|[(Hne' & Hko')|(-> & ->)]]; try lia.
    - assert (X1 : bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base (R1c R o1)))) by (rewrite HA1; lia).
      assert (X2 : bv_unsigned (lden E (rg_base (R1c R o1))) + rsz E (R1c R o1) <= bv_unsigned (lden E (rg_base R)) + rsz E R) by (rewrite HA1, HrR; lia).
      exact (proj1 (Hsub (R1c R o1) k' Rb X1 X2 Hne' Hko')).
    - unfold rg_disj. rewrite HA1, HA3, Hr1, Hr3. lia.
    - assert (X1 : bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base (R1c R o1)))) by (rewrite HA1; lia).
      assert (X2 : bv_unsigned (lden E (rg_base (R1c R o1))) + rsz E (R1c R o1) <= bv_unsigned (lden E (rg_base R)) + rsz E R) by (rewrite HA1, HrR; lia).
      exact (proj2 (Hsub (R1c R o1) k Ra X1 X2 Hne Hko)).
    - exact (rgs_disj_nth E (s_rgs S) k k' Ra Rb HD ltac:(lia) Hko Hko').
    - assert (X1 : bv_unsigned (lden E (rg_base R)) <= bv_unsigned (lden E (rg_base (R3c R o2)))) by (rewrite HA3; lia).
      assert (X2 : bv_unsigned (lden E (rg_base (R3c R o2))) + rsz E (R3c R o2) <= bv_unsigned (lden E (rg_base R)) + rsz E R) by (rewrite HA3, HrR; lia).
      exact (proj2 (Hsub (R3c R o2) k Ra X1 X2 Hne Hko)). }
  set (R2 := carve_R2 R o1 o2 lj).
  assert (Hb2 : uE E (rg_base R2) = A + o1 + L) by (unfold R2; eapply base_R2; eassumption).
  assert (Hr2 : rsz E R2 = o2 - o1 - L) by (unfold R2; eapply rsz_R2; eassumption).
  assert (HR2 : rg_ok segs E (ms_mem (restrict H ms)) R2).
  { unfold rg_ok. cbv zeta. fold (uE E (rg_base R2)). rewrite Hb2, Hr2. split; [lia|]. split; [lia|]. split.
    - intros i Hi. cbn [rg_kind R2 carve_R2]. replace (A + o1 + L + i) with (A + (o1 + L + i)) by lia. apply Hpt. lia.
    - intros p v Hp. cbn [rg_cont R2 carve_R2] in Hp. rewrite tget_empty in Hp. discriminate. }
  assert (Hcarve : carve_rgs (s_rgs S) j0 o1 o2 lj = split_rgs (s_rgs S) j0 o1 o2 ++ [R2]) by (unfold carve_rgs; rewrite Hj0; reflexivity).
  assert (Hlen1 : length (split_rgs (s_rgs S) j0 o1 o2) = Datatypes.S (length (s_rgs S))).
  { unfold split_rgs. rewrite Hj0, length_app, length_upd. cbn [length]. lia. }
  assert (Hdisj2 : Forall (fun R' => rg_disj E R' R2) (split_rgs (s_rgs S) j0 o1 o2)).
  { apply Forall_nth'. intros k R' Hk.
    unfold rg_disj. fold (uE E (rg_base R')) (uE E (rg_base R2)). rewrite Hb2, Hr2.
    destruct (nth_split E (s_rgs S) j0 R o1 o2 lj Hj0 HL k R' Hk) as [(-> & ->)|[(Hne & Hko)|(-> & ->)]].
    - rewrite Hb1, Hr1. lia.
    - pose proof (rgs_disj_nth E (s_rgs S) k j0 R' R HD Hne Hko Hj0) as Hdd. unfold rg_disj in Hdd. rewrite HrR in Hdd. unfold uE in *. fold A in Hdd. lia.
    - rewrite Hb3, Hr3. lia. }
  (* [comment removed for export] *)
  assert (HsdC : sden segs E S' (restrict H ms)).
  { apply sden0_sden; [exact Hswf|].
    unfold S'. cbn [with_rgs s_pc s_regs s_rgs s_facts s_resv]. rewrite Hcarve.
    refine (conj Hpc (conj Hsvc (conj Hrsv (conj HR (conj _ (conj _ (conj HF Hfrm))))))).
    - apply Forall_app. split; [exact HG1 | constructor; [exact HR2 | constructor]].
    - apply rgs_disj_snoc; [exact HD1 | exact Hdisj2]. }
  assert (HbR : lwf (s_next S) (rg_base R) = true).
  { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. exact (proj1 (andb_prop _ _ (Hbw R (nth_error_In _ _ Hj0)))). }
  assert (Hnotcp : forall x : word, outside E (s_rgs S) x -> ~ (A + o1 <= bv_unsigned x < A + o1 + L)).
  { intros x Hout Hcp. rewrite outside_nth_iff in Hout. apply (Hout j0 R Hj0). unfold in_rg. rewrite HrR. fold A. lia. }
  constructor.
  - rewrite HH. exact HsdC.
  - change (s_next S') with (s_next S). unfold sm_wf in *. cbn [M' own_add sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own forallb fst snd] in *.
    apply andb_prop in Hwf as [Hw1 Hw2]. rewrite Hw1, Hw2. rewrite andb_true_r, andb_true_l.
    apply andb_true_intro. split; [|exact Hwl]. unfold lwf, laddc in *. cbn [l_t] in *. exact HbR.
  - exact (state_wf_bases _ Hswf).
  - exact Hh.
  - exact Hawf.
  - exact Hanz.
  - exact Hminv.
  - exact Hhoff.
  - exact Hres.
  - exact Hlim.
  - exact Hsp.
  - exact Hspok.
  - exact Hbrk.
  - exact Hsbrk.
  - exact Htid.
  - exact Hmaps.
  - exact Hgsh.
  - exact Hgtop.
  - exact Hivwf.
  - exact Hpd.
  - exact Hmres.
  - exact Hkind.
  - exact Hlzm.
  - exact Hzrsh.
  - exact Hzrm.
  - intros w Hw Hout Hno Hnb. destruct (proj1 (Hiff _) Hout) as [Hout0|Hcp].
    + apply (Hzr w Hw Hout0); [|exact Hnb]. intros Ho'. apply Hno. apply Hop. right. exact Ho'.
    + exfalso. apply Hno. apply Hop. left. pose proof (Hzrsh w Hw) as Hs. unfold in_shadow, SH_LO, SH_HI in Hs.
      apply andb_prop in Hs as [Hsa Hsb]. apply Z.leb_le in Hsa. apply Z.ltb_lt in Hsb.
      rewrite u_small64 in Hcp by (unfold two64; lia). exact Hcp.
  - apply Forall_nth'. intros k R' Hk.
    pose proof (proj1 (Forall_nth' _ _) Hrl j0 R Hj0) as HrlR.
    destruct (nth_carve (s_rgs S) j0 R o1 o2 lj Hj0 k R' Hk) as [(-> & ->)|[(Hne & Hko)|[->| ->]]].
    + apply (rl_ok_sub E model R _ HrlR); rewrite ?Hb1, ?Hr1, ?HrR; fold A; lia.
    + exact (proj1 (Forall_nth' _ _) Hrl k R' Hko).
    + apply (rl_ok_sub E model R _ HrlR); rewrite ?Hb3, ?Hr3, ?HrR; fold A; lia.
    + fold R2. apply (rl_ok_sub E model R _ HrlR); rewrite ?Hb2, ?Hr2, ?HrR; fold A; lia.
  - exact Hvmo.
  - exact Hproc.
  - intros q Hq w Hw. destruct (Hfrz q Hq w Hw) as (Htp & Hout & Hm). split; [exact Htp|]. split; [apply Hiff; left; exact Hout|].
    unfold carve_mem0. destruct (Z.leb (A + o1) (bv_unsigned (Z_to_bv 64 w)) && Z.ltb (bv_unsigned (Z_to_bv 64 w)) (A + o1 + L))%bool eqn:X; [|exact Hm].
    exfalso. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (Hnotcp _ Hout (conj X1 X2)).
  - exact Hrom.
  - intros q Hq w Hw. cbn [sm_own M' own_add In] in Hq. destruct Hq as [<-|Hq].
    + cbn [fst snd] in Hw. rewrite Hhd in Hw. split.
      * rewrite HH. replace w with (A + (w - A)) by lia. apply Hvis. lia.
      * intros _. unfold carve_mem0. rewrite u_small64 by (unfold two64 in *; lia).
        replace (Z.leb (A + o1) w && Z.ltb w (A + o1 + L))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        reflexivity.
    + destruct (Hown q Hq w Hw) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros Hout'. destruct (proj1 (Hiff _) Hout') as [Hout0|Hcp].
      * rewrite (Hm Hout0). unfold carve_mem0.
        destruct (Z.leb (A + o1) (bv_unsigned (Z_to_bv 64 w)) && Z.ltb (bv_unsigned (Z_to_bv 64 w)) (A + o1 + L))%bool eqn:X; [|reflexivity].
        exfalso. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (Hnotcp _ Hout0 (conj X1 X2)).
      * unfold carve_mem0. replace (Z.leb (A + o1) (bv_unsigned (Z_to_bv 64 w)) && Z.ltb (bv_unsigned (Z_to_bv 64 w)) (A + o1 + L))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        reflexivity.
  - exact Hblob.
Qed.
End CarveDen.
(* [comment removed for export] *)
