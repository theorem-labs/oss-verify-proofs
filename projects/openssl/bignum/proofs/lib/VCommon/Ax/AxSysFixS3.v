(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWAcc AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxMeasure AxSysNode AxSysMmap AxGrant AxSysFix AxPostFix.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxFd AxModelRel AxMRFix AxSys2B AxSysFixS.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Ltac flia :=
  repeat match goal with
         | H : context [Z.modulo] |- _ => clear H
         | H : context [Z.div] |- _ => clear H
         end; lia.

Lemma in_replace_nth' (A : list region) (i : nat) (R' X : region) :
  In X (replace_nth A i R') -> X = R' \/ exists k, k <> i /\ nth_error A k = Some X.
Proof.
  revert i. induction A as [|R0 A IH]; intros i H; [destruct i; destruct H|].
  destruct i as [|i]; cbn [replace_nth] in H.
  - destruct H as [<-|H]; [left; reflexivity|]. right. apply In_nth_error in H as [k Hk]. exists (S k). split; [lia | exact Hk].
  - destruct H as [<-|H]; [right; exists 0%nat; split; [lia | reflexivity]|].
    destruct (IH i H) as [E|[k [Hk Hn]]]; [left; exact E | right; exists (S k); split; [lia | exact Hn]].
Qed.

Lemma nth_replace_nth_other (A : list region) (i k : nat) (R' : region) : k <> i -> nth_error (replace_nth A i R') k = nth_error A k.
Proof.
  revert i k. induction A as [|R0 A IH]; intros i k Hne; [destruct i; reflexivity|].
  destruct i as [|i], k as [|k]; cbn [replace_nth nth_error]; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma nth_replace_nth_same (A : list region) (i : nat) (R R' : region) : nth_error A i = Some R -> nth_error (replace_nth A i R') i = Some R'.
Proof.
  revert i. induction A as [|R0 A IH]; intros i H; [destruct i; discriminate|].
  destruct i as [|i]; cbn [replace_nth nth_error] in *; [reflexivity | exact (IH i H)].
Qed.

Lemma regions_ok_shrink (ρ : valuation) (A : list region) (i : nat) (R R' : region) :
  regions_ok ρ A -> nth_error A i = Some R -> region_wf ρ R' ->
  rbase ρ R <= rbase ρ R' -> rbase ρ R' + to_Z (rg_n R') <= rbase ρ R + to_Z (rg_n R) ->
  regions_ok ρ (replace_nth A i R').
Proof.
  revert i. induction A as [|R0 A IH]; intros i Hok Hi Hw Hlo Hhi; [destruct i; discriminate|].
  pose proof (to_Z_bounded (rg_n R')) as Hn'.
  destruct i as [|i]; cbn [nth_error replace_nth regions_ok] in *.
  - injection Hi as <-. destruct Hok as [_ [Hd Hok]]. split; [exact Hw|]. split; [|exact Hok].
    rewrite Forall_forall in *. intros X HX. specialize (Hd X HX). unfold rdisj in *. lia.
  - destruct Hok as [Hw0 [Hd Hok]]. split; [exact Hw0|]. split; [|exact (IH i Hok Hi Hw Hlo Hhi)].
    rewrite Forall_forall in *. intros X HX. destruct (in_replace_nth' A i R' X HX) as [->|[k [_ Hk]]].
    + specialize (Hd R (nth_error_In A i Hi)). unfold rdisj in *. lia.
    + exact (Hd X (nth_error_In A k Hk)).
Qed.

Lemma regions_ok_filter (ρ : valuation) (g : region -> bool) (A : list region) : regions_ok ρ A -> regions_ok ρ (List.filter g A).
Proof.
  induction A as [|R0 A IH]; intros Hok; [exact I|]. destruct Hok as [Hw0 [Hd Hok]]. cbn [List.filter].
  destruct (g R0); [|exact (IH Hok)]. cbn [regions_ok]. split; [exact Hw0|]. split; [|exact (IH Hok)].
  rewrite Forall_forall in *. intros X HX. apply filter_In in HX as [HX _]. exact (Hd X HX).
Qed.

Lemma find_at_spec (ts : terms) (o : w64) (k : rkind) (A : list region) : forall (j0 i : nat) (R : region),
  find_at ts o k A j0 = Some (i, R) ->
  (j0 <= i)%nat /\ nth_error A (i - j0) = Some R /\ rg_ts R = ts /\ rg_bo R = o /\ rg_cells R = IEmpty
  /\ ((rg_kind R = KZero /\ k = KZero) \/ (rg_kind R = KShadow /\ k = KShadow)).
Proof.
  induction A as [|X A IH]; intros j0 i R H; cbn [find_at] in H; [discriminate|].
  destruct (rg_at ts o k X) eqn:E.
  - injection H as <- <-. rewrite Nat.sub_diag. split; [lia|]. split; [reflexivity|].
    unfold rg_at in E. apply andb_prop in E as [E E4]. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply teqb_eq in E1. rewrite w_eqb_spec in E2. apply Z.eqb_eq in E2. apply wZ_inj in E2.
    split; [exact E1|]. split; [exact E2|]. split; [unfold is_empty in E3; destruct (rg_cells X); [reflexivity | discriminate..]|].
    destruct (rg_kind X), k; try discriminate E4; [left | right]; split; reflexivity.
  - destruct (IH (S j0) i R H) as (H1 & H2 & H3). split; [lia|]. split; [|exact H3].
    replace (i - j0)%nat with (S (i - S j0)) by lia. exact H2.
Qed.

Section PostCut.
Variable segs : list Segment.
Variable ρ : valuation.
Variables A A' : list region.
Variables m m' : word -> option byte.
Variables model model' : Model.
Variables a n : Z.

Hypothesis Hm_in : forall x : word, a <= bv_unsigned x < a + n -> m' x = None.
Hypothesis Hm_out : forall x : word, ~ (a <= bv_unsigned x < a + n) -> m' x = m x.
Hypothesis Hhs : hs_ok ρ A m.
Hypothesis Hmode : plain_mode A -> plain_mode A'.
Hypothesis Hcomp : comp_inv segs ρ A model.
Hypothesis Hcov : mem_cov segs model m.
Hypothesis Hna : na_ok segs ρ A model m.

Hypothesis Hsub : forall R', In R' A' -> exists R, In R A /\ is_shadow R' = is_shadow R /\ forall z, in_rg ρ R' z -> in_rg ρ R z.

Hypothesis Hcut_ss : forall z, a <= z < a + n -> ~ in_ss z.
Hypothesis Hcut_segs : forall z, in_segs segs z -> ~ (a <= z < a + n).

Hypothesis Hbg : forall z, in_ss z -> (forall S', In S' A' -> is_shadow S' = true -> ~ in_rg ρ S' z) ->
  (forall S, In S A -> is_shadow S = true -> ~ in_rg ρ S z) \/ m (wz z) = None \/ m (wz z) = Some (Z_to_bv 8 0).

Hypothesis Hpre : forall S', In S' A' -> is_shadow S' = true -> forall z, in_rg ρ S' z -> forall q, preimage z q -> ~ (a <= q < a + n).

Hypothesis Hled_w : forall q, ~ (a <= q < a + n) -> in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps model') q.
Lemma Hled : forall q, ~ (a <= q < a + n) -> in_ledger segs (m_vmmaps model) q -> in_ledger segs (m_vmmaps model') q.
Proof. exact (in_ledger_of_w_out segs _ _ (fun q => ~ (a <= q < a + n)) Hled_w). Qed.
Hypothesis Hna' : forall q, inl (vm_noaccess (m_vmmaps model')) q -> inl (vm_noaccess (m_vmmaps model)) q \/ a <= q < a + n.

Lemma cut_same_ss (z : Z) : in_ss z -> m' (wz z) = m (wz z).
Proof.
  intros Hz. apply Hm_out. rewrite u_wz by (unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hz; lia).
  intros Hr. exact (Hcut_ss z Hr Hz).
Qed.

Theorem hs_ok_cut : hs_ok ρ A' m'.
Proof.
  destruct Hhs as [Hpl|[P1 [P2 [P3 P4]]]]; [left; exact (Hmode Hpl) | right]. split; [|split; [|split]].
  - intros R' HR' Hs z Hz. destruct (Hsub R' HR') as [R [HR [Es Hin]]]. rewrite Es in Hs. exact (P1 R HR Hs z (Hin z Hz)).
  - intros z Hss Hout. rewrite (cut_same_ss z Hss). destruct (Hbg z Hss Hout) as [X|X]; [exact (P2 z Hss X) | exact X].
  - destruct P3 as [X|X]; [left | right]; intros z Hz; rewrite (cut_same_ss z (or_introl Hz)); exact (X z Hz).
  - destruct P4 as [X|X]; [left | right]; intros z Hz; rewrite (cut_same_ss z (or_intror Hz)); exact (X z Hz).
Qed.

Theorem mem_cov_cut : mem_cov segs model' m'.
Proof.
  intros x Hx. destruct (Z_le_gt_dec a (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L2|L2]|].
  - exfalso. apply Hx. apply Hm_in. lia.
  - rewrite Hm_out in Hx by lia. apply Hled_w; [lia | exact (Hcov x Hx)].
  - rewrite Hm_out in Hx by lia. apply Hled_w; [lia | exact (Hcov x Hx)].
Qed.

Theorem comp_inv_cut : comp_inv segs ρ A' model'.
Proof.
  intros S' HS' Hs z Hz. destruct (Hsub S' HS') as [S [HS [Es Hin]]]. rewrite Es in Hs.
  destruct (Hcomp S HS Hs z (Hin z Hz)) as [H1 H2]. split; [exact H1|]. intros q Hq.
  apply Hled; [|exact (H2 q Hq)]. rewrite <- Es in Hs. exact (Hpre S' HS' Hs z Hz q Hq).
Qed.

Theorem na_ok_cut : na_ok segs ρ A' model' m'.
Proof.
  destruct Hna as [N1 [N2 N3]]. split; [|split].
  - intros x Hx Hi. destruct (Z_le_gt_dec a (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L2|L2]|].
    + apply Hx. apply Hm_in. lia.
    + rewrite Hm_out in Hx by lia. destruct (Hna' _ Hi) as [X|X]; [exact (N1 x Hx X) | lia].
    + rewrite Hm_out in Hx by lia. destruct (Hna' _ Hi) as [X|X]; [exact (N1 x Hx X) | lia].
  - intros z Hz Hi. destruct (Hna' _ Hi) as [X|X]; [exact (N2 z Hz X) | exact (Hcut_segs z Hz X)].
  - intros S' HS' Hs z Hz q Hq Hi. destruct (Hsub S' HS') as [S [HS [Es Hin]]].
    destruct (Hna' _ Hi) as [X|X]; [|exact (Hpre S' HS' Hs z Hz q Hq X)].
    rewrite Es in Hs. exact (N3 S HS Hs z (Hin z Hz) q Hq X).
Qed.

End PostCut.

Section Trim.
Variable segs : list Segment.
Variable ρ : valuation.
Variable A : list region.
Variables m m' : word -> option byte.
Variable model : Model.
Variables a nZ nR : Z.
Variables R C R' C' : region.
Variables i j : nat.

Hypothesis HRM : RMem segs ρ A m.
Hypothesis Hhs : hs_ok ρ A m.
Hypothesis Hcomp : comp_inv segs ρ A model.
Hypothesis Hi : nth_error A i = Some R.
Hypothesis Hj : nth_error A j = Some C.
Hypothesis HRk : rg_kind R = KZero.
Hypothesis HRc : rg_cells R = IEmpty.
Hypothesis HRb : rbase ρ R = a.
Hypothesis HRn : to_Z (rg_n R) = nR.
Hypothesis HCk : rg_kind C = KShadow.
Hypothesis HCc : rg_cells C = IEmpty.
Hypothesis HCb : rbase ρ C = a / 8 + sh_off.
Hypothesis HCn : to_Z (rg_n C) = nR / 8.
Hypothesis HR'k : rg_kind R' = KZero.
Hypothesis HR'c : rg_cells R' = IEmpty.
Hypothesis HR'b : rbase ρ R' = a + nZ.
Hypothesis HR'n : to_Z (rg_n R') = nR - nZ.
Hypothesis HR'wf : region_wf ρ R'.
Hypothesis HC'k : rg_kind C' = KShadow.
Hypothesis HC'c : rg_cells C' = IEmpty.
Hypothesis HC'b : rbase ρ C' = (a + nZ) / 8 + sh_off.
Hypothesis HC'n : to_Z (rg_n C') = (nR - nZ) / 8.
Hypothesis HC'wf : region_wf ρ C'.
Hypothesis Ha8 : a mod 8 = 0.
Hypothesis HnZ8 : nZ mod 8 = 0.
Hypothesis HnR8 : nR mod 8 = 0.
Hypothesis Ha0 : 0 <= a.
Hypothesis HnZ : 0 < nZ < nR.
Hypothesis Hm_in : forall x : word, a <= bv_unsigned x < a + nZ -> m' x = None.
Hypothesis Hm_out : forall x : word, ~ (a <= bv_unsigned x < a + nZ) -> m' x = m x.

Let A' := replace_nth (replace_nth A i R') j C'.

Lemma trim_ij : i <> j.
Proof. intros E. subst j. rewrite Hi in Hj. injection Hj as E. subst C. rewrite HRk in HCk. discriminate HCk. Qed.

Lemma trim_div : a = 8 * (a / 8) /\ nZ = 8 * (nZ / 8) /\ nR = 8 * (nR / 8).
Proof.
  pose proof (Z.div_mod a 8 ltac:(lia)) as D1. pose proof (Z.div_mod nZ 8 ltac:(lia)) as D2. pose proof (Z.div_mod nR 8 ltac:(lia)) as D3.
  rewrite Ha8 in D1. rewrite HnZ8 in D2. rewrite HnR8 in D3. lia.
Qed.

Lemma trim_div2 : (a + nZ) / 8 = a / 8 + nZ / 8 /\ (nR - nZ) / 8 = nR / 8 - nZ / 8.
Proof.
  destruct trim_div as (D1 & D2 & D3). split.
  - rewrite D1 at 1. rewrite D2 at 1. replace (8 * (a / 8) + 8 * (nZ / 8)) with ((a / 8 + nZ / 8) * 8) by lia. apply Z.div_mul. lia.
  - rewrite D3 at 1. rewrite D2 at 1. replace (8 * (nR / 8) - 8 * (nZ / 8)) with ((nR / 8 - nZ / 8) * 8) by lia. apply Z.div_mul. lia.
Qed.

Lemma trim_R_wf : region_wf ρ R.
Proof. destruct HRM as [Hok _]. exact (regions_ok_nth ρ A i R Hok Hi). Qed.

Lemma trim_C_wf : region_wf ρ C.
Proof. destruct HRM as [Hok _]. exact (regions_ok_nth ρ A j C Hok Hj). Qed.

Lemma trim_old : hs_old ρ A m.
Proof. apply (hs_old_of_sh ρ A m C (nth_error_In A j Hj)); [unfold is_shadow; rewrite HCk; reflexivity | exact Hhs]. Qed.

Lemma trim_cut_ss (z : Z) : a <= z < a + nZ -> ~ in_ss z.
Proof.
  intros Hz. destruct trim_old as [P1 _]. apply (P1 R (nth_error_In A i Hi)); [unfold is_shadow; rewrite HRk; reflexivity|].
  unfold in_rg. rewrite HRb, HRn. lia.
Qed.

Lemma trim_C_ss (z : Z) : in_rg ρ C z -> in_ss z.
Proof. intros Hz. exact (proj1 (Hcomp C (nth_error_In A j Hj) ltac:(unfold is_shadow; rewrite HCk; reflexivity) z Hz)). Qed.

Lemma trim_ok : regions_ok ρ A'.
Proof.
  destruct HRM as [Hok _]. destruct trim_div2 as [E1 E2]. destruct trim_div as (D1 & D2 & D3).
  unfold A'. apply (regions_ok_shrink ρ _ j C C').
  - apply (regions_ok_shrink ρ A i R R' Hok Hi HR'wf); rewrite HR'b, HRb; [lia | rewrite HR'n, HRn; lia].
  - rewrite (nth_replace_nth_other A i j R' (fun E => trim_ij (eq_sym E))). exact Hj.
  - exact HC'wf.
  - rewrite HC'b, HCb, E1. lia.
  - rewrite HC'b, HCb, HC'n, HCn, E1, E2. lia.
Qed.

Lemma trim_in (X : region) : In X A' -> X = C' \/ X = R' \/ exists k, k <> i /\ k <> j /\ nth_error A k = Some X.
Proof.
  intros HX. unfold A' in HX. destruct (in_replace_nth' _ j C' X HX) as [->|[k [Hk Hn]]]; [left; reflexivity|]. right.
  destruct (Nat.eq_dec k i) as [->|Hki].
  - left. rewrite (nth_replace_nth_same A i R R' Hi) in Hn. injection Hn as <-. reflexivity.
  - right. exists k. rewrite (nth_replace_nth_other A i k R' Hki) in Hn. repeat split; assumption.
Qed.

Lemma trim_old_in (k : nat) (X : region) : k <> i -> k <> j -> nth_error A k = Some X -> In X A'.
Proof.
  intros Hki Hkj Hk. unfold A'. apply (nth_error_In _ k). rewrite (nth_replace_nth_other _ j k C' Hkj), (nth_replace_nth_other A i k R' Hki). exact Hk.
Qed.

Lemma trim_old_frame (k : nat) (X : region) : k <> i -> nth_error A k = Some X -> forall z, in_rg ρ X z -> ~ (a <= z < a + nZ).
Proof.
  intros Hki Hk z Hz Hr. destruct HRM as [Hok _]. pose proof (regions_ok_disj ρ A k i X R Hok Hk Hi Hki) as D.
  unfold rdisj in D. unfold in_rg in Hz. rewrite HRb, HRn in D. lia.
Qed.

Lemma trim_RRegion : Forall (RRegion segs ρ m') A'.
Proof.
  apply Forall_forall. intros X HX. destruct HRM as [Hok HRR]. pose proof trim_R_wf as WR. pose proof trim_C_wf as WC.
  destruct trim_div2 as [E1 E2]. destruct trim_div as (D1 & D2 & D3).
  destruct (trim_in X HX) as [->|[->|[k (Hki & Hkj & Hk)]]].
  -
    rewrite RRegion_ne by (unfold is_entry; rewrite HC'k; reflexivity). intros y Hy. pose proof (to_Z_bounded y) as Hyb.
    rewrite HC'n in Hy. rewrite HC'b.
    pose proof (zz_region_bytes segs ρ m C (proj1 (Forall_forall _ _) HRR C (nth_error_In A j Hj)) (or_intror HCk) HCc WC
                  (nZ / 8 + to_Z y) ltac:(rewrite HCn; lia)) as [Z1 Z2].
    rewrite HCb in Z1, Z2. replace (a / 8 + sh_off + (nZ / 8 + to_Z y)) with ((a + nZ) / 8 + sh_off + to_Z y) in Z1, Z2 by lia.
    assert (Hss : in_ss ((a + nZ) / 8 + sh_off + to_Z y)) by (apply trim_C_ss; unfold in_rg; rewrite HCb, HCn; lia).
    assert (Em : m' (wz ((a + nZ) / 8 + sh_off + to_Z y)) = m (wz ((a + nZ) / 8 + sh_off + to_Z y))).
    { apply Hm_out. rewrite u_wz by (unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hss; lia). intros Hr. exact (trim_cut_ss _ Hr Hss). }
    split.
    + exists (Z_to_bv 8 0). split; [unfold rv in *; rewrite Em; exact Z1|]. rewrite (rbyte_zz segs C' y (or_intror HC'k) HC'c). reflexivity.
    + intros _. unfold wview in *. rewrite Em. exact Z2.
  -
    rewrite RRegion_ne by (unfold is_entry; rewrite HR'k; reflexivity). intros y Hy. pose proof (to_Z_bounded y) as Hyb.
    rewrite HR'n in Hy. rewrite HR'b.
    pose proof (zz_region_bytes segs ρ m R (proj1 (Forall_forall _ _) HRR R (nth_error_In A i Hi)) (or_introl HRk) HRc WR
                  (nZ + to_Z y) ltac:(rewrite HRn; lia)) as [Z1 Z2].
    rewrite HRb in Z1, Z2. replace (a + (nZ + to_Z y)) with (a + nZ + to_Z y) in Z1, Z2 by lia.
    assert (Em : m' (wz (a + nZ + to_Z y)) = m (wz (a + nZ + to_Z y))).
    { apply Hm_out. destruct WR as (W1 & _). rewrite HRb, HRn in W1. rewrite u_wz by (unfold FastWord.two64 in W1; lia). lia. }
    split.
    + exists (Z_to_bv 8 0). split; [unfold rv in *; rewrite Em; exact Z1|]. rewrite (rbyte_zz segs R' y (or_introl HR'k) HR'c). reflexivity.
    + intros _. unfold wview in *. rewrite Em. exact Z2.
  -
    pose proof (regions_ok_nth ρ A k X Hok Hk) as WX.
    apply (RRegion_mframe segs ρ m m' X WX); [|exact (proj1 (Forall_forall _ _) HRR X (nth_error_In A k Hk))].
    intros z Hz. apply Hm_out. destruct WX as (W1 & _). pose proof (smod_range ρ (rg_ts X) (rg_bo X)) as Hb. fold (rbase ρ X) in Hb.
    rewrite u_wz by (unfold FastWord.two64 in *; lia). exact (trim_old_frame k X Hki Hk z Hz).
Qed.

Theorem RMem_trim : RMem segs ρ A' m'.
Proof. split; [exact trim_ok | exact trim_RRegion]. Qed.

Lemma trim_sub : forall X, In X A' -> exists Y, In Y A /\ is_shadow X = is_shadow Y /\ forall z, in_rg ρ X z -> in_rg ρ Y z.
Proof.
  intros X HX. destruct trim_div2 as [E1 E2]. destruct trim_div as (D1 & D2 & D3).
  destruct (trim_in X HX) as [->|[->|[k (Hki & Hkj & Hk)]]].
  - exists C. split; [exact (nth_error_In A j Hj)|]. split; [unfold is_shadow; rewrite HC'k, HCk; reflexivity|].
    intros z. unfold in_rg. rewrite HC'b, HC'n, HCb, HCn, E1, E2. lia.
  - exists R. split; [exact (nth_error_In A i Hi)|]. split; [unfold is_shadow; rewrite HR'k, HRk; reflexivity|].
    intros z. unfold in_rg. rewrite HR'b, HR'n, HRb, HRn. lia.
  - exists X. split; [exact (nth_error_In A k Hk)|]. split; [reflexivity | intros z Hz; exact Hz].
Qed.

Lemma trim_bg : forall z, in_ss z -> (forall S', In S' A' -> is_shadow S' = true -> ~ in_rg ρ S' z) ->
  (forall S, In S A -> is_shadow S = true -> ~ in_rg ρ S z) \/ m (wz z) = None \/ m (wz z) = Some (Z_to_bv 8 0).
Proof.
  intros z Hss Hout. destruct HRM as [Hok HRR]. pose proof trim_C_wf as WC.
  destruct (Z_le_gt_dec (rbase ρ C) z) as [L1|L1]; [destruct (Z_lt_le_dec z (rbase ρ C + to_Z (rg_n C))) as [L2|L2]|].
  - right. pose proof (zz_region_bytes segs ρ m C (proj1 (Forall_forall _ _) HRR C (nth_error_In A j Hj)) (or_intror HCk) HCc WC
                         (z - rbase ρ C) ltac:(lia)) as [Z1 _].
    replace (rbase ρ C + (z - rbase ρ C)) with z in Z1 by lia. unfold rv in Z1. destruct (m (wz z)) as [b|]; [right; exact Z1 | left; reflexivity].
  - left. intros S HS Hs Hz. apply In_nth_error in HS as [k Hk]. destruct (Nat.eq_dec k j) as [->|Hkj].
    + rewrite Hj in Hk. injection Hk as <-. unfold in_rg in Hz. lia.
    + assert (Hki : k <> i) by (intros ->; rewrite Hi in Hk; injection Hk as <-; unfold is_shadow in Hs; rewrite HRk in Hs; discriminate Hs).
      exact (Hout S (trim_old_in k S Hki Hkj Hk) Hs Hz).
  - left. intros S HS Hs Hz. apply In_nth_error in HS as [k Hk]. destruct (Nat.eq_dec k j) as [->|Hkj].
    + rewrite Hj in Hk. injection Hk as <-. unfold in_rg in Hz. lia.
    + assert (Hki : k <> i) by (intros ->; rewrite Hi in Hk; injection Hk as <-; unfold is_shadow in Hs; rewrite HRk in Hs; discriminate Hs).
      exact (Hout S (trim_old_in k S Hki Hkj Hk) Hs Hz).
Qed.

Lemma trim_pre : forall S', In S' A' -> is_shadow S' = true -> forall z, in_rg ρ S' z -> forall q, preimage z q -> ~ (a <= q < a + nZ).
Proof.
  intros S' HS' Hs z Hz q Hq. destruct trim_div2 as [E1 E2]. destruct trim_div as (D1 & D2 & D3). unfold preimage in Hq.
  destruct (trim_in S' HS') as [->|[->|[k (Hki & Hkj & Hk)]]].
  - unfold in_rg in Hz. rewrite HC'b, HC'n, E1 in Hz. lia.
  - unfold is_shadow in Hs. rewrite HR'k in Hs. discriminate Hs.
  - destruct HRM as [Hok _]. pose proof (regions_ok_disj ρ A k j S' C Hok Hk Hj Hkj) as D. unfold rdisj in D. unfold in_rg in Hz.
    rewrite HCb, HCn in D. lia.
Qed.

End Trim.

Section Main.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Lemma mod4096_8 (z : Z) : z mod 4096 = 0 -> z mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod z 4096 ltac:(lia)) as D. rewrite H in D. rewrite D, Z.add_0_r.
  replace (4096 * (z / 4096)) with ((512 * (z / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma comp_end_47 (a nR : Z) : a mod 8 = 0 -> nR mod 8 = 0 -> 0 <= a -> 8 <= nR -> in_ss (a / 8 + sh_off + nR / 8 - 1) -> a + nR <= 2 ^ 47.
Proof.
  intros Ha Hn Ha0 Hn8 Hss. pose proof (Z.div_mod nR 8 ltac:(lia)) as D. rewrite Hn in D. pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Ha in Da.
  unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, sh_off in Hss. lia.
Qed.

Theorem sys_fix_none_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 222 -> sys_fix_none A = Some l ->
  (forall B, In B l -> forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17 Hsys HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_fix_none in Hsys.
  destruct (fix_shape A 0) as [[nZ lz]|] eqn:Esh; [|discriminate Hsys].
  destruct (xform (a_facts A) (aget (a_regs A) 10%uint63)) as [f|] eqn:Ef; [|discriminate Hsys].
  destruct (find_ent (a_facts A) f nZ (am_maps (a_model A))) as [e0|] eqn:Ee; [|discriminate Hsys].
  destruct (find_at (snd f) (wofZ (fst f)) KZero (a_mem A) 0) as [[i R]|] eqn:EfR; [|discriminate Hsys].
  destruct (find_at (tdiv8 (snd f)) (wofZ (wS (wofZ (fst f)) / 8 + sh_off)) KShadow (a_mem A) 0) as [[j C]|] eqn:EfC; [|discriminate Hsys].
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate Hsys] end.
  injection Hsys as <-.
  apply andb_prop in Ec as [Ec Kfull]. apply andb_prop in Ec as [Ec Kbig]. apply negb_true_iff in Kfull.
  apply andb_prop in Ec as [Ec Hpos]. apply andb_prop in Ec as [Ec Q8]. apply andb_prop in Ec as [Ec Q7].
  apply andb_prop in Ec as [Ec Q6]. apply andb_prop in Ec as [Ec Q5]. apply andb_prop in Ec as [Ec Q4].
  apply andb_prop in Ec as [Ec Q3]. apply andb_prop in Ec as [Ec Q2b]. apply andb_prop in Ec as [Q1 Q2].
  apply negb_true_iff in Q1. apply Z.ltb_lt in Q3. apply Z.ltb_lt in Q4. apply Z.eqb_eq in Q5. apply Z.eqb_eq in Q6.
  apply Z.leb_le in Q7. apply Z.ltb_lt in Q8.
  destruct (fix_shape_spec A 0 nZ lz Esh) as (len & flags & L11 & L12 & L13 & L15 & Hlen & EnZ & Hfl & Elz).
  subst nZ. set (nZ := page_round_up_Z len) in *.
  pose proof HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 [H10 H10'] H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 222 H4 eq_refl H17) as R17.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len H4 eq_refl L11) as R11.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 12) 12%uint63 0 H4 eq_refl L12) as R12.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 13) 13%uint63 flags H4 eq_refl L13) as R13.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 15) 15%uint63 0 H4 eq_refl L15) as R15.
  pose proof (xform_sound ρ _ _ (rg ms (Z_to_bv 5 10)) f H11 (H4 (Z_to_bv 5 10)) Ef) as R10.
  destruct (find_ent_spec _ f nZ _ e0 Ee) as [He0 Hhas]. destruct (ent_has_sound ρ _ f nZ e0 H11 Hhas) as [Hlo Hhi].
  destruct (page_round_up_bounds len ltac:(flia)) as [Hb1 Hb2]. fold nZ in Hb1, Hb2.
  pose proof (lin_al_sound ρ 4096 f ltac:(flia) Q2) as Hal.
  pose proof (MR_ent segs fs0 ρ _ model e0 H8 He0) as (K1 & K2 & K3).
  pose proof (rng_top segs fs0 ρ _ model H8 e0 He0 f nZ Hhi) as Htop.
  destruct (eb_above_sound ρ _ _ _ H11 Q2b) as [Hat _]. rewrite <- (mr_atop segs fs0 ρ _ model H8) in Hat.
  set (a := leval ρ f) in *.

  pose proof (gate_of_MR segs fs0 ρ _ model H8 e0 He0 f len Hlen Hlo Hhi Hal (rg ms (Z_to_bv 5 10)) (rg ms (Z_to_bv 5 11)) R10 R11) as G.
  pose proof (fix_none_shape_lit (rg ms (Z_to_bv 5 12)) (rg ms (Z_to_bv 5 13)) (rg ms (Z_to_bv 5 15)) R12 ltac:(rewrite R13; exact Hfl) R15) as S.
  pose proof (gate_addr ρ f (rg ms (Z_to_bv 5 10)) R10) as Eaddr. fold a in Eaddr.
  pose proof (gate_fix_n len (rg ms (Z_to_bv 5 11)) R11) as En. fold nZ in En.
  assert (HnZ0 : 0 < nZ) by flia.
  assert (HnZ4 : 4096 <= nZ) by (clear - HnZ0 Hb2; lia).
  pose proof (rng_addr segs fs0 ρ _ model H8 e0 He0 f nZ HnZ0 Hlo Hhi) as Wa. fold a in Wa.
  pose proof (rng_n segs fs0 ρ _ model H8 e0 He0 f nZ HnZ0 Hlo Hhi) as Wn.
  set (addr := rg ms (Z_to_bv 5 10)) in *. set (flagsw := rg ms (Z_to_bv 5 13)) in *.
  set (m' := fix_none_model flagsw (Z_to_bv 64 a) (Z_to_bv 64 nZ) model).
  assert (Hused : vm_backing_used m' <= a_budget A).
  { pose proof (used_fix_none model flagsw (Z_to_bv 64 a) (Z_to_bv 64 nZ) (MR_maps_nowrap segs fs0 ρ _ model H8) (mr_na segs fs0 ρ _ model H8)
                  (MR_lazy_nowrap segs fs0 ρ _ model H8)) as X. fold m' in X.
    assert (Hrange : bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 nZ) <= AxAcct.two64)
      by (rewrite Wa, Wn; pose proof (alloc_top_lt (m_vmmaps model)) as Y; unfold two_pow_64 in Y; unfold AxAcct.two64; flia).
    specialize (X Hrange). flia. }
  assert (Hlim : vm_limit (m_vmmaps m') = LIM) by (unfold m'; rewrite fix_none_vmmaps; exact H10').

  destruct (find_at_spec _ _ _ _ 0%nat i R EfR) as (_ & Hi & Rts & Rbo & Rc & [[Rk _]|[_ X]]); [|discriminate X]. rewrite Nat.sub_0_r in Hi.
  destruct (find_at_spec _ _ _ _ 0%nat j C EfC) as (_ & Hj & Cts & Cbo & Cc & [[_ X]|[Ck _]]); [discriminate X|]. rewrite Nat.sub_0_r in Hj.
  set (nR := to_Z (rg_n R)) in *.
  assert (HnZr : 0 < nZ < nR) by flia.
  assert (Ha0 : 0 <= a) by flia.
  assert (Hc : 0 <= fst f < 9223372036854775808) by flia.
  assert (Hv : 0 <= leval ρ f < AxAcct.two64) by (fold a; unfold AxAcct.two64; flia).
  assert (Rb : rbase ρ R = a) by (unfold rbase; rewrite Rts, Rbo; exact (smod_form ρ f Hc Hv)).
  assert (Ha8 : a mod 8 = 0) by (apply mod4096_8; exact Hal). assert (HnZ8 : nZ mod 8 = 0) by (apply mod4096_8; exact Hb2).
  assert (Hw8 : wS (wofZ (fst f)) mod 8 = 0).
  { rewrite (wS_wofZ_small (fst f) Hc). apply mod4096_8. unfold lin_al in Q2. apply andb_prop in Q2 as [Q2 _]. apply Z.eqb_eq in Q2. exact Q2. }
  assert (Hsum : teval ρ (snd f) + wS (wofZ (fst f)) = a) by (rewrite (wS_wofZ_small (fst f) Hc); unfold a, leval; lia).
  assert (Ha47 : a + 0 <= 2 ^ 47) by flia.
  destruct (comp_rg_wf ρ (snd f) (wofZ (fst f)) 0 a (lin_al_tdiv8 f Q2) Hw8 Hsum Ha0 Ha47 (Z.le_refl 0)) as (Cb0 & _ & _).
  assert (Cb : rbase ρ C = a / 8 + sh_off) by (rewrite <- Cb0; unfold rbase, comp_rg; cbn [rg_ts rg_bo]; rewrite Cts, Cbo; reflexivity).

  assert (H47 : a + nR <= 2 ^ 47).
  { apply (comp_end_47 a nR Ha8 Q5 Ha0 ltac:(flia)).
    assert (Hin : in_rg ρ C (a / 8 + sh_off + nR / 8 - 1)).
    { unfold in_rg. rewrite Cb, Q6. assert (1 <= nR / 8) by (apply Z.div_le_lower_bound; flia). clear - H. lia. }
    exact (proj1 (H14 C (nth_error_In _ j Hj) ltac:(unfold is_shadow; rewrite Ck; reflexivity) _ Hin)). }
  pose proof (regions_ok_nth ρ _ i R (proj1 H7) Hi) as (WR1 & _). rewrite Rb in WR1. fold nR in WR1.

  set (f' := (fst f + nZ, snd f) : lin).
  assert (Hc' : 0 <= fst f' < 9223372036854775808) by (cbn [fst f']; flia).
  assert (Ef' : leval ρ f' = a + nZ) by (unfold leval, f', a; cbn [fst snd]; unfold leval; flia).
  assert (Hv' : 0 <= leval ρ f' < AxAcct.two64) by (rewrite Ef'; unfold AxAcct.two64, FastWord.two64 in *; flia).
  assert (Hr1 : 0 <= nR - nZ < 2 ^ 47) by flia. assert (Hr2 : a + nZ + (nR - nZ) <= FastWord.two64) by (unfold FastWord.two64 in *; flia).
  destruct (zero_rg_wf ρ (snd f) (wofZ (fst f + nZ)) (nR - nZ) (a + nZ)
              ltac:(rewrite <- Ef'; exact (smod_form ρ f' Hc' Hv')) Hr1 Hr2) as (Z1 & Z2 & Z3).
  assert (Hw8' : wS (wofZ (fst f + nZ)) mod 8 = 0).
  { rewrite (wS_wofZ_small (fst f + nZ) Hc'). apply mod4096_8. unfold lin_al in Q2. apply andb_prop in Q2 as [Q2 _]. apply Z.eqb_eq in Q2.
    rewrite Z.add_mod, Q2, Hb2 by lia. reflexivity. }
  assert (Hsum' : teval ρ (snd f) + wS (wofZ (fst f + nZ)) = a + nZ) by (rewrite (wS_wofZ_small (fst f + nZ) Hc'); unfold a, leval; flia).
  assert (Hr3 : 0 <= a + nZ) by flia. assert (Hr4 : a + nZ + (nR - nZ) <= 2 ^ 47) by flia. assert (Hr5 : 0 <= nR - nZ) by flia.
  destruct (comp_rg_wf ρ (snd f) (wofZ (fst f + nZ)) (nR - nZ) (a + nZ) (lin_al_tdiv8 f Q2) Hw8' Hsum' Hr3 Hr4 Hr5)
    as (C1 & C2 & C3).
  set (R' := zero_rg (snd f) (wofZ (fst f + nZ)) (nR - nZ)) in *. set (C' := comp_rg (snd f) (wofZ (fst f + nZ)) (nR - nZ)) in *.
  set (mem' := apply_unmaps (ms_mem ms) [(Z_to_bv 64 a, Z_to_bv 64 nZ)]).
  assert (Hin : forall x : word, a <= bv_unsigned x < a + nZ -> mem' x = None) by (intros x Hx; unfold mem'; apply unmaps_in; rewrite Wa, Wn; exact Hx).
  assert (Hout : forall x : word, ~ (a <= bv_unsigned x < a + nZ) -> mem' x = ms_mem ms x) by (intros x Hx; unfold mem'; apply unmaps_out; rewrite Wa, Wn; exact Hx).

  apply (rzc_latch segs cfg ms model w (KT ρ o) H9 H3 Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o) H9 eq_refl).
  - rewrite (check_syscall_222 segs (latch ms) _ _ model R17).
    exact (chk_fix_none_modeled model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) flagsw (rg ms (Z_to_bv 5 14)) (rg ms (Z_to_bv 5 15)) S G _).
  - intros eff m1 evs Hc0. rewrite (check_syscall_222 segs (latch ms) _ _ model R17) in Hc0.
    destruct (chk_fix_none_halted model addr _ _ flagsw _ _ eff m1 evs S G Hc0) as [E1 E2]. split; [exact E1 | rewrite E2; exact H9].
  - exists (mkEffectU addr [] [] [(addr, fix_n (rg ms (Z_to_bv 5 11)))] [] []), (fix_none_model flagsw addr (fix_n (rg ms (Z_to_bv 5 11))) model). split.
    + rewrite (check_syscall_222 segs (latch ms) _ _ model R17).
      exact (chk_fix_none_grant model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) flagsw (rg ms (Z_to_bv 5 14)) (rg ms (Z_to_bv 5 15)) S G).
    + rewrite (refusal_b_222 segs (latch ms) _ model _ R17). exact (fix_addr_not_errno model addr _ G).
  - intros eff m1 Hc0 Hnr. rewrite (check_syscall_222 segs (latch ms) _ _ model R17) in Hc0.
    destruct (chk_fix_none model addr _ _ flagsw _ _ S G eff m1 [] Hc0) as [Hr|(-> & -> & _)].
    + exfalso. specialize (Hnr (family_off_alloc segs cfg (latch ms) _ Hcfg2 ltac:(rewrite R17; cbn; tauto) ltac:(rewrite R17; discriminate))).
      rewrite (refusal_b_222 segs (latch ms) _ model _ R17) in Hnr.
      change (ret_in_errnos [ENOMEM] (eff_ret eff)) with (errno_ret_in mmap_errnos (eff_ret eff)) in Hnr. congruence.
    + rewrite En, Eaddr. fold m'. exists m'. split; [exact (materialize_nil m')|]. rewrite adv_unmaps. fold mem'.
      set (B := with_model A (npc A) (aset (a_regs A) reg_a0 (aget (a_regs A) reg_a0))
                  (replace_nth (replace_nth (a_mem A) i R') j C') (a_facts A) (a_model A) (a_budget A)).
      apply (HS B (or_introl eq_refl) ρ); [|exact Ho].
      assert (Evm : m_vmmaps m' = mkVmMapsFull (vm_reserved (m_vmmaps model)) (vm_maps (m_vmmaps model))
                      ((Z_to_bv 64 a, Z_to_bv 64 nZ) :: maps_subtract (vm_noaccess (m_vmmaps model)) a (a + nZ))
                      (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model))
                      (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model)))
        by (unfold m'; rewrite fix_none_vmmaps, Wa, Wn; reflexivity).

      assert (T_ss : forall z, a <= z < a + nZ -> ~ in_ss z).
      { eapply trim_cut_ss with (nR := nR) (R := R) (C := C); first [eassumption | reflexivity]. }
      assert (Hmode : plain_mode (a_mem A) -> plain_mode (replace_nth (replace_nth (a_mem A) i R') j C')).
      { intros [_ Hno]. exfalso. pose proof (Hno C (nth_error_In _ j Hj)) as X. unfold is_shadow in X. rewrite Ck in X. discriminate X. }
      assert (Hsegs : forall z, in_segs segs z -> ~ (a <= z < a + nZ)).
      { intros z Hz Hr. destruct (in_segs_reserved segs Hlow z Hz) as [q [Hq Hzq]]. rewrite <- (mr_res segs fs0 ρ _ model H8) in Hq.
        pose proof (rng_res segs fs0 ρ _ model H8 e0 He0 f nZ Hlo Hhi q Hq) as D. unfold iv_disj in D. fold a in D. flia. }
      assert (Hled : forall q, ~ (a <= q < a + nZ) -> in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps m') q)
        by (intros q _ Hq; unfold in_ledger_w in *; rewrite Evm; exact Hq).
      assert (Hna' : forall q, inl (vm_noaccess (m_vmmaps m')) q -> inl (vm_noaccess (m_vmmaps model)) q \/ a <= q < a + nZ).
      { intros q Hq. rewrite Evm in Hq. cbn [vm_noaccess] in Hq. apply inl_cons in Hq as [Hq|Hq].
        - right. rewrite bas_mk, bsz_mk, Wa, Wn in Hq. exact Hq.
        - left. apply (inl_subtract1 _ _ _ q (mr_na segs fs0 ρ _ model H8)) in Hq as [Hq _]. exact Hq. }
      assert (HRM' : RMem segs ρ (replace_nth (replace_nth (a_mem A) i R') j C') mem').
      { eapply RMem_trim with (m := ms_mem ms) (model := model) (a := a) (nZ := nZ) (nR := nR) (R := R) (C := C); first [eassumption | reflexivity]. }
      assert (Hsub : forall X, In X (replace_nth (replace_nth (a_mem A) i R') j C') ->
                exists Y, In Y (a_mem A) /\ is_shadow X = is_shadow Y /\ forall z, in_rg ρ X z -> in_rg ρ Y z).
      { eapply trim_sub with (a := a) (nZ := nZ) (nR := nR) (R := R) (C := C); first [eassumption | reflexivity]. }
      assert (Hbg : forall z, in_ss z -> (forall S', In S' (replace_nth (replace_nth (a_mem A) i R') j C') -> is_shadow S' = true -> ~ in_rg ρ S' z) ->
                (forall S, In S (a_mem A) -> is_shadow S = true -> ~ in_rg ρ S z) \/ ms_mem ms (wz z) = None \/ ms_mem ms (wz z) = Some (Z_to_bv 8 0)).
      { eapply trim_bg with (R := R) (C := C); first [eassumption | reflexivity]. }
      assert (Hpre : forall S', In S' (replace_nth (replace_nth (a_mem A) i R') j C') -> is_shadow S' = true ->
                forall z, in_rg ρ S' z -> forall q, preimage z q -> ~ (a <= q < a + nZ)).
      { eapply trim_pre with (m := ms_mem ms) (nR := nR) (R := R) (C := C); first [eassumption | reflexivity]. }
      apply (R_sys_post_B segs fs0 LIM ρ A B ms model m' _ (aget (a_regs A) reg_a0) _ HR); try reflexivity; try assumption.
      * rewrite <- Eaddr. exact (H4 (Z_to_bv 5 10)).
      * apply (MR_none segs fs0 ρ _ model H8 e0 He0 f nZ HnZ0 Hlo Hhi (conj Hal ltac:(unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)) flagsw Q1); [|exact Kfull].
        intros Hnrk. rewrite (fix_nores flagsw flags R13 Hfl), <- Elz in Hnrk. rewrite Hnrk in Kbig. cbn in Kbig. apply Z.leb_le in Kbig. exact Kbig.
      * unfold m'. rewrite fix_none_halted. exact H9.
      * eapply hs_ok_cut with (m := ms_mem ms) (A := a_mem A) (a := a) (n := nZ); eassumption.
      * eapply mem_cov_cut with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
      * eapply comp_inv_cut with (A := a_mem A) (model := model) (a := a) (n := nZ); eassumption.
      * eapply na_ok_cut with (A := a_mem A) (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
Qed.

End Main.
