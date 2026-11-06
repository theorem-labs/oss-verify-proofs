(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU MngMeas MngWk MngRz2 MngBudM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMeas OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRz2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngBudM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma u_w64' : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Ha. Qed.

(* [comment removed for export] *)
Fixpoint RL (L : layout) (rs : list region) (k : nat) : list (word * word) :=
  match rs with
  | [] => []
  | rg :: rs' => if rk_meta rg then (w64 (ly_reg L k), w64 (rg_len rg)) :: RL L rs' (S k) else RL L rs' (S k)
  end.

Lemma RL_In : forall L rs k e, In e (RL L rs k) ->
  exists j rg, nth_error rs j = Some rg /\ rk_meta rg = true /\ e = (w64 (ly_reg L (k + j)), w64 (rg_len rg)).
Proof.
  intros L rs. induction rs as [|rg rs IH]; intros k e H; [destruct H|]. cbn [RL] in H.
  destruct (rk_meta rg) eqn:Hk.
  - destruct H as [<-|H].
    + exists 0%nat, rg. rewrite Nat.add_0_r. auto.
    + destruct (IH (S k) e H) as (j & rg' & H1 & H2 & H3). exists (S j), rg'. rewrite <- Nat.add_succ_comm. auto.
  - destruct (IH (S k) e H) as (j & rg' & H1 & H2 & H3). exists (S j), rg'. rewrite <- Nat.add_succ_comm. auto.
Qed.

Section Fit.
Variables (HTOP : Z) (L : layout) (rs : list region).
Hypothesis HTB : HTOP <= 2 ^ 47.
(* [comment removed for export] *)
Hypothesis GEO : forall j rg, nth_error rs j = Some rg -> rk_meta rg = true -> 0 <= ly_reg L j /\ 0 <= rg_len rg /\ ly_reg L j + rg_len rg <= HTOP.
Hypothesis DIS : forall j1 j2 rg1 rg2, j1 <> j2 -> nth_error rs j1 = Some rg1 -> nth_error rs j2 = Some rg2 ->
  rk_meta rg1 = true -> rk_meta rg2 = true -> ranges_disjoint (ly_reg L j1, rg_len rg1) (ly_reg L j2, rg_len rg2).


#[using="HTB"] Lemma RL_pairwise : forall k, (forall j1 j2 rg1 rg2, j1 <> j2 -> nth_error (skipn k rs) j1 = Some rg1 -> nth_error (skipn k rs) j2 = Some rg2 ->
     rk_meta rg1 = true -> rk_meta rg2 = true -> ranges_disjoint (ly_reg L (k + j1), rg_len rg1) (ly_reg L (k + j2), rg_len rg2)) ->
  (forall j rg, nth_error (skipn k rs) j = Some rg -> rk_meta rg = true -> 0 <= ly_reg L (k + j) /\ 0 <= rg_len rg /\ ly_reg L (k + j) + rg_len rg <= HTOP) ->
  pairwise edisj (RL L (skipn k rs) k).
Proof. LiaFast.lf_pins (fun (HTB : LiaFast.U) => LiaFast.u0).
  intros k. remember (skipn k rs) as l eqn:El. clear El. revert k.
  induction l as [|rg l IH]; intros k D G; [exact I|]. cbn [RL].
  assert (IHk : pairwise edisj (RL L l (S k))).
  { apply IH.
    - intros j1 j2 rg1 rg2 Hne E1 E2 K1 K2. rewrite !Nat.add_succ_comm.
      exact (D (S j1) (S j2) rg1 rg2 ltac:(congruence) E1 E2 K1 K2).
    - intros j rg' E K. rewrite Nat.add_succ_comm. exact (G (S j) rg' E K). }
  destruct (rk_meta rg) eqn:Hk; [|exact IHk]. split; [|exact IHk].
  intros e He. destruct (RL_In L l (S k) e He) as (j & rg' & H1 & H2 & ->).
  pose proof (D 0%nat (S j) rg rg' ltac:(discriminate) eq_refl H1 Hk H2) as Dj. rewrite Nat.add_0_r, <- Nat.add_succ_comm in Dj.
  destruct (G 0%nat rg eq_refl Hk) as (A1 & A2 & A3). rewrite Nat.add_0_r in A1, A3.
  destruct (G (S j) rg' H1 H2) as (B1 & B2 & B3). rewrite <- Nat.add_succ_comm in B1, B3.
  unfold edisj, iv_overlap. cbn [fst snd]. rewrite !u_w64' by lia. unfold ranges_disjoint in Dj. cbn [fst snd] in Dj.
  apply andb_false_iff. destruct Dj as [Dj|Dj]; [right | left]; apply Z.ltb_ge; lia.
Qed.

#[using="HTB"] Lemma Wt_RL : forall k, (forall j rg, nth_error (skipn k rs) j = Some rg -> rk_meta rg = true ->
     0 <= ly_reg L (k + j) /\ 0 <= rg_len rg /\ ly_reg L (k + j) + rg_len rg <= HTOP) ->
  Wt (RL L (skipn k rs) k) (fun z => ind (inI 0 HTOP z)) = rtot (skipn k rs).
Proof. LiaFast.lf_pins (fun (HTB : LiaFast.U) => LiaFast.u0).
  intros k. remember (skipn k rs) as l eqn:El. clear El. revert k.
  induction l as [|rg l IH]; intros k G; [reflexivity|]. cbn [RL].
  assert (IHk : Wt (RL L l (S k)) (fun z => ind (inI 0 HTOP z)) = rtot l).
  { apply IH. intros j rg' E K. rewrite Nat.add_succ_comm. exact (G (S j) rg' E K). }
  unfold rtot. cbn [fold_right]. fold (rtot l). unfold rk_meta in *.
  destruct (rg_kind rg) eqn:Hk; [exact IHk | | exact IHk].
  assert (Hm : rk_meta rg = true) by (unfold rk_meta; rewrite Hk; reflexivity).
  destruct (G 0%nat rg eq_refl Hm) as (A1 & A2 & A3). rewrite Nat.add_0_r in A1, A3.
  rewrite Wt_cons, IHk. cbn [fst snd]. rewrite !u_w64' by lia.
  rewrite (sumr_ext _ (fun _ => 1)) by (intros z Hz; rewrite Z2Nat.id in Hz by lia; replace (inI 0 HTOP z) with true by (symmetry; apply inI_true; lia); reflexivity).
  rewrite sumr_one, Z2Nat.id by lia. reflexivity.
Qed.

Hypothesis HT0 : 0 <= HTOP.

#[using="L HTB GEO DIS HT0"] Theorem rtot_fit : rtot rs <= HTOP.
Proof. LiaFast.lf_pins (fun (L HTB GEO DIS HT0 : LiaFast.U) => LiaFast.u0).
  pose proof (Wt_RL 0%nat ltac:(intros j rg E K; exact (GEO j rg E K))) as W. cbn [skipn] in W.
  pose proof (RL_pairwise 0%nat ltac:(intros j1 j2 rg1 rg2 Hne E1 E2 K1 K2; exact (DIS j1 j2 rg1 rg2 Hne E1 E2 K1 K2))
                ltac:(intros j rg E K; exact (GEO j rg E K))) as PW. cbn [skipn] in PW.
  pose proof (Wt_disj_le (RL L rs 0) (fun z => ind (inI 0 HTOP z)) 0 HTOP PW HT0 ltac:(intros z; apply ind_range)
                ltac:(intros z Hz; cbv beta; replace (inI 0 HTOP z) with false by (symmetry; apply inI_false; lia); reflexivity)) as D.
  change (skipn 0 rs) with rs in W.
  assert (HS : sumr (fun z => ind (inI 0 HTOP z)) 0 (Z.to_nat (HTOP - 0)) = HTOP - 0) by (apply sumr_ind_full; exact HT0).
  rewrite HS in D. rewrite W in D. lia.
Qed.
End Fit.

(* [comment removed for export] *)
Theorem shift_le_34 : forall X R U s HTOP L, Inv X R U s -> rgeoA HTOP L s -> rdisj L s -> HTOP <= 2 ^ 47 ->
  st_meta_alloc_shift s <= 34.
Proof.
  intros X R U s HTOP0 L HI HG0 HD HTB0.
  set (HTOP := Z.max 0 HTOP0).
  assert (HTB : HTOP <= 2 ^ 47) by (unfold HTOP; lia). assert (HT0 : 0 <= HTOP) by (unfold HTOP; lia).
  assert (HG : forall r rg, region_of s r = Some rg -> rg_live rg = true -> PGSZ <= ly_reg L r /\ ly_reg L r + rg_len rg <= HTOP).
  { intros r rg E Lv. destruct (HG0 r rg E Lv) as (G1 & _ & G3 & _). unfold HTOP. lia. }
  pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & A5 & (F6 & _) & _).
  pose proof (inv_ctx HI) as C. unfold ctx_ok in C. destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C10 & _).
  assert (FIT : rtot (st_regions s) <= HTOP).
  { apply (rtot_fit HTOP L (st_regions s) HTB).
    - intros j rg E K. assert (Kk : rg_kind rg = RkMetaRes) by (unfold rk_meta in K; destruct (rg_kind rg); congruence).
      destruct (A5 j rg E Kk) as (Lv & _ & _). destruct (HG j rg E Lv) as (G1 & G3). unfold PGSZ in G1.
      pose proof (A5 j rg E Kk) as (_ & _ & N). lia.
    - intros j1 j2 rg1 rg2 Hne E1 E2 K1 K2.
      assert (Kk1 : rg_kind rg1 = RkMetaRes) by (unfold rk_meta in K1; destruct (rg_kind rg1); congruence).
      assert (Kk2 : rg_kind rg2 = RkMetaRes) by (unfold rk_meta in K2; destruct (rg_kind rg2); congruence).
      exact (HD j1 j2 rg1 rg2 Hne E1 E2 (proj1 (A5 j1 rg1 E1 Kk1)) (proj1 (A5 j2 rg2 E2 Kk2))).
    - exact HT0. }
  change (rtot (st_regions s)) with (resv_total s) in FIT. rewrite F6 in FIT.
  destruct (Z_le_gt_dec (st_meta_alloc_shift s) 34) as [E|E]; [exact E|]. exfalso.
  pose proof (Z.pow_le_mono_r 2 35 (st_meta_alloc_shift s) ltac:(lia) ltac:(lia)). unfold PGSZ in FIT. lia.
Qed.
