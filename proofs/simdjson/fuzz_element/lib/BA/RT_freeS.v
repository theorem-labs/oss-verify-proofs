(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeD RT_freeI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition pend_e (Σ : rtsA) (M n : Z) : Prop :=
  qent_ok Σ (M, n) /\ ~ In M (map fst (qents Σ))
  /\ (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n') ->
        p_abeg (l_SB (lay Σ)) c i + rz_size n' - 16 <> M -> In (p_abeg (l_SB (lay Σ)) c i + rz_size n' - 16, n') (qents Σ))
  /\ (forall t, In t (sec Σ) -> s_quar t = true -> s_mb t + 6128 <> M -> In (s_mb t + 6128, s_n t) (qents Σ)).

Lemma pend_e_p : forall Σ c i n, pend_ok Σ c i n -> pend_e Σ (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n.
Proof.
  intros Σ c i n (Hc & Hn & FR & RC1 & RC2). split.
  - left. exists c, i. split; [exact Hc|]. split; [exact Hn | reflexivity].
  - split; [exact FR|]. split.
    + intros c' i' n' Hc' Hi' Hne. apply (RC1 c' i' n' Hc' Hi'). destruct (Z.eq_dec c' c) as [->|X]; [|left; exact X].
      right. intros ->. rewrite Hn in Hi'. injection Hi' as <-. exact (Hne eq_refl).
    + intros t Ht Hq _. exact (RC2 t Ht Hq).
Qed.

Definition free_s (Σ : rtsA) (k : nat) (s : secst) (D' : depot) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (upd (sec Σ) k (mkSec (s_mb s) (s_n s) true)) (sec_nres Σ)
    (aw Σ) (ql Σ) (qg Σ) D' (fs0 Σ) (fsc0 Σ) (fs4 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live_remove (s_ubeg s) (live Σ)) (frames Σ) (ann Σ).

Lemma Forall_upd : forall {X} (P : X -> Prop) (l : list X) i x, Forall P l -> P x -> Forall P (upd l i x).
Proof.
  intros X P l. induction l as [|y l IH]; intros i x H Hx; [destruct i; constructor|].
  apply Forall_cons_iff in H as (H1 & H2). destruct i as [|i]; cbn [upd]; constructor; [exact Hx | exact H2 | exact H1 | exact (IH i x H2 Hx)].
Qed.

Lemma secsum_upd : forall (l : list secst) i x, (forall y, nth_error l i = Some y -> s_n y = s_n x) ->
  fold_right (fun s acc => smsz (s_n s) + acc) 0 (upd l i x) = fold_right (fun s acc => smsz (s_n s) + acc) 0 l.
Proof.
  intros l. induction l as [|y l IH]; intros i x H; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [upd fold_right].
  - rewrite (H y eq_refl). reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Section FreeS.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (D' : depot).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = false.
Hypothesis Hsn : s_n s <= 0x10000000.
Hypothesis HDok : depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HDinv : dep_step (dep Σ) D'.
#[local] Notation s1 := (mkSec (s_mb s) (s_n s) true).
#[local] Notation Σ1 := (free_s Σ k s D').

Lemma fs_nth : forall k' t, nth_error (upd (sec Σ) k s1) k' = Some t -> (k' = k /\ t = s1) \/ (k' <> k /\ nth_error (sec Σ) k' = Some t).
Proof using Hk.
  intros k' t H. destruct (Nat.eq_dec k' k) as [->|Hne].
  - left. split; [reflexivity|]. rewrite nth_error_upd_same in H by (apply nth_error_Some; rewrite Hk; discriminate). injection H as <-. reflexivity.
  - right. split; [exact Hne|]. rewrite nth_error_upd_other in H by (intros E; exact (Hne (eq_sym E))). exact H.
Qed.

Lemma fs_in : forall t, In t (upd (sec Σ) k s1) -> t = s1 \/ exists k', k' <> k /\ nth_error (sec Σ) k' = Some t.
Proof using Hk.
  intros t Ht. destruct (In_nth_error _ _ Ht) as (k' & Hk'). destruct (fs_nth k' t Hk') as [(_ & ->)|(Hne & X)]; [left; reflexivity|].
  right. exists k'. split; [exact Hne | exact X].
Qed.

Lemma fs_in_other : forall k' t, k' <> k -> nth_error (sec Σ) k' = Some t -> In t (upd (sec Σ) k s1).
Proof using Hk.
  intros k' t Hne H. apply (nth_error_In _ k'). rewrite nth_error_upd_other by (intros E; exact (Hne (eq_sym E))). exact H.
Qed.

Lemma fs_in_new : In s1 (upd (sec Σ) k s1).
Proof using Hk. apply (nth_error_In _ k). apply nth_error_upd_same. apply nth_error_Some. rewrite Hk. discriminate. Qed.

Lemma fs_apart : forall k' t, nth_error (sec Σ) k' = Some t -> k' <> k -> apart (s_mb s) (smsz (s_n s)) (s_mb t) (smsz (s_n t)).
Proof using HA Hk.
  intros k' t Hk' Hne. pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X). exact (X k' t Hk' Hne).
Qed.

Lemma fs_ubeg_ne : forall k' t, nth_error (sec Σ) k' = Some t -> k' <> k -> s_ubeg t <> s_ubeg s.
Proof using HA Hk.
  intros k' t Hk' Hne E. pose proof (fs_apart k' t Hk' Hne) as Y.
  pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (X1 & _ & _ & _ & _ & _ & _ & X8 & X9 & _).
  pose proof (fk_map Σ (geo_of_ART Σ m HA) k' t Hk') as (Y1 & _ & _ & _ & _ & _ & _ & Y8 & Y9 & _).
  unfold s_ubeg, apart in *. lia.
Qed.

Theorem free_s_wf : rt_wf0 Σ1.
Proof using HA Hk Hq Hsn HDok HDinv.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & _).
  assert (LRI : In (s_ubeg s, s_n s) (live Σ)) by (destruct W3 as (_ & _ & _ & _ & V5); exact (V5 s (nth_error_In _ _ Hk) Hq)).
  pose proof (live_remove_length_in _ _ (live Σ) LRI) as LRL.
  assert (POT' : dep_pot (d_n D') (Z.of_nat (length (live_remove (s_ubeg s) (live Σ)))) (credit Σ))
    by (apply (dep_pot_free (dep Σ) D' (Z.of_nat (length (live Σ))) _ _ HDinv W9); lia).
  pose proof (dep_inv_bounds D' _ _ (proj1 HDinv) POT' ltac:(lia) ltac:(destruct W7 as (C0 & _); exact C0)) as (B1 & B2).
  unfold rt_wf0, free_s. cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 ia_init credit live frames ann].
  split; [exact W1|]. split; [exact W2|]. split.
  {
    unfold live_wf. cbn [pr live lay sec]. destruct W3 as (V1 & V2 & V3 & V4 & V5).
    split; [pose proof (live_remove_length (s_ubeg s) (live Σ)); lia|]. split; [apply NoDup_ListNoDup; apply nodup_live_remove; apply NoDup_ListNoDup; exact V2|].
    split; [|split].
    - intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
      destruct (V3 p' n' Hin) as [X|(t & Ht & Htq & Htn & Ep)]; [left; exact X|right].
      destruct (In_nth_error _ _ Ht) as (k' & Hk'). destruct (Nat.eq_dec k' k) as [->|Hkk].
      + rewrite Hk in Hk'. injection Hk' as <-. exfalso. exact (Hne Ep).
      + exists t. split; [exact (fs_in_other k' t Hkk Hk')|]. split; [exact Htq|]. split; [exact Htn | exact Ep].
    - intros c' i' n' Hc' Hn'. apply live_remove_In. cbn [fst]. split; [exact (V4 c' i' n' Hc' Hn')|].
      intros E. exact (fp_sec_ne Σ m c' i' n' HA Hc' Hn' s (nth_error_In _ _ Hk) (eq_sym E)).
    - intros t Ht Htq. apply live_remove_In. cbn [fst]. destruct (fs_in t Ht) as [->|(k' & Hkk & Hk')]; [discriminate Htq|].
      split; [exact (V5 t (nth_error_In _ _ Hk') Htq) | exact (fs_ubeg_ne k' t Hk' Hkk)]. }
  split.
  {
    destruct W4 as (S1 & S2 & S3 & S4 & S5 & S6 & S7). unfold sec_wf. cbn [sec sec_nres lay aw].
    split; [rewrite upd_length; exact S1|]. split; [exact S2|]. split; [intros X; apply S3; destruct (sec Σ); [cbn in X; exact X | discriminate]|].
    split.
    { apply Forall_upd; [exact S4|]. exact (proj1 (Forall_forall _ _) S4 s (nth_error_In _ _ Hk)). }
    split.
    { intros k1 k2 t1 t2 H1 H2 Hne. destruct (fs_nth k1 t1 H1) as [(-> & ->)|(_ & X1)]; destruct (fs_nth k2 t2 H2) as [(-> & ->)|(_ & X2)].
      - exfalso. exact (Hne eq_refl).
      - exact (S5 k k2 s t2 Hk X2 Hne).
      - exact (S5 k1 k t1 s X1 Hk Hne).
      - exact (S5 k1 k2 t1 t2 X1 X2 Hne). }
    split; [apply Forall_upd; [exact S6|]; exact (proj1 (Forall_forall _ _) S6 s (nth_error_In _ _ Hk))|].
    apply Forall_upd; [exact S7|]. cbn [s_n s_quar]. intros _. exact Hsn. }
  split.
  {
    unfold quar_wf. cbn [ql qg pr lay sec]. destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [|split; [exact Q7 | exact Q8]].
    unfold qents in *. cbn [ql qg] in *. apply Forall_forall. intros e He.
    destruct (proj1 (Forall_forall _ _) Q6 e He) as [X|(t & Ht & Htq & Htn & Ee)]; [left; exact X|right].
    destruct (In_nth_error _ _ Ht) as (k' & Hk'). destruct (Nat.eq_dec k' k) as [->|Hkk].
    - rewrite Hk in Hk'. injection Hk' as <-. rewrite Hq in Htq. discriminate Htq.
    - exists t. split; [exact (fs_in_other k' t Hkk Hk')|]. split; [exact Htq|]. split; [exact Htn | exact Ee]. }
  split; [exact W6|]. split.
  {
    unfold budget_wf, secsum in *. cbn [credit aw sec]. destruct W7 as (G1 & G2 & G3 & G4 & G5).
    assert (ES : fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (upd (sec Σ) k s1) = fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σ))
      by (apply secsum_upd; intros y Hy; rewrite Hk in Hy; injection Hy as <-; reflexivity).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [|rewrite ES; exact G5].
    assert (E : rt_eager (free_s Σ k s D') = rt_eager Σ) by (unfold rt_eager, free_s; cbn [pr sec sec_nres]; rewrite ES; reflexivity).
    unfold free_s in E. cbn [pr sec sec_nres] in E. rewrite E. exact G4. }
  split; [exact HDok|]. split; [exact POT'|]. split; [lia|]. exact (proj1 HDinv).
Qed.

Theorem pend_e_s : pend_e Σ1 (s_mb s + 6128) (s_n s).
Proof using HA Hk Hq.
  pose proof (ART_wf Σ m HA) as HW. pose proof HW as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & Q6 & _) & _ & _ & _ & _ & _ & _ & (RC1 & RC2)).
  pose proof (fk_map Σ (geo_of_ART Σ m HA) k s Hk) as (X1 & X2 & X3 & X4 & XP & _ & _ & X8 & X9 & _).
  pose proof (fk_prb Σ (geo_of_ART Σ m HA)) as (P0 & P1 & P2 & P3 & P4).
  split; [|split; [|split]].
  - right. exists s1. split; [exact fs_in_new|]. split; [reflexivity|]. split; reflexivity.
  - intros Hin. apply in_map_iff in Hin as (e & Ee & He). unfold qents in He. cbn [free_s ql qg] in He.
    destruct (proj1 (Forall_forall _ _) Q6 e He) as [(c' & i' & Hc' & Hi' & Ep)|(t & Ht & Htq & Htn & Et)].
    +
      pose proof (fk_slot Σ (geo_of_ART Σ m HA) c' i' _ Hc' Hi') as (Y1 & Y2 & Y3 & _).
      pose proof (rz_facts (snd e)) as (R1 & R2).
      assert (PE : l_PRB (lay Σ) <= fst e < l_PRB (lay Σ) + 0x2000011000).
      { assert (R3 : rz_size (snd e) <= 2048)
          by (unfold rz_size, rz_log; repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia).
        rewrite Ep. pose proof (ClassSize_range c' Hc') as ((CS1 & CS2) & _). unfold rb, kUserCap in *.
        unfold p_abeg in *. clear - Y1 Y2 Y3 P3 P4 R2 R3 Hc' CS1. lia. }
      rewrite Ee in PE. pose proof (smsz_room (s_n s) ltac:(lia)) as SR. unfold apart in XP. clear - PE XP SR X1. lia.
    + destruct (In_nth_error _ _ Ht) as (k' & Hk'). destruct (Nat.eq_dec k' k) as [->|Hkk].
      * rewrite Hk in Hk'. injection Hk' as <-. rewrite Hq in Htq. discriminate Htq.
      * pose proof (fs_apart k' t Hk' Hkk) as Y. pose proof (fk_map Σ (geo_of_ART Σ m HA) k' t Hk') as (Z1 & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
        pose proof (smsz_room (s_n s) ltac:(lia)) as SR. pose proof (smsz_room (s_n t) ltac:(lia)) as SR'.
        rewrite Ee in Et. unfold apart in Y. clear - Y Et SR SR' X1 Z1. lia.
  - intros c' i' n' Hc' Hi' _. exact (RC1 c' i' n' Hc' Hi').
  - intros t Ht Htq Hne. cbn [free_s sec] in Ht. destruct (fs_in t Ht) as [->|(k' & Hkk & Hk')]; [exfalso; exact (Hne eq_refl)|].
    exact (RC2 t (nth_error_In _ _ Hk') Htq).
Qed.

End FreeS.

End GWIN.
