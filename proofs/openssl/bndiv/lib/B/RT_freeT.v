(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeD RT_freeI RT_freeS RT_refillstmt RT_refillst RT_refillwf RT_count.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rz_le2048 : forall n, rz_size n <= 2048.
Proof. intros n. unfold rz_size, rz_log. repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia. Qed.

(* [comment removed for export] *)
Lemma pq_fit : forall Σ c i n, rt_wf0 Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
  1 <= n /\ rz_size n + n <= ClassSize c.
Proof.
  intros Σ c i n HW Hc Hi. pose proof HW as (_ & (HR & _) & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
  pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi)) as (X1 & X2 & _). split; assumption.
Qed.

(* [comment removed for export] *)
Lemma pq_in_prb : forall Σ c i n, rt_wf0 Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
  l_PRB (lay Σ) <= p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 < l_PRB (lay Σ) + 0x2000011000.
Proof.
  intros Σ c i n HW Hc Hi. pose proof (geo_of_wf0 Σ HW) as HG.
  pose proof (fk_slot Σ HG c i _ Hc Hi) as (Y1 & Y2 & Y3 & _). pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  pose proof (rz_facts n) as (_ & R2). pose proof (rz_le2048 n) as R3. pose proof (ClassSize_range c Hc) as ((CS1 & _) & _).
  unfold rb, kUserCap in *. unfold p_abeg in *. clear - Y1 Y2 Y3 P3 P4 R2 R3 Hc CS1. lia.
Qed.

(* [comment removed for export] *)
Lemma hdr_unique : forall Σ M n n', rt_wf0 Σ -> qent_ok Σ (M, n) -> qent_ok Σ (M, n') -> n = n'.
Proof.
  intros Σ M n n' HW H1 H2. pose proof (geo_of_wf0 Σ HW) as HG.
  destruct H1 as [(c & i & Hc & Hi & E)|(t & Ht & Htq & Htn & Et)]; destruct H2 as [(c' & i' & Hc' & Hi' & E')|(t' & Ht' & Htq' & Htn' & Et')];
    cbn [fst snd] in *.
  - destruct (Z.eq_dec c c') as [<-|Hcc]; [destruct (Nat.eq_dec i i') as [<-|Hii]|].
    + rewrite Hi in Hi'. injection Hi' as <-. reflexivity.
    + exfalso. pose proof (g_slot_apart Σ HG c i c i' _ _ Hc Hc Hi Hi' (or_intror Hii)) as Y.
      pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (pq_fit Σ c i' n' HW Hc Hi') as (G1 & G2).
      pose proof (rz_facts n) as (_ & R1). pose proof (rz_facts n') as (_ & R1'). clear - Y E E' F1 F2 G1 G2 R1 R1'. lia.
    + exfalso. pose proof (g_slot_apart Σ HG c i c' i' _ _ Hc Hc' Hi Hi' (or_introl Hcc)) as Y.
      pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (pq_fit Σ c' i' n' HW Hc' Hi') as (G1 & G2).
      pose proof (rz_facts n) as (_ & R1). pose proof (rz_facts n') as (_ & R1'). clear - Y E E' F1 F2 G1 G2 R1 R1'. lia.
  - exfalso. pose proof (pq_in_prb Σ c i n HW Hc Hi) as PE. destruct (In_nth_error _ _ Ht') as (k' & Hk').
    pose proof (fk_map Σ HG k' t' Hk') as (X1 & _ & _ & _ & XP & _). pose proof (smsz_room (s_n t') ltac:(lia)) as SR.
    unfold apart in XP. clear - PE XP SR X1 E Et'. lia.
  - exfalso. pose proof (pq_in_prb Σ c' i' n' HW Hc' Hi') as PE. destruct (In_nth_error _ _ Ht) as (k & Hk).
    pose proof (fk_map Σ HG k t Hk) as (X1 & _ & _ & _ & XP & _). pose proof (smsz_room (s_n t) ltac:(lia)) as SR.
    unfold apart in XP. clear - PE XP SR X1 E' Et. lia.
  - destruct (In_nth_error _ _ Ht) as (k & Hk). destruct (In_nth_error _ _ Ht') as (k' & Hk').
    destruct (Nat.eq_dec k k') as [<-|Hkk]; [rewrite Hk in Hk'; injection Hk' as <-; rewrite <- Htn, <- Htn'; reflexivity|].
    exfalso. pose proof (fk_map Σ HG k t Hk) as (X1 & _ & _ & _ & _ & _ & _ & _ & _ & X10). pose proof (X10 k' t' Hk' ltac:(intros E; exact (Hkk (eq_sym E)))) as Y.
    pose proof (smsz_room (s_n t) ltac:(lia)) as SR. pose proof (fk_map Σ HG k' t' Hk') as (Y1 & _).
    pose proof (smsz_room (s_n t') ltac:(lia)) as SR'. unfold apart in Y. clear - Y SR SR' X1 Y1 Et Et'. lia.
Qed.

(* [comment removed for export] *)
Lemma pend_refill_e : forall Σ1 M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> pend_e (refillΣ Σ1 24) M n.
Proof.
  intros Σ1 M n HW (QE & FR & RC1 & RC2). split; [|split; [exact FR|split]].
  - destruct QE as [(c & i & Hc & Hi & E)|X]; [left|right; exact X].
    exists c, i. split; [exact Hc|]. split; [exact (rfs_keep Σ1 24 ltac:(lia) HW c i _ Hi) | exact E].
  - intros c' i' n' Hc' Hi' Hne. destruct (rfs_st Σ1 24 ltac:(lia) HW c' i' _ Hi') as [Hi0|(_ & E & _)]; [exact (RC1 c' i' n' Hc' Hi0 Hne) | discriminate E].
  - exact RC2.
Qed.

(* [comment removed for export] *)
Lemma pend_room_e : forall Σ1 M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> ca Σ1 24 = [] -> refill_room Σ1 24.
Proof.
  intros Σ1 M n HW (QE & FR & RC1 & RC2) HCA. pose proof (geo_of_wf0 Σ1 HW) as HG.
  apply (carved_room_gen Σ1 24 (Z.to_nat ((M - rb (l_SB (lay Σ1)) 24) / 8192)) HW ltac:(lia) HCA).
  intros i' n' Hi' Hne. apply (RC1 24 i' n' ltac:(lia) Hi'). intros E. apply Hne.
  pose proof (pq_fit Σ1 24 i' n' HW ltac:(lia) Hi') as (F1 & F2). change (ClassSize 24) with 8192 in F2.
  pose proof (rz_facts n') as (_ & R1). rewrite <- E. unfold p_abeg, rb. change (ClassSize 24) with 8192.
  replace (l_SB (lay Σ1) + 24 * 2 ^ 32 + Z.of_nat i' * 8192 + rz_size n' - 16 - (l_SB (lay Σ1) + 24 * 2 ^ 32))
    with (rz_size n' - 16 + Z.of_nat i' * 8192) by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by (clear - F1 F2 R1; lia). rewrite Z.add_0_l. symmetry. apply Nat2Z.id.
Qed.
