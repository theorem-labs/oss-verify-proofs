(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Lemma one5_iff (A B C D E A' B' C' D' E' : Prop) :
  (A <-> A') -> (B <-> B') -> (C <-> C') -> (D <-> D') -> (E <-> E') -> one5 A B C D E -> one5 A' B' C' D' E'.
Proof. unfold one5. tauto. Qed.
(* [comment removed for export] *)
Lemma one5_E_to_B (A B C D E B' E' : Prop) : E -> B' -> ~ E' -> one5 A B C D E -> one5 A B' C D E'.
Proof. unfold one5. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst bg, sstart (MR st g) i).
Hypothesis C1 : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0.
Hypothesis C2 : x_fresh X <> Some g -> m_sizeclass (MR st g) < 48 -> in_list LS g.
Hypothesis C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g).
Let st' := upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

Lemma aor_form : st' = upd_meta g (fun r => m_set_avail (m_avail (MR st g)) (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) r)) st.
Proof. unfold st', upd_meta, MR. destruct (get_meta_rec st g); reflexivity. Qed.

Theorem INVL_aor : INVL (xpend X None) st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false).
  { destruct (tbit (m_avail (MR st g)) i) eqn:E; [| reflexivity]. exfalso. unfold one5 in Pi. tauto. }
  assert (TB : forall j, 0 <= j -> tbit (Z.lor (m_freed (MR st g)) (bit i)) j = tbit (m_freed (MR st g)) j || (i =? j)).
  { intros j Hj. unfold tbit. rewrite Z.lor_spec, testbit_bit by lia. reflexivity. }
  assert (NZ : Z.lor (m_freed (MR st g)) (bit i) <> 0).
  { intros E. pose proof (TB i ltac:(lia)) as T. rewrite E, Z.eqb_refl, Bool.orb_true_r in T. unfold tbit in T. rewrite Z.bits_0 in T. discriminate. }
  rewrite aor_form.
  apply (INVL_mask_change X st L BL LS g bg ai (m_avail (MR st g)) (Z.lor (m_freed (MR st g)) (bit i)) None INV Hg).
  - split; [exact M1|]. split; [apply Z.lor_nonneg; split; [exact M2| unfold bit; apply Z.pow_nonneg; lia]|]. split; [exact M3|].
    split; [| split].
    + intros j Hj. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M4 j Hj H)| apply Z.eqb_eq in H; lia].
    + intros j Hj Ha. rewrite TB by exact Hj. rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
    + intros j Hj. rewrite TB by lia. rewrite (M6 j Hj). reflexivity.
  - intros j Hj. cbn zeta. rewrite TB by lia.
    pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in P |- *.
    destruct (Z.eqb_spec i j) as [<-|NE].
    + rewrite Bool.orb_true_r. eapply one5_E_to_B; [exact HP| reflexivity| discriminate| exact P].
    + rewrite Bool.orb_false_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
      rewrite HP. split; [intros E; exfalso| discriminate]. inversion E.
      destruct (Z.lt_total i j) as [LT|[EQ|LT]]; [| lia|].
      * pose proof (sstart_lt _ _ _ IG _ _ i j Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
      * pose proof (sstart_lt _ _ _ IG _ _ j i Hgh LT). pose proof (stride_ge _ _ _ IG _ _ Hgh) as [SG _]. unfold UNIT in *. lia.
  - right. split.
    + intros s Hs. rewrite HP in Hs. inversion Hs. subst s. exists i. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh). reflexivity.
    + intros s Hs. discriminate.
  - intros NF sc Hin Hnh. split; [exact (C1 NF sc Hin Hnh)| exact NZ].
  - intros NF Hsc NI. exfalso. exact (NI (C2 NF Hsc)).
  - intros _ Hsc Hlt. exfalso. pose proof (C3 Hsc). lia.
Qed.
End AOR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ACT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (a ba : aptr) (aia : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Ha : s_groups st !! ba = Some (mkGhdr (Some a) aia).
Hypothesis AV0 : m_avail (MR st a) = 0.
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st a)))) = Some a.
Let act := mask_upto aia.
Let A' := Z.land (m_freed (MR st a)) act.
Let F' := Z.ldiff (m_freed (MR st a)) act.
Let st' := upd_meta a (fun r => m_set_avail A' (m_set_freed F' r)) st.

Lemma act_eq : match m_mem (MR st a) with
               | Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (MR st a))))
               | None => 0 end = act.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ aia Ha)). cbn. unfold group_active_idx, get_group. rewrite Ha.
  pose proof (g_ai _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as AI. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha)) as LI.
  unfold act. f_equal. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia.
Qed.

Lemma activate_group_eq {T} (k : mstate -> Z -> M T) bail : activate_group a st k bail = k st' A'.
Proof.
  unfold activate_group. fold (MR st a). rewrite AV0. cbn [guard Z.eqb]. rewrite act_eq. reflexivity.
Qed.

Lemma a_listed : In a (LS (LActive (m_sizeclass (MR st a)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st a)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

Theorem INVL_activate : INVL X st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Ha) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hah : hosts st ba a) by (exists aia; exact Ha).
  assert (TA : forall j, 0 <= j -> tbit A' j = tbit (m_freed (MR st a)) j && (j <=? aia)).
  { intros j Hj. unfold A', act, tbit. rewrite Z.land_spec, testbit_mask_upto by lia. reflexivity. }
  assert (TF : forall j, 0 <= j -> tbit F' j = tbit (m_freed (MR st a)) j && negb (j <=? aia)).
  { intros j Hj. unfold F', act, tbit. rewrite Z.ldiff_spec, testbit_mask_upto by lia. reflexivity. }
  assert (X_eta : X = mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) by (destruct X; reflexivity).
  rewrite X_eta at 1.
  apply (INVL_mask_change X st L BL LS a ba aia A' F' (x_pend X) INV Ha).
  - split; [apply Z.land_nonneg; left; exact M2|]. split; [apply Z.ldiff_nonneg; left; exact M2|].
    split; [| split; [| split]].
    + intros j Hj. rewrite TA by exact Hj. rewrite Bool.andb_true_iff. intros [_ H]. apply Z.leb_le in H. exact H.
    + intros j Hj. rewrite TF by exact Hj. rewrite Bool.andb_true_iff. intros [H _]. exact (M4 j Hj H).
    + intros j Hj. rewrite TA, TF by exact Hj. rewrite !Bool.andb_true_iff. intros [_ H1] [_ H2]. rewrite H1 in H2. discriminate.
    + intros j Hj. rewrite TF by lia. rewrite (M6 j Hj). cbn. destruct (Z.leb_spec j aia); [lia| reflexivity].
  - intros j Hj. cbn zeta. rewrite TA, TF by lia.
    pose proof (is_part _ _ _ IS _ _ _ j Ha Hj) as P. cbn zeta in P.
    assert (NAj : tbit (m_avail (MR st a)) j = false) by (unfold tbit; rewrite AV0; apply Z.bits_0).
    rewrite NAj in P.
    destruct (tbit (m_freed (MR st a)) j); destruct (j <=? aia); cbn [andb negb]; revert P; unfold one5; clear; tauto.
  - left. reflexivity.
  - intros NF sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc a Hin) as (_ & _ & E). subst sc. exact (Hnh (eq_sym HEAD)).
  - intros NF Hsc NI. exfalso. apply NI. exists (LActive (m_sizeclass (MR st a))). exact a_listed.
  - intros NF Hsc Hlt. destruct (g_under _ _ _ _ _ _ GO NF Hsc Hlt) as [_ F0]. unfold A', F'. rewrite F0. split; [apply Z.land_0_l| apply Z.ldiff_0_l].
Qed.
End ACT.
End CEIL_WRAP_1.

