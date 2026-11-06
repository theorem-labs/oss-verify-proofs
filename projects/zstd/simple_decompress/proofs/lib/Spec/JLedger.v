(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Malloc KInv.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive jphase : Type :=
| JUntried
| JQueried (curG curC : Z)
| JGuard (curG curC : Z)
| JLive
| JDead.

Record jled : Type := mkJ {
  j_resvG : list (Z * Z);
  j_resvC : list (Z * Z);
  j_groups : list (Z * Z * Z);        (* [comment removed for export] *)
  j_metas : list (Z * Z * Z * Z);     (* [comment removed for export] *)
  j_brkreg : option (Z * Z * Z);      (* [comment removed for export] *)
  j_brk : jphase;
  j_live : list cptr;
  j_atopG : Z;                         (* [comment removed for export] *)
  j_atopC : Z
}.

Definition jled_init (resvG resvC : list (Z * Z)) (atopG atopC : Z) : jled := mkJ resvG resvC [] [] None JUntried [] atopG atopC.
Definition jset_groups v J := mkJ (j_resvG J) (j_resvC J) v (j_metas J) (j_brkreg J) (j_brk J) (j_live J) (j_atopG J) (j_atopC J).
Definition jset_metas v J := mkJ (j_resvG J) (j_resvC J) (j_groups J) v (j_brkreg J) (j_brk J) (j_live J) (j_atopG J) (j_atopC J).
Definition jset_brkreg v J := mkJ (j_resvG J) (j_resvC J) (j_groups J) (j_metas J) v (j_brk J) (j_live J) (j_atopG J) (j_atopC J).
Definition jset_brk v J := mkJ (j_resvG J) (j_resvC J) (j_groups J) (j_metas J) (j_brkreg J) v (j_live J) (j_atopG J) (j_atopC J).
Definition jset_live v J := mkJ (j_resvG J) (j_resvC J) (j_groups J) (j_metas J) (j_brkreg J) (j_brk J) v (j_atopG J) (j_atopC J).

Definition phG (p : jphase) : brk_phase :=
  match p with JUntried => BPUntried | JQueried c _ => BPQueried c | JGuard c _ => BPGuard c | JLive => BPLive | JDead => BPDead end.
Definition phC (p : jphase) : brk_phase :=
  match p with JUntried => BPUntried | JQueried _ c => BPQueried c | JGuard _ c => BPGuard c | JLive => BPLive | JDead => BPDead end.

Definition gG (g : Z * Z * Z) : Z * Z := let '(bG, bC, l) := g in (bG, l).
Definition gC (g : Z * Z * Z) : Z * Z := let '(bG, bC, l) := g in (bC, l).
Definition mG (m : Z * Z * Z * Z) : Z * Z * Z := let '(bG, bC, l, k) := m in (bG, l, k).
Definition mC (m : Z * Z * Z * Z) : Z * Z * Z := let '(bG, bC, l, k) := m in (bC, l, k).
Definition rG (r : Z * Z * Z) : Z * Z := let '(bG, bC, l) := r in (bG, l).
Definition rC (r : Z * Z * Z) : Z * Z := let '(bG, bC, l) := r in (bC, l).

Definition projG (J : jled) : mled :=
  mkLed (j_resvG J) (map gG (j_groups J)) (map mG (j_metas J)) (option_map rG (j_brkreg J)) (phG (j_brk J)) (j_live J) (j_atopG J).
Definition projC (J : jled) : mled :=
  mkLed (j_resvC J) (map gC (j_groups J)) (map mC (j_metas J)) (option_map rC (j_brkreg J)) (phC (j_brk J)) (j_live J) (j_atopC J).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_fixed (flags : Z) : bool := negb (Z.land flags MAP_FIXED =? 0).

(* [comment removed for export] *)
Definition jev_rel (J : jled) (eG eC : ev) : Prop :=
  match eG, eC with
  | EBrk rG', EBrk rC' =>
      (rG' = 0 /\ rC' = 0 /\ j_brk J = JUntried)
      \/ (exists cG cC, j_brk J = JQueried cG cC /\ rG' = round_up_pg cG + 2 * PGSZ /\ rC' = round_up_pg cC + 2 * PGSZ /\ 0 < rG' /\ 0 < rC')
      \/ (exists bG bC l, j_brk J = JLive /\ j_brkreg J = Some (bG, bC, l) /\ rG' = bG + l + PGSZ /\ rC' = bC + l + PGSZ /\ 0 < rG' /\ 0 < rC')
  | EMmap aG len prot flags, EMmap aC len' prot' flags' =>
      len' = len /\ prot' = prot /\ flags' = flags /\
      ((brk_quiet (projG J) /\ aG = 0 /\ aC = 0 /\ flags = MAPF /\ (prot = PROT_NONE \/ prot = PROT_RW) /\ 0 < len < LEN_MAX)
       \/ (exists cG cC, j_brk J = JGuard cG cC /\ aG = round_up_pg cG /\ aC = round_up_pg cC /\ len = PGSZ /\ prot = PROT_NONE /\ flags = MAPFX))
  | EMunmap aG len, EMunmap aC len' =>
      len' = len /\ brk_quiet (projG J) /\ exists l, In (aG, aC, l) (j_groups J) /\ (len = l \/ len = round_up_pg l)
  | EMprotect aG len prot, EMprotect aC len' prot' =>
      len' = len /\ prot' = prot /\ brk_quiet (projG J) /\ len = PGSZ /\ prot = PROT_RW /\
      exists bG bC l k, In (bG, bC, l, k) (j_metas J) /\ aG = bG + (1 + k) * PGSZ /\ aC = bC + (1 + k) * PGSZ /\ (2 + k) * PGSZ <= round_up_pg l
  | _, _ => False
  end.

Definition mprot_okb (z : Z) : bool := (z =? 0) || (z =? TWO64 - ENOSYS).

(* [comment removed for export] *)
Definition same_class (eG eC : ev) (zG zC : Z) : bool :=
  match eG, eC with
  | EBrk rG', EBrk rC' => if rG' =? 0 then true else Bool.eqb (zG =? rG') (zC =? rC')
  | EMmap _ _ _ flags, EMmap _ _ _ _ => if is_fixed flags then true else Bool.eqb (is_err zG) (is_err zC)
  | EMunmap _ _, EMunmap _ _ => true
  | EMprotect _ _ _, EMprotect _ _ _ => Bool.eqb (mprot_okb zG) (mprot_okb zC)
  | _, _ => false
  end.

Definition jans_ok (J : jled) (eG eC : ev) (zG zC : Z) : bool :=
  answer_ok (projG J) eG zG && answer_ok (projC J) eC zC && same_class eG eC zG zC.

Fixpoint jg_remove (aG : Z) (l : list (Z * Z * Z)) : list (Z * Z * Z) :=
  match l with
  | [] => []
  | g :: l' => if fst (fst g) =? aG then l' else g :: jg_remove aG l'
  end.
Definition jbump (aG : Z) (m : Z * Z * Z * Z) : Z * Z * Z * Z :=
  let '(bG, bC, l, k) := m in if bG + (1 + k) * PGSZ =? aG then (bG, bC, l, k + 1) else m.

Definition jevent_post (J : jled) (eG eC : ev) (zG zC : Z) : jled :=
  match eG, eC with
  | EBrk rG', EBrk rC' =>
      if rG' =? 0 then jset_brk (JQueried zG zC) J
      else if zG =? rG' then
             match j_brk J with
             | JQueried cG cC => jset_brk (JGuard cG cC) J
             | _ => match j_brkreg J with
                    | Some (bG, bC, l) => jset_brkreg (Some (bG, bC, l + PGSZ)) J
                    | None => J
                    end
             end
           else jset_brk JDead J
  | EMmap aG len prot flags, EMmap aC _ _ _ =>
      if Z.land flags MAP_FIXED =? 0 then
        if is_err zG then J
        else if prot =? PROT_NONE then jset_metas ((zG, zC, len, 0) :: j_metas J) J
        else jset_groups ((zG, zC, len) :: j_groups J) J
      else jset_brk JLive (jset_brkreg (Some (aG, aC, 2 * PGSZ)) J)
  | EMunmap aG len, EMunmap _ _ => jset_groups (jg_remove aG (j_groups J)) J
  | EMprotect aG len prot, EMprotect _ _ _ =>
      if mprot_okb zG then jset_metas (map (jbump aG) (j_metas J)) J else J
  | _, _ => J
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition erase (cs : mstate) : mstate :=
  mkState (s_ctx cs) (fmap (fun r => mkRegion (r_kind r) 0 (r_len r)) (s_regions cs)) (s_shadow cs) (s_next_rid cs)
          (s_metas cs) (s_areas cs) (s_groups cs) (s_slots cs) (s_tick cs) (s_secret cs) [] 0.

Fixpoint jtree_ok {R1 R2} (J : jled) (tG : stree ev Z R1) (tC : stree ev Z R2) (Post : jled -> R1 -> R2 -> Prop) : Prop :=
  match tG, tC with
  | SRet x, SRet y => Post J x y
  | SVis eG kG, SVis eC kC =>
      jev_rel J eG eC /\
      forall zG zC, jans_ok J eG eC zG zC = true -> jtree_ok (jevent_post J eG eC zG zC) (kG zG) (kC zC) Post
  | _, _ => False
  end.

Inductive jcpath {R1 R2} : jled -> stree ev Z R1 -> stree ev Z R2 -> jled -> R1 -> R2 -> Prop :=
| jcpath_ret J x y : jcpath J (SRet x) (SRet y) J x y
| jcpath_vis J eG eC kG kC zG zC J' x y :
    jans_ok J eG eC zG zC = true -> jcpath (jevent_post J eG eC zG zC) (kG zG) (kC zC) J' x y ->
    jcpath J (SVis eG kG) (SVis eC kC) J' x y.

Definition malloc_post2 (J : jled) (x y : mstate * option cptr) : Prop :=
  snd x = snd y /\ erase (fst x) = erase (fst y)
  /\ match snd x with Some c => ~ In c (j_live J) | None => True end.
Definition free_post2 (J : jled) (x y : mstate) : Prop := erase x = erase y.

Inductive jcreach : mstate -> mstate -> jled -> Prop :=
| jcreach_init resvG resvC atopG atopC : 0 < atopG <= atop_hi -> 0 < atopC <= atop_hi ->
    jcreach (strip (minit 0 resvG atopG)) (strip (minit 0 resvC atopC)) (jled_init resvG resvC atopG atopC)
| jcreach_malloc csG csC J n J' xG xC :
    jcreach csG csC J -> 0 <= n -> jcpath J (cmalloc csG n) (cmalloc csC n) J' xG xC ->
    jcreach (fst xG) (fst xC) (match snd xG with Some c => jset_live (c :: j_live J') J' | None => J' end)
| jcreach_free csG csC J c J' csG' csC' :
    jcreach csG csC J -> In c (j_live J) -> jcpath J (cfree csG (Some c)) (cfree csC (Some c)) J' csG' csC' ->
    jcreach csG' csC' (jset_live (ap_remove c (j_live J')) J').

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma erase_strip_minit : forall s rv rv' a a', erase (strip (minit s rv a)) = erase (strip (minit s rv' a')).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_quiet_proj : forall J, brk_quiet (projG J) <-> brk_quiet (projC J).
Proof. intros J. unfold brk_quiet, projG, projC. cbn. destruct (j_brk J); cbn; tauto. Qed.

Lemma jev_rel_pre : forall J eG eC, jev_rel J eG eC -> event_pre (projG J) eG /\ event_pre (projC J) eC.
Proof.
  intros J eG eC H. destruct eG, eC; cbn in H; try contradiction.
  - destruct H as [(-> & -> & Hph)|[(cG & cC & Hph & -> & -> & _)|(bG & bC & l & Hph & Hreg & -> & -> & _)]]; cbn; rewrite ?Hph, ?Hreg; cbn.
    + split; left; auto.
    + split; right; left; eexists; eauto.
    + split; right; right; do 2 eexists; eauto.
  - destruct H as (-> & -> & -> & [(Hq & -> & -> & -> & Hp & Hl)|(cG & cC & Hph & -> & -> & -> & -> & ->)]); cbn.
    + split; left; repeat split; auto; try lia. apply brk_quiet_proj. exact Hq.
    + rewrite Hph. split; right; eexists; eauto.
  - destruct H as (-> & Hq & l & Hin & Hl). cbn. split.
    + split; [exact Hq|]. exists l. split; [|exact Hl]. apply in_map_iff. eexists; split; [|exact Hin]; reflexivity.
    + split; [apply brk_quiet_proj; exact Hq|]. exists l. split; [|exact Hl]. apply in_map_iff. eexists; split; [|exact Hin]; reflexivity.
  - destruct H as (-> & -> & Hq & -> & -> & bG & bC & l & k & Hin & -> & -> & Hk). cbn. split.
    + split; [exact Hq|]. repeat split; auto. exists bG, l, k. split; [|auto]. apply in_map_iff. exists (bG, bC, l, k). auto.
    + split; [apply brk_quiet_proj; exact Hq|]. repeat split; auto. exists bC, l, k. split; [|auto]. apply in_map_iff. exists (bG, bC, l, k). auto.
Qed.

Lemma jans_ok_G : forall J eG eC zG zC, jans_ok J eG eC zG zC = true -> answer_ok (projG J) eG zG = true.
Proof. intros. unfold jans_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H. Qed.
Lemma jans_ok_C : forall J eG eC zG zC, jans_ok J eG eC zG zC = true -> answer_ok (projC J) eC zC = true.
Proof. intros. unfold jans_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H. Qed.
Lemma jans_ok_class : forall J eG eC zG zC, jans_ok J eG eC zG zC = true -> same_class eG eC zG zC = true.
Proof. intros. unfold jans_ok in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma projG_live : forall J, ld_live (projG J) = j_live J. Proof. reflexivity. Qed.
Lemma projC_live : forall J, ld_live (projC J) = j_live J. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_gG_remove : forall aG l, map gG (jg_remove aG l) = g_remove aG (map gG l).
Proof.
  induction l as [|[[bG bC] n] l IH]; intros; [reflexivity|]. cbn. destruct (bG =? aG); [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma map_mG_bump : forall aG l, map mG (map (jbump aG) l) = map (bump_meta aG) (map mG l).
Proof.
  induction l as [|[[[bG bC] n] k] l IH]; intros; [reflexivity|]. cbn. rewrite IH. unfold bump_meta. destruct (bG + (1 + k) * PGSZ =? aG); reflexivity.
Qed.

Lemma projG_post : forall J eG eC zG zC,
  jev_rel J eG eC -> same_class eG eC zG zC = true ->
  projG (jevent_post J eG eC zG zC) = event_post (projG J) eG zG.
Proof.
  intros [rvG rvC gs ms br ph lv] eG eC zG zC Hr Hc. destruct eG as [req|ag len prot flags|ag len|ag len prot|? ? ?|?], eC as [req'|ac len' prot' flags'|ac len'|ac len' prot'|? ? ?|?]; cbn in Hr; try contradiction; unfold projG, event_post; cbn.
  - destruct (req =? 0); [reflexivity|]. destruct (zG =? req); [|reflexivity].
    destruct ph; destruct br as [[[bG bC] l]|]; cbn; reflexivity.
  - destruct Hr as (-> & -> & -> & _). destruct (Z.land flags MAP_FIXED =? 0); [|reflexivity].
    destruct (is_err zG); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - cbn. rewrite map_gG_remove. reflexivity.
  - unfold mprot_okb. destruct ((zG =? 0) || (zG =? TWO64 - ENOSYS)); cbn; [|reflexivity]. rewrite map_mG_bump. reflexivity.
Qed.

(* [comment removed for export] *)
Definition jg_coherent (aG aC : Z) (l : list (Z * Z * Z)) : Prop :=
  forall g, In g l -> (fst (fst g) = aG <-> snd (fst g) = aC).
Definition jm_coherent (aG aC : Z) (l : list (Z * Z * Z * Z)) : Prop :=
  forall bG bC n k, In (bG, bC, n, k) l -> (bG + (1 + k) * PGSZ = aG <-> bC + (1 + k) * PGSZ = aC).

Lemma map_gC_remove : forall aG aC l, jg_coherent aG aC l -> map gC (jg_remove aG l) = g_remove aC (map gC l).
Proof.
  induction l as [|[[bG bC] n] l IH]; intros Hc; [reflexivity|]. cbn.
  pose proof (Hc (bG, bC, n) (or_introl eq_refl)) as E. cbn in E.
  destruct (Z.eqb_spec bG aG) as [E1|N1]; destruct (Z.eqb_spec bC aC) as [E2|N2]; try reflexivity.
  - exfalso. apply N2. apply E. exact E1.
  - exfalso. apply N1. apply E. exact E2.
  - cbn. rewrite IH; [reflexivity|]. intros g Hg. apply Hc. right. exact Hg.
Qed.

Lemma map_mC_bump : forall aG aC l, jm_coherent aG aC l -> map mC (map (jbump aG) l) = map (bump_meta aC) (map mC l).
Proof.
  induction l as [|[[[bG bC] n] k] l IH]; intros Hc; [reflexivity|]. cbn.
  pose proof (Hc bG bC n k (or_introl eq_refl)) as E.
  rewrite IH by (intros ? ? ? ? Hin; apply (Hc _ _ _ _ (or_intror Hin))). unfold bump_meta.
  destruct (Z.eqb_spec (bG + (1 + k) * PGSZ) aG) as [E1|N1]; destruct (Z.eqb_spec (bC + (1 + k) * PGSZ) aC) as [E2|N2]; try reflexivity.
  - exfalso. apply N2. apply E. exact E1.
  - exfalso. apply N1. apply E. exact E2.
Qed.

Lemma projC_post : forall J eG eC zG zC,
  jev_rel J eG eC -> same_class eG eC zG zC = true ->
  (forall aG aC len len', eG = EMunmap aG len -> eC = EMunmap aC len' -> jg_coherent aG aC (j_groups J)) ->
  (forall aG aC len len' p p', eG = EMprotect aG len p -> eC = EMprotect aC len' p' -> jm_coherent aG aC (j_metas J)) ->
  projC (jevent_post J eG eC zG zC) = event_post (projC J) eC zC.
Proof.
  intros [rvG rvC gs ms br ph lv] eG eC zG zC Hr Hc Hg Hm. cbn in Hg, Hm. destruct eG as [req|ag len prot flags|ag len|ag len prot|? ? ?|?], eC as [req'|ac len' prot' flags'|ac len'|ac len' prot'|? ? ?|?]; cbn in Hr; try contradiction; unfold projC, event_post; cbn; cbn in Hc.
  - assert (E0 : (req =? 0) = (req' =? 0)).
    { destruct Hr as [(-> & -> & _)|[(cG & cC & _ & -> & -> & P1 & P2)|(bG & bC & l & _ & _ & -> & -> & P1 & P2)]]; [reflexivity| |];
      rewrite !(proj2 (Z.eqb_neq _ 0)) by lia; reflexivity. }
    rewrite <- E0. destruct (req =? 0); [reflexivity|].
    apply Bool.eqb_prop in Hc. rewrite <- Hc. destruct (zG =? req); [|reflexivity].
    destruct ph; destruct br as [[[bG bC] l]|]; cbn; reflexivity.
  - destruct Hr as (-> & -> & -> & _). unfold is_fixed in Hc. destruct (Z.land flags MAP_FIXED =? 0); cbn in Hc; [|reflexivity].
    apply Bool.eqb_prop in Hc. rewrite <- Hc. destruct (is_err zG); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - cbn. rewrite (map_gC_remove ag ac) by (eapply Hg; reflexivity). reflexivity.
  - apply Bool.eqb_prop in Hc. unfold mprot_okb in Hc |- *. rewrite <- Hc. destruct ((zG =? 0) || (zG =? TWO64 - ENOSYS)); cbn; [|reflexivity].
    rewrite (map_mC_bump ag ac) by (eapply Hm; reflexivity). reflexivity.
Qed.
