(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext
  MI_Pres2 MI_WAMeta2 MI_Sim MI_Contracts KLink KLink3 KBudgetB1 KBudgetB2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint tall {R} (P : R -> Prop) (t : M R) : Prop :=
  match t with SRet r => P r | SVis _ k => forall z, tall P (k z) end.

Lemma tall_follow {R} (P : R -> Prop) : forall (t : M R) ans r, tall P t -> follow t ans = Some r -> P r.
Proof.
  induction t as [r0|e k IH]; intros ans r H F; cbn in *.
  - congruence.
  - destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; exact (IH a ans r (H a) F).
Qed.

Lemma tall_sbind {A B} (P : A -> Prop) (Q : B -> Prop) : forall (t : M A) (f : A -> M B),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (sbind t f).
Proof. induction t as [r|e k IH]; intros f H Hf; cbn in *; [apply Hf; exact H| intros z; apply IH; [apply H| exact Hf]]. Qed.

Section ARFree.
Variable A : gmap aptr area.
Let AP : mstate -> Prop := fun s => s_areas s = A.
Context {R : Type}.
Variable P : R -> Prop.
Implicit Types (k : mstate -> mapinfo -> M R) (bail : M R).

Lemma ta_undef u (k0 : Z -> M R) : tall P (k0 0) -> (forall z, tall P (k0 z)) -> tall P (SVis (EUndef u) k0).
Proof. intros. cbn. assumption. Qed.

Lemma ta_guard tag c (t bail : M R) : tall P t -> tall P bail -> tall P (guard tag c t bail).
Proof. intros. unfold guard. destruct c; [assumption| cbn; auto]. Qed.

Lemma ta_queue h m st (k1 : mstate -> M R) bail :
  AP st -> (forall st', AP st' -> tall P (k1 st')) -> tall P bail -> tall P (queue h m st k1 bail).
Proof.
  intros HA Hk Hb. unfold queue. apply ta_guard; [| exact Hb]. apply ta_guard; [| exact Hb].
  destruct (get_head st h); [destruct (m_prev _)|]; apply Hk; unfold AP in *; destruct h; cbn; autorewrite with mst; exact HA.
Qed.

Lemma ta_free_meta m st (k1 : mstate -> M R) bail :
  AP st -> (forall st', AP st' -> tall P (k1 st')) -> tall P bail -> tall P (free_meta m st k1 bail).
Proof. intros HA Hk Hb. unfold free_meta. apply ta_queue; [unfold AP in *; autorewrite with mst; exact HA| exact Hk| exact Hb]. Qed.

Lemma ta_activate_group m st (k2 : mstate -> Z -> M R) bail :
  AP st -> (forall st' z, AP st' -> tall P (k2 st' z)) -> tall P bail -> tall P (activate_group m st k2 bail).
Proof. intros HA Hk Hb. unfold activate_group. apply ta_guard; [| exact Hb]. apply Hk. unfold AP in *; autorewrite with mst; exact HA. Qed.

Lemma ta_dec_slots st p (k3 : aptr -> Z -> M R) bail :
  (forall g i, tall P (k3 g i)) -> tall P bail -> tall P (dec_slots st p k3 bail).
Proof. intros Hk Hb. unfold dec_slots. destruct (_ !! _) as [[g i]|]; [apply Hk| cbn; auto]. Qed.

Lemma AP_dequeue h m st : AP st -> AP (dequeue h m st).
Proof. unfold AP. intros HA. unfold dequeue. destruct h; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _)| |destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _)|]; cbn; autorewrite with mst; exact HA. Qed.

Lemma ta_free_group rec st g k bail :
  AP st ->
  (forall st1 m idx k', AP st1 -> (forall st3 mi, AP st3 -> tall P (k' st3 mi)) -> tall P (rec st1 m idx k' bail)) ->
  (forall st' mi, AP st' -> tall P (k st' mi)) -> tall P bail ->
  tall P (free_group R dec_slots rec st g k bail).
Proof.
  intros HA Hrec Hk Hb. unfold free_group.
  destruct (m_mem _) as [p|]; [| cbn; auto].
  set (st1 := del_slots _ _ _ _).
  assert (HA1 : AP st1) by (subst st1; unfold AP in *; destruct (_ <? _); autorewrite with mst; exact HA).
  destruct (negb _).
  - apply ta_free_meta; [unfold AP in *; autorewrite with mst; exact HA1| intros; apply Hk; assumption| exact Hb].
  - apply ta_dec_slots; [| exact Hb]. intros g' i. apply Hrec; [exact HA1|]. intros st3 mi H3. apply ta_free_meta; [exact H3| intros; apply Hk; assumption| exact Hb].
Qed.

Lemma ta_nontrivial_free fuel : forall st g i k bail,
  AP st -> (forall st' mi, AP st' -> tall P (k st' mi)) -> tall P bail ->
  tall P (nontrivial_free dec_slots fuel st g i k bail).
Proof.
  induction fuel as [|f IH]; intros st g i k bail HA Hk Hb; cbn [nontrivial_free]; [cbn; auto|].
  destruct (_ && _).
  - destruct (m_next _).
    + apply ta_guard; [| exact Hb]. destruct (optr_eqb _ _); [destruct (active _ _)|].
      * apply ta_activate_group; [apply AP_dequeue; exact HA| | exact Hb]. intros st' z H'. apply ta_free_group; auto.
      * apply ta_free_group; auto. apply AP_dequeue; exact HA.
      * apply ta_free_group; auto. apply AP_dequeue; exact HA.
    + apply ta_free_group; auto.
  - destruct (_ =? _).
    + apply ta_guard; [| exact Hb]. destruct (negb _).
      * apply ta_queue; [exact HA| | exact Hb]. intros st' H'. apply Hk. unfold AP in *; autorewrite with mst; exact H'.
      * apply Hk. unfold AP in *; autorewrite with mst; exact HA.
    + apply Hk. unfold AP in *; autorewrite with mst; exact HA.
Qed.
End ARFree.

Lemma ta_free_tail st g idx : tall (fun s => s_areas s = s_areas st) (free_tail dec_slots st g idx).
Proof.
  unfold free_tail. apply ta_guard; [| cbn; reflexivity]. destruct (negb _); [cbn; autorewrite with mst; reflexivity|].
  apply (ta_nontrivial_free (s_areas st)); [reflexivity| | cbn; reflexivity].
  intros st2 [[base len]|] H2; [| exact H2]. destruct (negb _); [| exact H2].
  cbn. intros z. destruct (munmap_answer_ok z); cbn; [autorewrite with mst; exact H2| auto].
Qed.

Lemma cfree_areas cs c ans cs' : follow (cfree cs (Some c)) ans = Some cs' -> s_areas cs' = s_areas cs.
Proof.
  intros F. apply (tall_follow (fun s => s_areas s = s_areas cs) (cfree cs (Some c)) ans cs'); [| exact F].
  unfold cfree. destruct (_ !! _) as [[g idx]|]; [| cbn; reflexivity].
  apply (tall_sbind (fun s => s_areas s = s_areas cs)); [apply ta_free_tail|]. intros a Ha. cbn. rewrite <- Ha. apply (proj1 (proj2 (proj2 (proj2 (proj2 (strip_fields a)))))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ABND : Z := 48 + 49 * (HCNT + 48) + Z.of_nat FUEL.
Definition areas_cap (st : mstate) : Prop := NSLOTS * (Z.of_nat (size (s_areas st)) - 1) <= ABND.

Definition HSIM (cs : mstate) (L : mled) : Prop :=
  exists st BL LS, strip st = cs /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ areas_cap st.

Lemma live_cnt_BL st L BL LS : INVL x0 st L BL LS -> ld_live L = map bslot BL -> live_cnt_ok L -> Z.of_nat (length BL) + 1 <= HCNT.
Proof.
  intros INV LIVE (Xl & COV & HX). pose proof INV as (_ & _ & _ & _ & _ & IS & _).
  pose proof (count_incl (map bslot BL) Xl (proj1 (NoDup_ListNoDup _) (is_nodup _ _ _ IS)) ltac:(intros c Hc; apply COV; rewrite LIVE; exact Hc)) as C.
  rewrite map_length in C. lia.
Qed.

Theorem hreach_sim cs L : hreach cs L -> HSIM cs L.
Proof.
  induction 1 as [secret resv Hs|cs L n L' cs' r CR IH Hn HL CP|cs L c L' cs' CR IH Hc CP].
  - exists (minit secret resv), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; exact Hs|]. split; [reflexivity|].
    unfold areas_cap, ABND, HCNT, NSLOTS, FUEL. change (size (s_areas (minit secret resv))) with 0%nat. cbn. lia.
  - destruct IH as (st & BL & LS & <- & INV & LIVE & CAP).
    pose proof (live_cnt_BL st L BL LS INV LIVE HL) as NBL.
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL').
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & AR & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL' in RES, LIVE'.
    assert (CAP' : areas_cap st').
    { unfold areas_cap, NSLOTS in *. destruct AR as [LE|(Xc & stc & Lc & LSc & INVc & FR & AC & IDL & ZB & _ & _ & SZ)]; [lia|].
      pose proof (carve_count Xc stc Lc BL LSc INVc FR AC) as CC. rewrite ZB in CC. cbn [length] in CC.
      unfold ABND, HCNT, FUEL, DEPTH, NSLOTS in *. change (Z.to_nat 101) with 101%nat in CC. lia. }
    destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
    + destruct RES as (off & LS' & Epf & Hoff & INV' & NI & _).
      exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. split; [| exact CAP']. cbn. rewrite LIVE', LIVE. reflexivity.
    + destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. split; [| exact CAP']. rewrite LIVE'. exact LIVE.
  - destruct IH as (st & BL & LS & <- & INV & LIVE & CAP).
    rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL').
    pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
    rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
    destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
    pose proof (cfree_areas _ _ _ _ Hf) as EA.
    rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL' in INV', LIVE'.
    exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. split.
    + cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
    + unfold areas_cap, NSLOTS in *. cbn in EA. rewrite EA. exact CAP.
Qed.

(* [comment removed for export] *)
Lemma areas_cap_num st : areas_cap st -> Z.of_nat (size (s_areas st)) <= 2012.
Proof. unfold areas_cap, ABND, HCNT, NSLOTS, FUEL. cbn [Z.of_nat Pos.of_succ_nat]. lia. Qed.
