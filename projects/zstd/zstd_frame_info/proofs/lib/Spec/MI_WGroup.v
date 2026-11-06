(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_Bits MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition TF (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> 12 <= o mod 16.

(* [comment removed for export] *)
Definition TKS (st : mstate) (T : N) : Prop :=
  forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Definition DOMS (st0 st : mstate) : Prop :=
  forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup.

Lemma TKS_of X st L BL LS : INVL X st L BL LS -> TKS st (s_tick st).
Proof. intros INV. exact (ish_ticks _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.
Lemma DOMS_of X st L BL LS : INVL X st L BL LS -> DOMS st st.
Proof. intros INV. exact (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

Lemma TF_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF (set_tick t st).
Proof.
  intros TK LT rid sh o v t' Hsh Ho E. cbn in E, Hsh. subst t'. destruct (TK rid sh Hsh) as (C & _ & _). destruct (C o v t Ho) as [_ LE]. exfalso. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59308516196.12000007S2LT2LE".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma get_shadow_cells_some st rid o c : r_cells (get_shadow st rid) !! o = Some c -> exists sh, s_shadow st !! rid = Some sh /\ r_cells sh !! o = Some c.
Proof.
  unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn; [intros H; exists sh; auto|]. rewrite lookup_empty. discriminate.
Qed.

Lemma TF_wr8 st q v : TF st -> 12 <= snd q mod 16 -> TF (wr8 q v st).
Proof.
  intros H Hq rid sh o w t. rewrite (wr8_shadow_lookup st q v rid). destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
  intros E. inversion E. subst sh. cbn. destruct (Z.eq_dec o (snd q)) as [->|NEo].
  - rewrite lookup_insert_eq. intros _ _. exact Hq.
  - rewrite lookup_insert_ne by congruence. intros Ho Et. destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
Qed.

Lemma TF_hdr_havoc st b : TF st -> TF (hdr_havoc b st).
Proof.
  intros H rid sh o w t. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn. intros Ho Et.
    destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
  - rewrite lookup_insert_ne by congruence. apply H.
Qed.

Lemma TF_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF st -> TF st'.
Proof. intros E1 E2 H rid sh o v t. rewrite E1, E2. apply H. Qed.

Lemma TKS_hdr_havoc st b : TKS st (s_tick st) -> TKS (hdr_havoc b st) (s_tick st).
Proof.
  intros TK rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn.
  assert (G : forall P : shadow -> Prop, (forall sh, s_shadow st !! fst b = Some sh -> P sh) -> P shadow0 -> P (get_shadow st (fst b))).
  { intros P H1 H0. unfold get_shadow. destruct (s_shadow st !! fst b) eqn:Es; [apply H1; reflexivity| exact H0]. }
  split; [| split].
  - apply (G (fun sh => forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (TK _ _ Hsh))| intros o w t Ho; cbn in Ho; rewrite lookup_empty in Ho; discriminate].
  - intros u hl ch. destruct (Z.eq_dec u (snd b / 16)) as [->|NEu].
    + rewrite lookup_insert_eq. intros E2. inversion E2. subst hl. unfold hav_add. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010;131666670.6000001S".
intros [<-|Hin]; [cbn; lia|].
      apply (proj2 (list_elem_of_In _ _)) in Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin.
      revert Hin. apply (G (fun sh => In ch (default [] (r_hav sh !! (snd b / 16))) -> (snd ch <= s_tick st)%N)).
      * intros sh Hsh Hin. destruct (r_hav sh !! (snd b / 16)) as [hl0|] eqn:Eh; cbn in Hin; [| destruct Hin]. exact (proj1 (proj2 (TK _ _ Hsh)) _ hl0 ch Eh Hin).
      * cbn. rewrite lookup_empty. cbn. tauto.
    + rewrite lookup_insert_ne by congruence.
      apply (G (fun sh => r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (proj2 (TK _ _ Hsh)) u hl ch)|].
      cbn. rewrite lookup_empty. discriminate.
  - apply (G (fun sh => forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N)); [intros sh Hsh; exact (proj2 (proj2 (TK _ _ Hsh)))|].
    intros pg t Hp. cbn in Hp. rewrite lookup_empty in Hp. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma DOMS_wr8 st0 st q v : DOMS st0 st -> (exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wr8 q v st).
Proof. intros D Hq. unfold DOMS. apply (wr8_dom st q v (fun rid => exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup) D Hq). Qed.
Lemma DOMS_hdr_havoc st0 st b : DOMS st0 st -> (exists r, s_regions st0 !! fst b = Some r /\ r_kind r = RKGroup) -> DOMS st0 (hdr_havoc b st).
Proof.
  intros D Hb rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [intros _; exact Hb|].
  rewrite lookup_insert_ne by congruence. apply D.
Qed.
Lemma TKS_wr8 st q v T : (s_tick st <= T)%N -> TKS st T -> TKS (wr8 q v st) T.
Proof. intros LE TK. exact (wr8_tks st q v T LE TK). Qed.

(* [comment removed for export] *)
Lemma sh_ticks_of st rid : TKS st (s_tick st) -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros TK. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - destruct (TK _ _ E) as (_ & A & B). split; [exact A| exact B].
  - split; [intros u hl ch H; rewrite lookup_empty in H; discriminate| intros pg t H; rewrite lookup_empty in H; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wrs (l : list (aptr * Z)) (st : mstate) : mstate :=
  match l with [] => st | (q, v) :: l' => wrs l' (wr8 q v st) end.

Lemma wrs_app l1 l2 st : wrs (l1 ++ l2) st = wrs l2 (wrs l1 st).
Proof. revert st. induction l1 as [|[q v] l1 IH]; intros st; cbn; [reflexivity| apply IH]. Qed.

Section WRS.

#[using="Type"] Lemma wrs_ctrl l st : ctrl_eq st (wrs l st) /\ s_tick (wrs l st) = s_tick st.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st; cbn; [split; [apply ctrl_eq_refl| reflexivity]|].
  destruct (IH (wr8 q v st)) as [C T]. split; [eapply ctrl_eq_trans; [apply ctrl_eq_wr8| exact C]| rewrite T; reflexivity].
Qed.

#[using="Type"] Lemma wrs_read_other l st q : ~ In q (map fst l) ->
  cell_read (get_shadow (wrs l st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  revert st. induction l as [|[q' v] l IH]; intros st Hn; cbn; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply cell_read_wr8_other. cbn in Hn. intros ->. apply Hn. left. reflexivity.
Qed.

#[using="Type"] Lemma wrs_TKS l st T : (s_tick st <= T)%N -> TKS st T -> TKS (wrs l st) T.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st LE TK; cbn; [exact TK|].
  apply IH; [cbn; exact LE|]. apply TKS_wr8; assumption.
Qed.

#[using="Type"] Lemma wrs_DOMS l st0 st : DOMS st0 st -> (forall q, In q (map fst l) -> exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st D H; cbn; [exact D|].
  apply IH; [apply DOMS_wr8; [exact D| apply H; left; reflexivity]| intros q' Hq'; apply H; right; exact Hq'].
Qed.

#[using="Type"] Lemma wrs_TF l st : TF st -> (forall q, In q (map fst l) -> 12 <= snd q mod 16) -> TF (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st H Hl; cbn; [exact H|].
  apply IH; [apply TF_wr8; [exact H| apply Hl; left; reflexivity]| intros q' Hq'; apply Hl; right; exact Hq'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wrs_read_last l1 q v l2 st :
  ~ In q (map fst l2) -> TKS st (s_tick st) ->
  cell_read (get_shadow (wrs (l1 ++ (q, v) :: l2) st) (fst q)) (snd q) = Known (Z.land v 255).
Proof.
  intros Hn TK. rewrite wrs_app. cbn. rewrite wrs_read_other by exact Hn.
  destruct (wrs_ctrl l1 st) as [C T].
  apply cell_read_wr8_same. apply sh_ticks_of. rewrite T. Local Ltac2 Set LiaHints.tbl := fun () => "0010;129851848.9000003S1T".
apply wrs_TKS; [lia| exact TK].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WRS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zlist (p : aptr) (size : Z) (i : Z) (n : nat) : list (aptr * Z) :=
  match n with O => [] | S n' => (aadd p (UNIT + i * size - 4), 0) :: zlist p size (i + 1) n' end.

Lemma zero_hdrs_wrs p size i n st : zero_hdrs p size i n st = wrs (zlist p size i n) st.
Proof. revert i st. induction n as [|n IH]; intros; cbn; [reflexivity| apply IH]. Qed.

Lemma in_zlist p size q : forall n i, In q (map fst (zlist p size i n)) <-> exists k, i <= k < i + Z.of_nat n /\ q = aadd p (UNIT + k * size - 4).
Proof.
  induction n as [|n IH]; intros i; cbn.
  - Local Ltac2 Set LiaHints.tbl := fun () => "0040=21405571751.842478331863.754363954658.559308586510.600000700;00<00@S2Hk2NES2HkSS2Hk".
split; [tauto| intros (k & Hk & _); lia].
  - rewrite IH. split.
    + intros [<-|(k & Hk & ->)]; [exists i; split; [lia| reflexivity]| exists k; split; [lia| reflexivity]].
    + intros (k & Hk & ->). destruct (Z.eq_dec k i) as [->|NE]; [left; reflexivity| right; exists k; split; [lia| reflexivity]].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma zlist_split p size i n k : i <= k < i + Z.of_nat n ->
  exists l1 l2, zlist p size i n = l1 ++ (aadd p (UNIT + k * size - 4), 0) :: l2
    /\ (forall q, In q (map fst l2) -> exists k', k < k' < i + Z.of_nat n /\ q = aadd p (UNIT + k' * size - 4)).
Proof.
  revert i. Local Ltac2 Set LiaHints.tbl := fun () => "0040>21405571751.8 24375032405.1532384910131.8 53512245611.5 00000700?00G00KS2Hk2NES2Hk3Hk'S2Hk3Hk'S2Hk".
induction n as [|n IH]; intros i Hk; [cbn in Hk; lia|].
  cbn. destruct (Z.eq_dec k i) as [->|NE].
  - exists [], (zlist p size (i + 1) n). split; [reflexivity|]. intros q Hq. apply in_zlist in Hq as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
  - destruct (IH (i + 1) ltac:(lia)) as (l1 & l2 & E & H). exists ((aadd p (UNIT + i * size - 4), 0) :: l1), l2.
    rewrite E. split; [reflexivity|]. intros q Hq. destruct (H q Hq) as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (aig idx j size cnt : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let p : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some p.
Hypothesis STR : get_stride (MR st g) = UNIT * size_class j.
Hypothesis SZ16 : size mod 16 = 0.
Hypothesis SZ0 : 16 <= size.
Hypothesis CNT : 1 <= cnt.
Hypothesis FIT : UNIT + cnt * size <= get_stride (MR st g).
Hypothesis HTF : TF st.
Let q : Z := (snd p - (snd bg + UNIT)) / UNIT.
Let st' := nest_layout st g idx j size cnt.

(* [comment removed for export] *)
Definition nl_list : list (aptr * Z) :=
  [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5);
   (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ zlist p size 0 (Z.to_nat (cnt + 1)).

#[using="aig Hg"] Lemma g_hosts : hosts st bg g. Proof. exists aig. exact Hg. Qed.
#[using="X L BL LS aig INV Hg"] Lemma p_eq : slot_start' (MR st g) idx = p. Proof. unfold p. apply (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ g_hosts). Qed.
#[using="X L BL LS aig INV Hg"] Lemma bg_gbase : gbase (MR st g) = bg. Proof. apply (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ g_hosts). Qed.

#[using="X L BL LS aig INV Hg STR"] Lemma nl_eq : st' = wrs nl_list st.
Proof.
  unfold st', nest_layout, enframe_at. fold (MR st g). cbn [negb Z.eqb].
  change (aadd (default (0%N, 0) (m_mem (MR st g))) (UNIT + get_stride (MR st g) * idx)) with (slot_start' (MR st g) idx).
  rewrite p_eq. unfold set_size.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>16828152918.25000001S".
replace (snd (aadd p (get_stride (MR st g) - IB)) - snd p - (UNIT * size_class j - IB)) with 0
    by (unfold aadd; cbn [fst snd]; rewrite STR; unfold UNIT, IB; lia).
  change (5 <=? 0) with false. change (0 =? 0) with true. cbn [negb].
  unfold nl_list. rewrite wrs_app. cbn [wrs app]. rewrite zero_hdrs_wrs. unfold wr16.
  unfold q. fold (gbase (MR st g)). rewrite bg_gbase. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="X L BL LS aig size INV Hg Hidx SZ0 q"] Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  unfold p. cbn. unfold sstart. rewrite bg_gbase.
  pose proof (g_align _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as [_ A].
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [_ SM].
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>24890737227.2724891063415.28000001002SS".
pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2.
  unfold UNIT in *. rewrite A in D1. rewrite SM in D2.
  replace (snd bg + 16 + get_stride (MR st g) * idx) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * idx) * 16) by nia.
  apply Z_mod_mult.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st g bg idx size p q"] Lemma res16 a d : a mod 16 = 0 -> (a + d) mod 16 = d mod 16.
Proof. intros H. rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.

#[using="X L BL LS aig j INV Hg Hidx STR SZ16 SZ0 CNT FIT"] Lemma nl_residues r : In r (map fst nl_list) -> 12 <= snd r mod 16.
Proof.
  pose proof p_mod16 as PM. clearbody p. unfold nl_list. rewrite map_app, in_app_iff. unfold aadd. cbn [map fst snd In]. intros [H|H].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0060>21353308612.2624890856233.2841060744883.2642600000628.2659826176747.2863283482408.2800000A00E00V00g00k01?S3STR3SZ03CNT3FITS2HkS3STR3SZ03CNT3FITS3STR3SZ03CNT3FITS2HkS3STR3SZ03CNT3FIT2Hk".
destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; rewrite <- ?Z.add_assoc, (res16 _ _ PM); cbn; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [snd]. rewrite (res16 _ _ PM). unfold UNIT.
    replace (16 + k * size - 4) with (k * size + 12) by lia. rewrite res16; [cbn; lia|].
    rewrite Z.mul_mod, SZ16, Z.mul_0_r by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="X L BL LS aig j INV Hg STR SZ16 SZ0 CNT FIT"] Lemma nl_in_T r : In r (map fst nl_list) ->
  inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r \/ r = (fst bg, sstart (MR st g) (idx + 1) - 4).
Proof.
  unfold nl_list. rewrite map_app, in_app_iff. rewrite sstart_succ. unfold inT, p, aadd. cbn [map fst snd In]. intros [H|H].
  - left. pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [SG _].
    Local Ltac2 Set LiaHints.tbl := fun () => "0040>31195465760.2733753686765.2651018389571.2958554180386.2800000800<00Z00aS3CNT2HkS2SGS3STR4SZ163SZ03CNT3FIT2Hk2NE1HS3SZ01E".
destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold UNIT in *; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [fst snd]. unfold UNIT in *. rewrite Z2Nat.id in Hk by lia.
    destruct (Z.eq_dec (16 + k * size) (get_stride (MR st g))) as [E|NE].
    + right. unfold aadd. cbn [fst snd]. f_equal. lia.
    + left. unfold aadd. cbn [fst snd]. split; [reflexivity|]. assert (k * size <= cnt * size) by nia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="X L BL LS aig j INV Hg STR SZ16 SZ0 CNT FIT"] Lemma nl_regions r : In r (map fst nl_list) -> fst r = fst bg.
Proof. intros H. destruct (nl_in_T r H) as [[E _]| ->]; [exact E| reflexivity]. Qed.

#[using="aig INV Hg Hidx HP STR SZ16 SZ0 CNT FIT HTF"] Theorem nest_layout_ok :
  INVL X st' L BL LS /\ TF st' /\ ctrl_eq st st' /\ s_tick st' = s_tick st
  /\ known st' (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st' (aadd p (-2)) (Z.land q 255) /\ known st' (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr q 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st' (aadd p (UNIT + k * size - 4)) 0)
  /\ (forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
        cell_read (get_shadow st' (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
Proof.
  rewrite nl_eq. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (wrs_ctrl nl_list st) as [CE TK].
  pose proof (TKS_of _ _ _ _ _ INV) as TK0. pose proof (DOMS_of _ _ _ _ _ INV) as DM0.
  assert (RD : forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
        cell_read (get_shadow (wrs nl_list st) (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
  { intros r Hr. destruct (in_dec aptr_eq_dec r (map fst nl_list)) as [Hin|Hn]; [| apply wrs_read_other; exact Hn].
    destruct (nl_in_T r Hin) as [HT| ->]; [exfalso; exact (Hr HT)|].
    (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "00?0>134015061.41  18004349237.4031193368676.4831195465760.4631195522813.4131195555839.4141226676207.4055310823023.4659308874064.4659309024362.4059310683722.4859314873579.4359314955108.456078919026.38 61929033212.4100000400?00K00S00^00f01101801?01Q01Y01j02002902AS2TKS3FIT2TK2EkS3CNT2TK3Hk'S3CNT2TKS3CNT2TK2HkS3CNT2TKS3FIT2TK2EkS2TK2HkS2TK2Z1S3SZ03CNT3FIT2TK1ES2TK3Hk'S3SZ03FIT2TK2Ek1HS2TK1ES4Hidx2TKS3CNT2TK".
pose proof (ish_hdr0 _ _ ISH bg g (idx + 1) g_hosts ltac:(unfold cnt_of; lia)) as K0. unfold known, SHd, IB in K0. cbn [fst snd] in K0 |- *. rewrite K0.
    assert (E : (fst bg, sstart (MR st g) (idx + 1) - 4) = aadd p (UNIT + cnt * size - 4) /\ UNIT + cnt * size = get_stride (MR st g)).
    { unfold nl_list in Hin. rewrite map_app in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - exfalso. cbn [map fst In] in Hin. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
        destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold p, aadd in E; cbn [fst snd] in E; rewrite sstart_succ in E; unfold UNIT in *; lia.
      - apply in_zlist in Hin as (k & Hk & Ek). rewrite Z2Nat.id in Hk by lia. apply (f_equal snd) in Ek. unfold p, aadd in Ek. cbn [fst snd] in Ek.
        rewrite sstart_succ in Ek. destruct (Z.eq_dec k cnt) as [->|NEk].
        + split; [unfold p, aadd; cbn [fst snd]; rewrite sstart_succ; f_equal; unfold UNIT in *; lia| unfold UNIT in *; lia].
        + exfalso. assert (k * size <= (cnt - 1) * size) by nia. unfold UNIT in *. lia. }
    destruct E as [E1 E2]. apply (f_equal snd) in E1. cbn [snd] in E1. rewrite E1.
    destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) cnt ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & EZ & Hl2).
    change (cell_read (get_shadow (wrs nl_list st) (fst (aadd p (UNIT + cnt * size - 4)))) (snd (aadd p (UNIT + cnt * size - 4))) = Known (Z.land 0 255)).
    unfold nl_list. rewrite EZ.
    rewrite (app_assoc _ l1) || rewrite app_assoc.
    apply wrs_read_last; [| exact TK0].
    intros Hin2. destruct (Hl2 _ Hin2) as (k' & Hk' & _). rewrite Z2Nat.id in Hk' by lia. lia. }
  pose proof (is_part _ _ _ IS _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite p_eq, HP in P5. unfold one5 in P5.
  assert (NH : s_groups st !! p = None).
  { destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (NB : forall k, In k BL -> bslot k <> p).
  { intros k Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk. }
  assert (REG : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hg).
  split; [| split; [| split; [exact CE| split; [exact TK|]]]].
  - split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
    split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
    split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
    apply (inv_SH_write_T X st (wrs nl_list st) BL LS IM IG IS ISH g bg idx g_hosts Hidx NH NB CE TK RD).
    + apply wrs_DOMS; [exact DM0|]. intros r Hr. rewrite (nl_regions r Hr). exact REG.
    + apply wrs_TKS; [lia| exact TK0].
  - apply wrs_TF; [exact HTF| apply nl_residues].
  - (* [comment removed for export] *)
    assert (KN : forall l1 r v l2, nl_list = l1 ++ (r, v) :: l2 -> ~ In r (map fst l2) -> known (wrs nl_list st) r (Z.land v 255)).
    { intros l1 r v l2 E Hn. unfold known, SHd. rewrite E. apply wrs_read_last; [exact Hn| exact TK0]. }
    pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
    assert (ZL : forall r, In r (map fst (zlist p size 0 (Z.to_nat (cnt + 1)))) -> snd p + 12 <= snd r).
    { intros r Hr. apply in_zlist in Hr as (k & Hk & ->). cbn. unfold UNIT. nia. }
    split; [| split; [| split; [| split; [| exact RD]]]].
    + apply (KN [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5)] (aadd p (-3)) _ (zlist p size 0 (Z.to_nat (cnt + 1))) eq_refl).
      intros Hin. pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + rewrite <- (Z.land_assoc q 255 255 : Z.land (Z.land q 255) 255 = Z.land q (Z.land 255 255)) || idtac.
      replace (Z.land q 255) with (Z.land (Z.land q 255) 255) by (rewrite <- Z.land_assoc; reflexivity).
      replace (Z.land (Z.land q 255) 255) with (Z.land q 255) by (rewrite <- Z.land_assoc; reflexivity).
      apply (KN [] (aadd p (-2)) q _ eq_refl).
      cbn [map fst app]. intros [E|[E|[E|[E|Hin]]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + apply (KN [(aadd p (-2), q)] (aadd (aadd p (-2)) 1) (Z.shiftr q 8) _ eq_refl).
      cbn [map fst app]. intros [E|[E|[E|Hin]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + intros k Hk. destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) k ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & E & Hl2).
      change (known (wrs nl_list st) (aadd p (UNIT + k * size - 4)) (Z.land 0 255)).
      apply (KN ([(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5); (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ l1) _ 0 l2).
      * unfold nl_list. rewrite E. rewrite <- app_assoc. reflexivity.
      * intros Hin. destruct (Hl2 _ Hin) as (k' & Hk' & E'). unfold aadd in E'. apply (f_equal snd) in E'. cbn in E'. unfold UNIT in E'. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End NL.
