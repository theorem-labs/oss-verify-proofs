(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Lia.
From Stdlib Require Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Module MI_Bits.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* [comment removed for export] *)
Lemma sub_bit_ldiff f i : 0 <= f -> 0 <= i -> Z.testbit f i = true -> f - 2 ^ i = Z.ldiff f (2 ^ i).
Proof.
  intros Hf Hi Hb.
  assert (E : f = Z.lor (Z.ldiff f (2 ^ i)) (2 ^ i)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec i n) as [<-|NE]; [rewrite Hb; reflexivity|]. cbn. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity. }
  assert (D : Z.land (Z.ldiff f (2 ^ i)) (2 ^ i) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec i n); cbn; [rewrite Bool.andb_false_r| rewrite Bool.andb_false_r]; reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as A. rewrite (Z.lxor_lor _ _ D) in A. rewrite <- E in A. lia.
Qed.

Lemma testbit_sub_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = true ->
  Z.testbit (f - 2 ^ i) j = Z.testbit f j && negb (i =? j).
Proof.
  intros Hf Hi Hj Hb. rewrite (sub_bit_ldiff f i Hf Hi Hb), Z.ldiff_spec, Z.pow2_bits_eqb by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lowbit_idiom m : 0 < m ->
  exists k, 0 <= k /\ lowbit m = 2 ^ k /\ ctz32 (lowbit m) = k /\ Z.testbit m k = true
    /\ 0 <= m - lowbit m /\ (forall j, 0 <= j -> Z.testbit (m - lowbit m) j = Z.testbit m j && negb (k =? j)).
Proof.
  intros Hm. destruct (lowbit_nonzero m Hm) as (k & Hk & E & L). exists k.
  pose proof (lowbit_testbit m k Hk E) as Tb.
  split; [exact Hk|]. split; [exact E|]. split; [rewrite E; apply ctz32_pow2; exact Hk|]. split; [exact Tb|].
  rewrite E. split; [lia|]. intros j Hj. apply testbit_sub_bit; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma mask_below m n : 0 <= m -> 0 <= n -> (forall i, 0 <= i -> Z.testbit m i = true -> i <= n) -> m < 2 ^ (n + 1).
Proof. intros Hm Hn H. apply bits_below_bound; [lia| lia|]. intros i Hi Hb. pose proof (H i Hi Hb). lia. Qed.


End CeilWrap.
End MI_Bits.

(* [comment removed for export] *)
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree2.
Module MI_WGroup.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith MI_Bits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

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
  intros TK LT rid sh o v t' Hsh Ho E. cbn in E, Hsh. subst t'. destruct (TK rid sh Hsh) as (C & _ & _). destruct (C o v t Ho) as [_ LE]. exfalso. lia.
Qed.

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
    + rewrite lookup_insert_eq. intros E2. inversion E2. subst hl. unfold hav_add. cbn. intros [<-|Hin]; [cbn; lia|].
      apply (proj2 (list_elem_of_In _ _)) in Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin.
      revert Hin. apply (G (fun sh => In ch (default [] (r_hav sh !! (snd b / 16))) -> (snd ch <= s_tick st)%N)).
      * intros sh Hsh Hin. destruct (r_hav sh !! (snd b / 16)) as [hl0|] eqn:Eh; cbn in Hin; [| destruct Hin]. exact (proj1 (proj2 (TK _ _ Hsh)) _ hl0 ch Eh Hin).
      * cbn. rewrite lookup_empty. cbn. tauto.
    + rewrite lookup_insert_ne by congruence.
      apply (G (fun sh => r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (proj2 (TK _ _ Hsh)) u hl ch)|].
      cbn. rewrite lookup_empty. discriminate.
  - apply (G (fun sh => forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N)); [intros sh Hsh; exact (proj2 (proj2 (TK _ _ Hsh)))|].
    intros pg t Hp. cbn in Hp. rewrite lookup_empty in Hp. discriminate.
Qed.

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

Lemma wrs_ctrl l st : ctrl_eq st (wrs l st) /\ s_tick (wrs l st) = s_tick st.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st; cbn; [split; [apply ctrl_eq_refl| reflexivity]|].
  destruct (IH (wr8 q v st)) as [C T]. split; [eapply ctrl_eq_trans; [apply ctrl_eq_wr8| exact C]| rewrite T; reflexivity].
Qed.

Lemma wrs_read_other l st q : ~ In q (map fst l) ->
  cell_read (get_shadow (wrs l st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  revert st. induction l as [|[q' v] l IH]; intros st Hn; cbn; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply cell_read_wr8_other. cbn in Hn. intros ->. apply Hn. left. reflexivity.
Qed.

Lemma wrs_TKS l st T : (s_tick st <= T)%N -> TKS st T -> TKS (wrs l st) T.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st LE TK; cbn; [exact TK|].
  apply IH; [cbn; exact LE|]. apply TKS_wr8; assumption.
Qed.

Lemma wrs_DOMS l st0 st : DOMS st0 st -> (forall q, In q (map fst l) -> exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st D H; cbn; [exact D|].
  apply IH; [apply DOMS_wr8; [exact D| apply H; left; reflexivity]| intros q' Hq'; apply H; right; exact Hq'].
Qed.

Lemma wrs_TF l st : TF st -> (forall q, In q (map fst l) -> 12 <= snd q mod 16) -> TF (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st H Hl; cbn; [exact H|].
  apply IH; [apply TF_wr8; [exact H| apply Hl; left; reflexivity]| intros q' Hq'; apply Hl; right; exact Hq'].
Qed.

(* [comment removed for export] *)
Lemma wrs_read_last l1 q v l2 st :
  ~ In q (map fst l2) -> TKS st (s_tick st) ->
  cell_read (get_shadow (wrs (l1 ++ (q, v) :: l2) st) (fst q)) (snd q) = Known (Z.land v 255).
Proof.
  intros Hn TK. rewrite wrs_app. cbn. rewrite wrs_read_other by exact Hn.
  destruct (wrs_ctrl l1 st) as [C T].
  apply cell_read_wr8_same. apply sh_ticks_of. rewrite T. apply wrs_TKS; [lia| exact TK].
Qed.
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
  - split; [tauto| intros (k & Hk & _); lia].
  - rewrite IH. split.
    + intros [<-|(k & Hk & ->)]; [exists i; split; [lia| reflexivity]| exists k; split; [lia| reflexivity]].
    + intros (k & Hk & ->). destruct (Z.eq_dec k i) as [->|NE]; [left; reflexivity| right; exists k; split; [lia| reflexivity]].
Qed.

Lemma zlist_split p size i n k : i <= k < i + Z.of_nat n ->
  exists l1 l2, zlist p size i n = l1 ++ (aadd p (UNIT + k * size - 4), 0) :: l2
    /\ (forall q, In q (map fst l2) -> exists k', k < k' < i + Z.of_nat n /\ q = aadd p (UNIT + k' * size - 4)).
Proof.
  revert i. induction n as [|n IH]; intros i Hk; [cbn in Hk; lia|].
  cbn. destruct (Z.eq_dec k i) as [->|NE].
  - exists [], (zlist p size (i + 1) n). split; [reflexivity|]. intros q Hq. apply in_zlist in Hq as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
  - destruct (IH (i + 1) ltac:(lia)) as (l1 & l2 & E & H). exists ((aadd p (UNIT + i * size - 4), 0) :: l1), l2.
    rewrite E. split; [reflexivity|]. intros q Hq. destruct (H q Hq) as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
Qed.

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

Lemma g_hosts : hosts st bg g. Proof. exists aig. exact Hg. Qed.
Lemma p_eq : slot_start' (MR st g) idx = p. Proof. unfold p. apply (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ g_hosts). Qed.
Lemma bg_gbase : gbase (MR st g) = bg. Proof. apply (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ g_hosts). Qed.

Lemma nl_eq : st' = wrs nl_list st.
Proof.
  unfold st', nest_layout, enframe_at. fold (MR st g). cbn [negb Z.eqb].
  change (aadd (default (0%N, 0) (m_mem (MR st g))) (UNIT + get_stride (MR st g) * idx)) with (slot_start' (MR st g) idx).
  rewrite p_eq. unfold set_size.
  replace (snd (aadd p (get_stride (MR st g) - IB)) - snd p - (UNIT * size_class j - IB)) with 0
    by (unfold aadd; cbn [fst snd]; rewrite STR; unfold UNIT, IB; lia).
  change (5 <=? 0) with false. change (0 =? 0) with true. cbn [negb].
  unfold nl_list. rewrite wrs_app. cbn [wrs app]. rewrite zero_hdrs_wrs. unfold wr16.
  unfold q. fold (gbase (MR st g)). rewrite bg_gbase. reflexivity.
Qed.

Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  unfold p. cbn. unfold sstart. rewrite bg_gbase.
  pose proof (g_align _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as [_ A].
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [_ SM].
  pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2.
  unfold UNIT in *. rewrite A in D1. rewrite SM in D2.
  replace (snd bg + 16 + get_stride (MR st g) * idx) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * idx) * 16) by nia.
  apply Z_mod_mult.
Qed.

Lemma res16 a d : a mod 16 = 0 -> (a + d) mod 16 = d mod 16.
Proof. intros H. rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.

Lemma nl_residues r : In r (map fst nl_list) -> 12 <= snd r mod 16.
Proof.
  pose proof p_mod16 as PM. clearbody p. unfold nl_list. rewrite map_app, in_app_iff. unfold aadd. cbn [map fst snd In]. intros [H|H].
  - destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; rewrite <- ?Z.add_assoc, (res16 _ _ PM); now vm_compute.
  - apply in_zlist in H as (k & Hk & ->). cbn [snd]. rewrite (res16 _ _ PM). unfold UNIT.
    replace (16 + k * size - 4) with (k * size + 12) by lia. rewrite res16; [now vm_compute|].
    rewrite Z.mul_mod, SZ16, Z.mul_0_r by lia. reflexivity.
Qed.

Lemma nl_in_T r : In r (map fst nl_list) ->
  inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r \/ r = (fst bg, sstart (MR st g) (idx + 1) - 4).
Proof.
  unfold nl_list. rewrite map_app, in_app_iff. rewrite sstart_succ. unfold inT, p, aadd. cbn [map fst snd In]. intros [H|H].
  - left. pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [SG _].
    destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold UNIT in *; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [fst snd]. unfold UNIT in *. rewrite Z2Nat.id in Hk by lia.
    destruct (Z.eq_dec (16 + k * size) (get_stride (MR st g))) as [E|NE].
    + right. unfold aadd. cbn [fst snd]. f_equal. lia.
    + left. unfold aadd. cbn [fst snd]. split; [reflexivity|]. assert (k * size <= cnt * size) by nia. lia.
Qed.
Lemma nl_regions r : In r (map fst nl_list) -> fst r = fst bg.
Proof. intros H. destruct (nl_in_T r H) as [[E _]| ->]; [exact E| reflexivity]. Qed.

Theorem nest_layout_ok :
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
Qed.
End NL.


End CeilWrap.
End MI_WGroup.

(* [comment removed for export] *)
Module MI_TF2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_WGroup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TW (st : mstate) (P : aptr -> Prop) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> P (rid, o).

Definition TF0 (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> (t < s_tick st)%N.

(* [comment removed for export] *)
Definition PS (st : mstate) (q : aptr) : Prop :=
  exists b m, hosts st b m /\ fst b = fst q /\
    ((exists i, 0 <= i <= cnt_of (MR st m) /\ snd q = sstart (MR st m) i - IB)
     \/ (m_maplen (MR st m) = 0 /\ snd b - 3 <= snd q <= snd b - 1)).

Definition TF2 (st : mstate) : Prop := TW st (PS st).

Lemma TF0_TW st P : TF0 st -> TW st P.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.
Lemma TF0_TF2 st : TF0 st -> TF2 st. Proof. apply TF0_TW. Qed.
Lemma TF0_TF st : TF0 st -> TF st.
Proof. intros H rid sh o v t Hs Hc Ht. exfalso. pose proof (H rid sh o v t Hs Hc). lia. Qed.

Lemma TW_mono st (P P' : aptr -> Prop) : (forall q, P q -> P' q) -> TW st P -> TW st P'.
Proof. intros HP H rid sh o v t Hs Hc Ht. apply HP. eapply H; eassumption. Qed.

Lemma TW_ctrl st st' P : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TW st P -> TW st' P.
Proof. intros E1 E2 H rid sh o v t Hs Hc Ht. rewrite E1 in Hs. rewrite E2 in Ht. eapply H; eassumption. Qed.

Lemma TF0_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF0 st -> TF0 st'.
Proof. intros E1 E2 H rid sh o v t Hs Hc. rewrite E1 in Hs. rewrite E2. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Lemma TF0_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF0 (set_tick t st).
Proof.
  intros TK Ht rid sh o v tk Hs Hc. cbn in Hs |- *. destruct (TK rid sh Hs) as (C & _ & _). destruct (C o v tk Hc) as [_ Hle]. lia.
Qed.

Lemma TF0_hdr_havoc st b : TF0 st -> TF0 (hdr_havoc b st).
Proof.
  intros H rid sh o v t Hs Hc. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st).
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; eassumption.
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; eassumption.
Qed.

Lemma TW_hdr_havoc st b P : TW st P -> TW (hdr_havoc b st) P.
Proof.
  intros H rid sh o v t Hs Hc Ht. unfold hdr_havoc, upd_shadow in Hs. cbn in Hs.
  change (s_tick (hdr_havoc b st)) with (s_tick st) in Ht.
  destruct (N.eq_dec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    unfold get_shadow in Hc. destruct (s_shadow st !! fst b) as [sh0|] eqn:E0; cbn in Hc.
    + eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
    + rewrite lookup_empty in Hc. discriminate.
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [eassumption| eassumption| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wr8' st q v P : TW st P -> P q -> TW (wr8 q v st) P.
Proof.
  intros H Hq rid sh o w t Hs Hc Ht. change (s_tick (wr8 q v st)) with (s_tick st) in Ht.
  unfold wr8, upd_shadow in Hs. cbn in Hs.
  destruct (N.eq_dec rid (fst q)) as [->|NE].
  - rewrite lookup_insert_eq in Hs. inversion Hs; subst; clear Hs. cbn in Hc.
    destruct (Z.eq_dec o (snd q)) as [->|NEo].
    + replace (fst q, snd q) with q by (destruct q; reflexivity). exact Hq.
    + rewrite lookup_insert_ne in Hc by congruence. unfold get_shadow in Hc.
      destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hc; [| rewrite lookup_empty in Hc; discriminate].
      eapply H; [exact E0| exact Hc| first [reflexivity| exact Ht]].
  - rewrite lookup_insert_ne in Hs by congruence. eapply H; [exact Hs| exact Hc| first [reflexivity| exact Ht]].
Qed.

Lemma TW_wrs l : forall st P, TW st P -> (forall q, In q (map fst l) -> P q) -> TW (wrs l st) P.
Proof.
  induction l as [|[q v] l IH]; intros st P H HP; cbn [wrs]; [exact H|].
  apply IH.
  - apply TW_wr8'; [exact H| apply HP; left; reflexivity].
  - intros q' Hq'. apply HP. right. exact Hq'.
Qed.

(* [comment removed for export] *)
Definition geom_kept (st st' : mstate) : Prop :=
  forall b m, hosts st b m -> hosts st' b m /\ (forall i, sstart (MR st' m) i = sstart (MR st m) i)
                              /\ cnt_of (MR st' m) = cnt_of (MR st m) /\ m_maplen (MR st' m) = m_maplen (MR st m).

Lemma geom_kept_refl st : geom_kept st st.
Proof. intros b m H. auto. Qed.
Lemma geom_kept_trans a b c : geom_kept a b -> geom_kept b c -> geom_kept a c.
Proof.
  intros H1 H2 bb m H. destruct (H1 _ _ H) as (Hb & S1 & C1 & M1). destruct (H2 _ _ Hb) as (Hc & S2 & C2 & M2).
  split; [exact Hc|]. split; [intros i; rewrite S2; apply S1|]. split; congruence.
Qed.

Lemma PS_mono st st' q : geom_kept st st' -> PS st q -> PS st' q.
Proof.
  intros GK (b & m & Hm & Hf & ALT). destruct (GK _ _ Hm) as (Hm' & S & C & ML).
  exists b, m. split; [exact Hm'|]. split; [exact Hf|].
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - left. exists i. rewrite C, S. auto.
  - right. rewrite ML. auto.
Qed.

Lemma TF2_kept st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> geom_kept st st' -> TF2 st -> TF2 st'.
Proof.
  intros E1 E2 GK H. unfold TF2. eapply TW_mono; [intros q; apply (PS_mono st st' q GK)|]. exact (TW_ctrl st st' _ E1 E2 H).
Qed.

(* [comment removed for export] *)
Lemma geom_kept_of st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall b m, hosts st b m -> MR st' m = MR st m) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  rewrite (HM _ _ Hm). auto.
Qed.

(* [comment removed for export] *)
Lemma wr8_cells_other st q v rid o : (rid, o) <> q ->
  r_cells (get_shadow (wr8 q v st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  intros NE. unfold get_shadow at 1. rewrite (wr8_shadow_lookup st q v rid).
  destruct (N.eqb_spec rid (fst q)) as [->|NR]; [| reflexivity]. cbn.
  rewrite lookup_insert_ne; [reflexivity|]. intros E. apply NE. rewrite <- E. destruct q; reflexivity.
Qed.

Lemma wrs_cells_other l : forall st rid o, ~ In (rid, o) (map fst l) ->
  r_cells (get_shadow (wrs l st) rid) !! o = r_cells (get_shadow st rid) !! o.
Proof.
  induction l as [|[q v] l IH]; intros st rid o Hn; cbn [wrs]; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply wr8_cells_other. cbn in Hn. intros E. apply Hn. left. symmetry. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INTERIOR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma sstart_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof INV as (_ & _ & IM0 & _ & IG0 & _).
  pose proof (stride_ge X st LS IG0 _ _ Hx) as [SG SM]. destruct (hosts_ok X st LS IG0 _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase X st LS IM0 _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Variables (g bg : aptr) (idx : Z).
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Hypothesis NH : s_groups st !! (fst bg, sstart (MR st g) idx) = None.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma PS_not_interior q :
  PS st q -> fst q = fst bg -> ~ (sstart (MR st g) idx <= snd q < sstart (MR st g) (idx + 1) - IB).
Proof.
  intros (b & m & Hm & Hf & ALT) Hq HI. rewrite Hq in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)].
  - destruct (Z.eq_dec i (cnt_of (MR st m))) as [Ei|NEi].
    + (* [comment removed for export] *)
      assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * pose proof (sstart_mono X st LS IG _ _ (idx + 1) i Hg ltac:(unfold cnt_of in *; lia)). unfold IB in *. lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
    + assert (Hi' : 0 <= i <= m_last_idx (MR st m) + 1) by (unfold cnt_of in *; lia).
      destruct (aptr_eq_dec m g) as [->|NEm].
      * destruct (Z.eq_dec i idx) as [->|NEi2]; [unfold IB in *; lia|].
        destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH g b i Hm Hf Hi' ltac:(right; exact NEi2)); unfold IB in *; lia.
      * destruct (sep_hdr0 _ _ _ _ IM IG IS g bg idx Hg Hidx NH m b i Hm Hf Hi' ltac:(left; exact NEm)); unfold IB in *; lia.
  - (* [comment removed for export] *)
    destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO).
    destruct (g_nest _ _ _ _ _ _ GO Z0) as (p & ip & Hsl & Hfp & _ & _ & _).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as (LVp & Hip & Eb).
    destruct LVp as [bp Hp].
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp) in Eb.
    assert (Hfb : fst bp = fst bg) by (rewrite Eb in Hf; exact Hf).
    assert (Esnd : snd b = sstart (MR st p) ip) by (rewrite Eb; reflexivity).
    assert (NE : p <> g \/ ip <> idx).
    { destruct (aptr_eq_dec p g) as [->|]; [| left; assumption]. right. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hg) as Ebp. rewrite Ebp in Eb. rewrite Eb in Hb. rewrite NH in Hb. discriminate. }
    destruct (sep_h3 _ _ _ _ IM IG IS g bg idx Hg Hidx NH p bp ip Hp Hfb Hip NE); unfold IB in *; lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_interior_old :
  TF2 st -> forall o v t, r_cells (get_shadow st (fst bg)) !! o = Some (v, t) ->
  sstart (MR st g) idx <= o < sstart (MR st g) (idx + 1) - IB -> (t < s_tick st)%N.
Proof.
  intros TF o v t Hc Ho. destruct (get_shadow_cells_some st (fst bg) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst bg) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  exact (PS_not_interior (fst bg, o) (TF _ _ _ _ _ Hs Hc' Et) eq_refl Ho).
Qed.

(* [comment removed for export] *)
Lemma TF2_ghdr_old (p : aptr) :
  TF2 st -> snd p mod 16 = 0 ->
  forall o v t, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, t) -> (t < s_tick st)%N.
Proof.
  intros TF Al o v t Ho Hc. destruct (get_shadow_cells_some st (fst p) o (v, t) Hc) as (sh & Hs & Hc').
  destruct (TKS_of _ _ _ _ _ INV (fst p) sh Hs) as (C & _ & _). destruct (C o v t Hc') as [_ Hle].
  destruct (N.eq_dec t (s_tick st)) as [Et|]; [| lia]. exfalso.
  destruct (TF _ _ _ _ _ Hs Hc' Et) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd p) 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma TF2_TF : TF2 st -> TF st.
Proof.
  intros TF rid sh o v t Hs Hc Ht. destruct (TF _ _ _ _ _ Hs Hc Ht) as (b & m & Hm & Hf & ALT). cbn in Hf.
  destruct ALT as [(i & Hi & E)|(Z0 & R0)]; cbn in *.
  - pose proof (sstart_res b m i Hm) as RS. rewrite <- E in RS. pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. unfold UNIT in A16.
    pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (snd b) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
Qed.
End INTERIOR.


End CeilWrap.
End MI_TF2.

(* [comment removed for export] *)
Module MI_WEnframe.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt MI_TF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).
Lemma fold_all : forallb fold_f (zrange 0 256) = true. Proof. vm_cast_no_check (@eq_refl bool true).  (* [comment removed for export] *) Qed.

Lemma fold_off_le off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
  - pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
    pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
    replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
    apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s_shadow_havoc p n st : 0 < n ->
  s_shadow (havoc p n st) = <[fst p := get_shadow (havoc p n st) (fst p)]> (s_shadow st).
Proof.
  intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
  f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.

Lemma TKS_havoc p n st : snd p mod 16 = 0 -> 0 < n -> TKS st (s_tick st) -> TKS (havoc p n st) (s_tick st).
Proof.
  intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
  pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
  destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
              ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
  split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
  rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
  - exact (proj1 (TK _ _ E0)).
  - intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.

Lemma DOMS_havoc st0 p n st : 0 < n -> DOMS st0 st -> (exists r, s_regions st0 !! fst p = Some r /\ r_kind r = RKGroup) -> DOMS st0 (havoc p n st).
Proof.
  intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.

Lemma havoc_ctrl p n st : ctrl_eq st (havoc p n st) /\ s_tick (havoc p n st) = s_tick st.
Proof. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.

Definition ef_list : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
  ++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
  ++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma enframe_at_eq : enframe_at st g idx n off = (wrs ef_list st, p0).
Proof.
  unfold enframe_at, set_size, ef_list. unfold q, res, p0, e, c, gm, stride, mr.
  (* [comment removed for export] *)
  destruct (off =? 0); cbn beta iota delta [negb];
    match goal with |- context [if negb (?x =? 0) then _ else _] => destruct (x =? 0) end; cbn beta iota delta [negb];
    match goal with |- context [if 5 <=? ?x then _ else _] => destruct (5 <=? x) end; cbn beta iota delta [wr16 wr32 wrs app negb]; reflexivity.
Qed.

Lemma p0_eq : p0 = aadd c (UNIT * off).
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
  match l with
  | [] => acc
  | (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
  end.

Lemma lastw_acc l r v : lastw l r (Some v) = match lastw l r None with Some w => Some w | None => Some v end.
Proof.
  revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
  destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.

Lemma wrs_lastw l : forall st r, TKS st (s_tick st) ->
  cell_read (get_shadow (wrs l st) (fst r)) (snd r) =
  match lastw l r None with Some w => Known (Z.land w 255) | None => cell_read (get_shadow st (fst r)) (snd r) end.
Proof.
  induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
  rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
  destruct (aptr_eqb_spec a r) as [<-|NE].
  - rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
  - destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.

Lemma known_range X st L BL LS q v : INVL X st L BL LS -> cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256.
Proof.
  intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.

Lemma havoc_0 p st : havoc p 0 st = st.
Proof. reflexivity. Qed.

Lemma land255_range a : 0 <= Z.land a 255 < 256.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.


End CeilWrap.
End MI_WEnframe.

(* [comment removed for export] *)
Module MI_WKill.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; unfold zsum in *; cbn in *; lia. Qed.

Lemma round_up_ge_k x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

Definition gterm (st : mstate) (sc : Z) (bh : aptr * ghdr) : Z :=
  match g_meta (snd bh) with
  | Some m => if m_sizeclass (MR st m) =? sc then cnt_of (MR st m) else 0
  | None => 0
  end.
Lemma gcnt_unfold st sc : gcnt st sc = zsum (map (gterm st sc) (map_to_list (s_groups st))).
Proof. reflexivity. Qed.

Lemma gcnt_delete st st' p h sc :
  s_groups st !! p = Some h -> s_groups st' = delete p (s_groups st) -> s_metas st' = s_metas st ->
  gcnt st sc = gterm st sc (p, h) + gcnt st' sc.
Proof.
  intros Hp HG HM. rewrite !gcnt_unfold, HG.
  rewrite <- (zsum_perm _ _ (Permutation_map (gterm st sc) (map_to_list_delete (s_groups st) p h Hp))). cbn. f_equal.
  f_equal. apply map_ext. intros [b hb]. unfold gterm. cbn. unfold MR, get_meta_rec. rewrite HM. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KILL.
Variables (X : extras) (st st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g p : aptr) (ai i : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! p = Some (mkGhdr (Some g) ai).
Hypothesis HF : x_fresh X = Some g.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis HO : x_orph X = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis HP : x_pend X = Some (fst p, sstart (MR st g) i).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Let sc := m_sizeclass (MR st g).
Let cnt := m_last_idx (MR st g) + 1.
(* [comment removed for export] *)
Hypothesis S1 : exists U, st1 = upd_ctx (fun c => set_usage_map U c) st.
Hypothesis U1 : forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc'.
Hypothesis U2 : forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48.
Let st' := del_slots p (get_stride (MR st g)) cnt (del_group p st1).
Let nested := m_maplen (MR st g) =? 0.
Let X' := mkX (x_idle X) (g :: x_zomb X) (if nested then Some p else None) (if nested then None else Some (fst p)) None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma g_hosts : hosts st p g. Proof. exists ai. exact Hg. Qed.
Lemma GO : group_ok X st LS g p ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
Lemma stride_pos : 0 < get_stride (MR st g).
Proof. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [H _]. unfold UNIT in H. lia. Qed.
Lemma gbase_p : gbase (MR st g) = p. Proof. exact (hosts_gbase _ _ _ IM _ _ g_hosts). Qed.
Lemma slot_g j : slot_start' (MR st g) j = (fst p, snd p + UNIT + get_stride (MR st g) * j).
Proof. rewrite slot_start'_sstart. unfold sstart. rewrite gbase_p. reflexivity. Qed.
Lemma sstart_g j : sstart (MR st g) j = snd p + UNIT + get_stride (MR st g) * j.
Proof. unfold sstart. rewrite gbase_p. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_metas : s_metas st' = s_metas st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_MR x : MR st' x = MR st x. Proof. unfold MR, get_meta_rec. rewrite K_metas. reflexivity. Qed.
Lemma K_regions : s_regions st' = s_regions st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_shadow : s_shadow st' = s_shadow st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_areas : s_areas st' = s_areas st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_tick : s_tick st' = s_tick st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_next_rid : s_next_rid st' = s_next_rid st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_secret : s_secret st' = s_secret st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_reserved : s_reserved st' = s_reserved st. Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_groups : s_groups st' = delete p (s_groups st). Proof. destruct S1 as [U ->]. reflexivity. Qed.
Lemma K_ctx : s_ctx st' = s_ctx st1. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma K_c (P : mctx -> Prop) : (forall c U, P c -> P (set_usage_map U c)) -> P (s_ctx st) -> P (s_ctx st').
Proof. intros HPU H0. rewrite K_ctx. destruct S1 as [U ->]. cbn. apply HPU. exact H0. Qed.
Lemma K_cf :
  c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st) /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st)
  /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st)
  /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)
  /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st)
  /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) /\ c_active (s_ctx st') = c_active (s_ctx st)
  /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st) /\ c_bounces (s_ctx st') = c_bounces (s_ctx st)
  /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st) /\ c_usage (s_ctx st') = c_usage (s_ctx st1).
Proof. destruct S1 as [U E]. rewrite K_ctx, E. cbn. repeat split; reflexivity. Qed.
Lemma K_usage sc' : usage st' sc' = usage st1 sc'.
Proof. reflexivity. Qed.

Lemma K_get_head h : get_head st' h = get_head st h.
Proof. destruct S1 as [U ->]. destruct h; reflexivity. Qed.
Lemma K_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite K_ctx. destruct S1 as [U ->]. reflexivity. Qed.

(* [comment removed for export] *)
Definition gslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = slot_start' (MR st g) j.
Lemma K_slots s : s_slots st' !! s = s_slots st !! s /\ ~ gslot s \/ s_slots st' !! s = None /\ gslot s.
Proof.
  pose proof stride_pos as SP. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold st'. rewrite lookup_del_slots; [| unfold cnt; lia| exact SP].
  replace (s_slots (del_group p st1)) with (s_slots st) by (destruct S1 as [U ->]; reflexivity).
  set (d := snd s - snd p - UNIT).
  destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod get_stride (MR st g) =? 0) && (d / get_stride (MR st g) <? cnt)) eqn:E.
  - right. split; [reflexivity|]. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
    apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
    exists (d / get_stride (MR st g)). split; [split; [apply Z.div_pos; lia| exact E4]|].
    rewrite slot_g. pose proof (Z.div_mod d (get_stride (MR st g)) ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
    destruct s as [sr so]. cbn [fst snd] in E1, d |- *. subst sr. f_equal. subst d. lia.
  - left. split; [reflexivity|]. intros (j & Hj & Es). rewrite slot_g in Es. subst s. cbn in d.
    assert (Ed : d = get_stride (MR st g) * j) by (unfold d; lia).
    rewrite N.eqb_refl in E. cbn in E.
    assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; apply Z.mul_nonneg_nonneg; lia). rewrite E2 in E. cbn in E.
    assert (E3 : (d mod get_stride (MR st g) =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult).
    rewrite E3 in E. cbn in E.
    assert (E4 : (d / get_stride (MR st g) <? cnt) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia).
    rewrite E4 in E. discriminate.
Qed.
Lemma K_slots_other s : ~ gslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros NG. destruct (K_slots s) as [[E _]|[_ G]]; [exact E| tauto]. Qed.
Lemma K_slots_g s : gslot s -> s_slots st' !! s = None.
Proof. intros G. destruct (K_slots s) as [[_ NG]|[E _]]; [tauto| exact E]. Qed.
Lemma K_slots_some s v : s_slots st' !! s = Some v -> s_slots st !! s = Some v /\ ~ gslot s.
Proof. intros H. destruct (K_slots s) as [[E NG]|[E G]]; [rewrite <- E; auto| congruence]. Qed.

(* [comment removed for export] *)
Lemma none_of {A} (o : option A) : (o <> None -> False) -> o = None.
Proof. destruct o; [intros H; exfalso; apply H; discriminate| reflexivity]. Qed.

Lemma g_slot_free j : 0 <= j <= m_last_idx (MR st g) ->
  ~ In (fst p, sstart (MR st g) j) (map bslot BL) /\ s_groups st !! (fst p, sstart (MR st g) j) = None
  /\ (x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
Proof.
  intros Hj. pose proof (is_part _ _ _ IS _ _ _ j Hg Hj) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts) in P. unfold one5 in P.
  destruct P as (_ & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
  assert (PJ : x_pend X = Some (fst p, sstart (MR st g) j) -> j = i).
  { intros HPj. rewrite HP in HPj. inversion HPj.
    destruct (Z.lt_total j i) as [LT|[E|LT]]; [| exact E|]; exfalso.
    - pose proof (sstart_lt _ _ _ IG _ _ j i g_hosts LT). pose proof stride_pos. lia.
    - pose proof (sstart_lt _ _ _ IG _ _ i j g_hosts LT). pose proof stride_pos. lia. }
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite HP in *. split; [intros C; apply nCE; auto|]. split; [| auto]. apply none_of. intros Hh. apply nDE. auto.
  - destruct (ALL j Hj NE) as [A|B].
    + split; [intros C; exact (nAC (conj A C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nAD (conj A Hh)).
    + split; [intros C; exact (nBC (conj B C))|]. split; [| exact PJ]. apply none_of. intros Hh. exact (nBD (conj B Hh)).
Qed.
Lemma g_slot_free' j : 0 <= j <= m_last_idx (MR st g) ->
  ~ In (slot_start' (MR st g) j) (map bslot BL) /\ s_groups st !! (slot_start' (MR st g) j) = None.
Proof. intros Hj. rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). destruct (g_slot_free j Hj) as (A & B & _). auto. Qed.

Lemma gslot_range s : gslot s -> exists j, 0 <= j <= m_last_idx (MR st g) /\ s = slot_start' (MR st g) j.
Proof. intros (j & Hj & E). exists j. unfold cnt in Hj. split; [lia| exact E]. Qed.

(* [comment removed for export] *)
Lemma other_slot_not_g m b j : hosts st b m -> m <> g -> 0 <= j <= m_last_idx (MR st m) -> ~ gslot (slot_start' (MR st m) j).
Proof.
  intros Hm NE Hj G. destruct (gslot_range _ G) as (j' & Hj' & E).
  destruct (slot_key_inj _ _ _ IS _ _ _ _ _ _ Hm g_hosts Hj Hj' E) as [Em _]. exact (NE Em).
Qed.
Lemma entry_not_g s m j : s_slots st !! s = Some (m, j) -> m <> g -> ~ gslot s.
Proof.
  intros Hs NE. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). exact (other_slot_not_g m b j Hb NE Hj).
Qed.
(* [comment removed for export] *)
Lemma entry_g_gslot s j : s_slots st !! s = Some (g, j) -> gslot s.
Proof.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hj & ->). exists j. unfold cnt. split; [lia| reflexivity].
Qed.

Lemma hosts_K b m : hosts st' b m <-> hosts st b m /\ b <> p.
Proof.
  unfold hosts. rewrite K_groups. split.
  - intros [a H]. apply lookup_delete_Some in H as [NE H]. split; [exists a; exact H| congruence].
  - intros [[a H] NE]. exists a. rewrite lookup_delete_ne by congruence. exact H.
Qed.
Lemma hosts_K_neq b m : hosts st' b m -> m <> g.
Proof. intros H. apply hosts_K in H as [H NE]. intros ->. exact (NE (hosts_inj _ _ _ IM _ _ _ H g_hosts)). Qed.
Lemma live_K m : live_group st m -> m <> g -> live_group st' m.
Proof.
  intros [b Hb] NE. exists b. apply hosts_K. split; [exact Hb|]. intros ->. exact (NE (hosts_fun _ _ _ _ Hb g_hosts)).
Qed.
Lemma g_unlisted_K h : ~ In g (LS h).
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h). Qed.

(* [comment removed for export] *)
Lemma p_not_gslot : ~ gslot p.
Proof.
  intros (j & Hj & E). rewrite slot_g in E. pose proof stride_pos.
  assert (snd p = snd p + UNIT + get_stride (MR st g) * j) by (rewrite E at 1; reflexivity). unfold UNIT in *. nia.
Qed.
Lemma slots_pos s m j : s_slots st !! s = Some (m, j) -> 0 < snd s.
Proof.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hj & ->). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn.
  pose proof (sstart0 _ _ _ IM _ _ Hb). pose proof (sstart_mono _ _ _ IG _ _ 0 j Hb ltac:(lia)).
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (a & _ & GOm). pose proof (g_align _ _ _ _ _ _ GOm) as [A _]. unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Lemma top_region_empty b h : m_maplen (MR st g) <> 0 -> s_groups st !! b = Some h -> fst b = fst p -> b = p.
Proof.
  intros Hml Hb Hf. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hmem & _).
  assert (Hm : hosts st b m) by (destruct h as [hm ha]; cbn in Em; subst hm; exists ha; exact Hb).
  destruct (aptr_eq_dec m g) as [->|NE]; [exact (hosts_inj _ _ _ IM _ _ _ Hm g_hosts)|]. exfalso.
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [Hml'|Hml'].
  - destruct (@top_chain _ _ _ _ IM IG IS m b Hm Hml') as (t & j & c & bt & Ha & Ht & Htop & Hft).
    assert (t = g) by (apply (@top_unique _ _ _ IG t g bt p Ht g_hosts Htop Hml); congruence). subst t.
    destruct (@anc_hostslot _ _ _ _ IM IG IS m g j c Ha) as (bp & Hp & Hsl).
    pose proof (hosts_inj _ _ _ IM _ _ _ Hp g_hosts). subst bp.
    destruct (@anc_facts _ _ _ _ IM IG IS m g j c Ha) as (bm' & bp' & _ & _ & _ & Hj & _).
    destruct (g_slot_free j Hj) as (_ & N & _). exact (Hsl N).
  - apply NE. apply (@top_unique _ _ _ IG m g b p Hm g_hosts Hml' Hml Hf).
Qed.

Lemma gcnt_K sc' : gcnt st sc' = (if sc =? sc' then cnt else 0) + gcnt st' sc'.
Proof.
  rewrite (gcnt_delete st st' p _ sc' Hg K_groups K_metas). unfold gterm. cbn. fold sc. fold cnt. reflexivity.
Qed.

Theorem INVL_kill : INVL X' st' L BL LS.
Proof.
  pose proof GO as GOg. pose proof g_hosts as Hgh.
  assert (NGm : forall b m, hosts st b m -> m <> g -> b <> p).
  { intros b m Hm NE ->. exact (NE (hosts_fun _ _ _ _ Hm g_hosts)). }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?K_regions, ?K_next_rid, ?K_reserved; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite K_frontier. reflexivity.
    + intros rid r H1 H2. rewrite K_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite K_frontier. exact (ir_brkfront rid r H1 H2).
    + apply (K_c (fun c => 0 <= c_meta_alloc_shift c /\ (c_meta_alloc_shift c = 0 \/ exists rid r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ r_len r = 2 ^ c_meta_alloc_shift c * PGSZ))); [intros c U H; exact H| exact ir_shift].
    + apply (K_c (fun c => match c_brk c with
                           | BrkUntried => ld_brk L = BPUntried /\ forall rid r, s_regions st !! rid = Some r -> r_kind r <> RKBrk
                           | BrkDead => ld_brk L = BPDead
                           | BrkLive rid off => ld_brk L = BPLive /\ exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off end));
        [intros c U H; exact H| exact ir_brk].
    + apply (K_c (fun c => 0 <= c_avail_meta_area_count c /\
        (0 < c_avail_meta_area_count c -> c_avail_meta_areas c <> None) /\
        (forall rid off, c_avail_meta_areas c = Some (rid, off) -> exists r, s_regions st !! rid = Some r /\ is_metakind r /\ PGSZ <= off /\ off mod PGSZ = 0
           /\ off + c_avail_meta_area_count c * PGSZ = r_len r /\ (0 < c_avail_meta_area_count c -> r_kind r = RKMeta))));
        [intros c U H; exact H| exact ir_cursor].
    + intros rid Ho. unfold X' in Ho. cbn in Ho. unfold nested in Ho. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [E|NE]; [discriminate|].
      inversion Ho. subst rid. destruct (g_top _ _ _ _ _ _ GOg NE) as (H0 & r & Hr & Hk & _). exists r. split; [exact Hr|]. split; [exact Hk|].
      intros b Hb. rewrite K_groups. destruct (aptr_eq_dec b p) as [->|NEb]; [apply lookup_delete_eq|]. rewrite lookup_delete_ne by congruence.
      destruct (s_groups st !! b) eqn:Eb; [| reflexivity]. exfalso. exact (NEb (top_region_empty b _ NE Eb Hb)).
  - (* [comment removed for export] *) destruct K_cf as (cf1 & cf2 & cf3 & cf4 & cf5 & cf6 & cf7 & cf8 & cf9 & cf10 & cf11 & cf12 & cf13 & cf14 & cf15 & cf16 & cf17).
    destruct IA; constructor; rewrite ?K_regions, ?K_areas, ?K_secret, ?K_metas, ?cf1, ?cf2, ?cf3, ?cf4, ?cf5, ?cf6, ?cf7, ?cf8, ?cf9, ?cf10, ?cf11, ?cf12, ?cf13, ?cf14, ?cf15, ?cf16, ?cf17; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite K_frontier. auto.
    + intros sc' Hsc'. rewrite K_usage, (U1 sc' Hsc').
      pose proof (gcnt_K sc') as GK. rewrite <- (ia_usage sc' Hsc') in GK. rewrite Z.eqb_sym in GK.
      destruct (Z.eqb_spec sc' sc) as [E|NE]; [rewrite <- E; lia| lia].
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5] eqn:EIM; constructor; rewrite ?K_MR.
    + intros m Hm. rewrite !K_MR. apply M1. rewrite <- (K_MR m). exact Hm.
    + intros m b Hm. rewrite K_MR in Hm. destruct (aptr_eq_dec m g) as [->|NE]; [right; left; reflexivity|].
      destruct (M2 m b Hm) as [H|H]; [left| right; right; exact H]. apply hosts_K. split; [exact H|]. exact (NGm b m H NE).
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NE Hb]. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !K_MR. auto.
    + intros m Hm. rewrite K_metas. exact (M4 m Hm).
    + intros z Hz. rewrite !K_MR, K_groups. cbn in Hz. destruct Hz as [<-|Hz].
      * split; [intros [h Hh]; exact (g_unlisted_K h Hh)|]. split; [exact NL|].
        split; [exact (proj2 (il_link _ _ IL g) NL)|].
        exists p. split; [exact (hosts_mem _ _ _ IM _ _ g_hosts)| apply lookup_delete_eq].
      * destruct (M5 z Hz) as (A1 & A2 & A3 & b & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
        exists b. split; [exact A4|]. destruct (aptr_eq_dec b p) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; exact A5].
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9] eqn:EIL; constructor; try assumption.
    + intros h. rewrite K_get_head. apply L1.
    + intros h. apply (dll_ext_metas st st' K_metas). apply L2.
    + intros m. rewrite !K_MR. apply L5.
    + intros m Hm. rewrite !K_MR. apply L6. exact Hm.
    + intros sc0 m Hm. destruct (L7 sc0 m Hm) as (A1 & A2 & A3). rewrite K_MR. split; [exact A1|]. split; [| exact A3].
      apply live_K; [exact A2|]. intros ->. exact (g_unlisted_K _ Hm).
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
    + intros m b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. pose proof (G1 m b aim Hb) as GOm.
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aim Hb) g_hosts)).
      assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      destruct GOm; constructor; rewrite ?K_MR, ?K_metas, ?K_regions; try assumption.
      * intros _. exact (g_partial NF).
      * intros _. exact (g_unlisted NF).
      * intros _. exact (g_rest NF).
      * intros _. exact (g_under NF).
      * intros Hml. destruct (g_nest Hml) as (pm & i' & Hs & REST). exists pm, i'. rewrite !K_MR. split; [| exact REST].
        rewrite K_slots_other; [exact Hs|]. apply (entry_not_g _ _ _ Hs). intros ->.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi' & Eb).
        destruct (g_slot_free' i' Hi') as [_ N]. rewrite <- Eb, Hb in N. discriminate.
    + intros b aim Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. exact (G2 b aim Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite K_groups in H1, H2. apply lookup_delete_Some in H1 as [_ H1]. apply lookup_delete_Some in H2 as [_ H2].
      rewrite !K_MR. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite K_regions in Hr. destruct (G4 rid r Hr Hk ltac:(rewrite HO; discriminate)) as (m & Hm & Hml). exists m. rewrite K_MR. split; [| exact Hml].
      apply hosts_K. split; [exact Hm|]. intros E.
      assert (Em : m = g) by (apply (hosts_fun st p); [rewrite <- E; exact Hm| exact g_hosts]). subst m.
      unfold X' in Ho. cbn in Ho. unfold nested in Ho. rewrite (proj2 (Z.eqb_neq _ _) Hml) in Ho. apply Ho. rewrite <- E. reflexivity.
    + intros b h Hb. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [_ Hb]. rewrite K_regions. exact (G5 b h Hb).
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
    + intros s m j Hs. destruct (K_slots_some _ _ Hs) as [Hs0 NG]. destruct (S1' s m j Hs0) as (Hl & Hj & Es). rewrite !K_MR.
      assert (NEm : m <> g) by (intros ->; exact (NG (entry_g_gslot _ _ Hs0))).
      split; [exact (live_K m Hl NEm)|]. auto.
    + intros b m j Hb Hj. rewrite K_MR in Hj |- *. apply hosts_K in Hb as [Hb NEb].
      assert (NEm : m <> g) by (intros ->; exact (NEb (hosts_inj _ _ _ IM _ _ _ Hb g_hosts))).
      rewrite K_slots_other; [exact (S2 b m j Hb Hj)|]. exact (other_slot_not_g m b j Hb NEm Hj).
    + intros b m aim j Hb Hj. rewrite K_groups in Hb. apply lookup_delete_Some in Hb as [NEb Hb]. rewrite K_MR in Hj. rewrite !K_MR, K_groups. unfold X'. cbn [x_pend].
      assert (Hbm : hosts st b m) by (exists aim; exact Hb).
      assert (NEm : m <> g) by (intros ->; apply NEb; symmetry; exact (hosts_inj _ _ _ IM _ _ _ Hbm g_hosts)).
      pose proof (S3 b m aim j Hb Hj) as P. cbn zeta in P |- *.
      set (s := slot_start' (MR st m) j) in *.
      assert (OP : ~ (x_pend X = Some s)).
      { rewrite HP. intros E. apply (other_slot_not_g m b j Hbm NEm Hj). exists i. split; [unfold cnt; lia|].
        rewrite (slot_start'_eq _ _ _ IM _ _ _ g_hosts). apply (inj Some) in E. rewrite E. reflexivity. }
      unfold one5 in P |- *.
      destruct P as (P0 & nAB & nAC & nAD & nAE & nBC & nBD & nBE & nCD & nCE & nDE).
      destruct (aptr_eq_dec s p) as [Esp|NEsp].
      * assert (Hn : nested = true).
        { unfold nested. apply Z.eqb_eq. destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [E|NE]; [exact E|]. exfalso.
          destruct (g_top _ _ _ _ _ _ GOg NE) as [H0 _]. pose proof (slots_pos s m j (S2 b m j Hbm Hj)) as SP. rewrite Esp in SP. lia. }
        rewrite Hn. rewrite Esp in *. rewrite lookup_delete_eq.
        assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
        assert (nA : ~ tbit (m_avail (MR st m)) j = true) by (intros A; exact (nAD (conj A D))).
        assert (nB : ~ tbit (m_freed (MR st m)) j = true) by (intros B; exact (nBD (conj B D))).
        assert (nC : ~ In p (map bslot BL)) by (intros C; exact (nCD (conj C D))).
        clear - nA nB nC. assert (NN : ~ (@None ghdr <> None)) by (intros H; apply H; reflexivity). tauto.
      * rewrite lookup_delete_ne by congruence.
        assert (NP' : ~ ((if nested then Some p else None) = Some s)) by (destruct nested; [intros E; inversion E; congruence| discriminate]).
        revert P0 nAB nAC nAD nAE nBC nBD nBE nCD nCE nDE OP NP'. clear.
        generalize (tbit (m_avail (MR st m)) j = true) (tbit (m_freed (MR st m)) j = true) (In s (map bslot BL)) (s_groups st !! s <> None).
        generalize ((if nested then Some p else None) = Some s) (x_pend X = Some s). intros. tauto.
    + intros s Hs. unfold X' in Hs. cbn [x_pend] in Hs. unfold nested in Hs. destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; [| discriminate]. inversion Hs. subst s.
      destruct (g_nest _ _ _ _ _ _ GOg Hml) as (pm & ip & Hs0 & _). rewrite K_slots_other; [rewrite Hs0; discriminate| exact p_not_gslot].
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & j & Hs & REST). exists m, j. rewrite K_MR. split; [| exact REST].
      rewrite K_slots_other; [exact Hs|]. intros G. destruct (gslot_range _ G) as (j' & Hj' & E).
      destruct (g_slot_free' j' Hj') as [NB _]. apply NB. rewrite <- E. apply in_map_iff. exists k. auto.
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
    assert (KN : forall q v, known st q v -> known st' q v).
    { intros q v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
    assert (UN : forall q, unknown st q -> unknown st' q).
    { intros q. unfold unknown, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
    constructor.
    + intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_regions. exact (D1 rid sh Hsh).
    + intros rid sh Hsh. rewrite K_shadow in Hsh. rewrite K_tick. exact (D2 rid sh Hsh).
    + intros b m j Hb Hj. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hj |- *. apply KN. exact (D3 b m j Hb Hj).
    + intros b m o Hb Ho. apply hosts_K in Hb as [Hb _]. apply UN. exact (D4 b m o Hb Ho).
    + intros b m pm j Hb Hml Hs. apply hosts_K in Hb as [Hb _]. rewrite K_MR in Hml. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR.
      destruct (D5 b m pm j Hb Hml Hs0) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
      split; [exists v3; auto|]. auto.
    + intros k m j Hk Hs. destruct (K_slots_some _ _ Hs) as [Hs0 _]. rewrite !K_MR. pose proof (D6 k m j Hk Hs0) as B. cbn zeta in B |- *.
      destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [exact A5|]. split.
      * intros Hres. destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; auto.
      * split; [intros Hres; apply KN; apply A7; exact Hres|]. intros a Ha. apply UN. apply A8. exact Ha.
Qed.

Lemma kill_top : m_maplen (MR st g) <> 0 ->
  exists r, snd p = 0 /\ s_regions st' !! (fst p) = Some r /\ r_kind r = RKGroup
    /\ m_maplen (MR st g) * 4096 = round_up_pg (r_len r) /\ 0 < m_maplen (MR st g) * 4096.
Proof.
  intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r & Hr & Hk & E & _). exists r. rewrite K_regions.
  pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & L0 & _). pose proof (round_up_ge_k (r_len r)). repeat split; auto. lia.
Qed.

Lemma kill_nested : m_maplen (MR st g) = 0 ->
  exists pm ip bpm, s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48
    /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
    /\ gend (MR st g) <= sstart (MR st pm) ip + get_stride (MR st pm).
Proof.
  intros Hml. destruct (g_nest _ _ _ _ _ _ GO Hml) as (pm & ip & Hs & Hf & He & Hsc & Hstr).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpm Hpm] & Hip & Ep).
  exists pm, ip, bpm.
  assert (NE : pm <> g) by (intros ->; lia).
  split; [rewrite K_slots_other; [exact Hs| exact p_not_gslot]|].
  split; [apply hosts_K; split; [exact Hpm|]; intros ->; exact (NE (hosts_fun _ _ _ _ Hpm g_hosts))|].
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm) in Ep.
  split; [rewrite Ep; reflexivity|]. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma dec_hdr_eq {T} (k : aptr -> Z -> M T) bail :
  m_maplen (MR st g) = 0 ->
  exists pm ip bpm, dec_hdr st' p k bail = k pm ip
    /\ s_slots st' !! p = Some (pm, ip) /\ hosts st' bpm pm /\ fst bpm = fst p
    /\ 0 <= ip <= m_last_idx (MR st pm) /\ p = (fst bpm, sstart (MR st pm) ip)
    /\ m_sizeclass (MR st g) < m_sizeclass (MR st pm) < 48.
Proof.
  intros Hml. destruct (kill_nested Hml) as (pm & ip & bpm & Hs' & Hpm' & Hf & Hip & Ep & Hsc & Hstr & Hend).
  exists pm, ip, bpm. split; [| repeat split; auto; lia].
  pose proof Hpm' as Hpm. apply hosts_K in Hpm as [Hpm NEb].
  destruct (hosts_ok _ _ _ IG _ _ Hpm) as (aipm & Hgpm & GOpm).
  assert (Hs : s_slots st !! p = Some (pm, ip)) by (destruct (K_slots_some _ _ Hs') as [H _]; exact H).
  (* [comment removed for export] *)
  pose proof (ish_nest _ _ ISH p g pm ip g_hosts Hml Hs) as NS. cbn zeta in NS. rewrite (hosts_gbase _ _ _ IM _ _ Hpm) in NS.
  set (q := (snd p - snd bpm - UNIT) / UNIT) in NS.
  destruct NS as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
  pose proof (ish_hdr0 _ _ ISH bpm pm ip Hpm ltac:(unfold cnt_of; lia)) as K4.
  assert (KN : forall a v, known st a v -> known st' a v).
  { intros a v. unfold known, SHd, get_shadow. rewrite K_shadow. exact (fun H => H). }
  assert (Hq : UNIT * q = get_stride (MR st pm) * ip).
  { subst q. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm).
    replace (snd bpm + UNIT + get_stride (MR st pm) * ip - snd bpm - UNIT) with (size_class (m_sizeclass (MR st pm)) * ip * UNIT) by (rewrite Hstr; lia).
    rewrite Hstr. unfold UNIT. rewrite Z.div_mul by lia. lia. }
  clearbody q.
  pose proof (g_align _ _ _ _ _ _ GOpm) as [A0 A16].
  unfold dec_hdr, get_meta.
  rewrite (guard_true 10).
  2:{ apply Z.eqb_eq. rewrite Ep. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), Hstr. unfold UNIT in *.
      replace (snd bpm + 16 + 16 * size_class (m_sizeclass (MR st pm)) * ip) with (snd bpm + (1 + size_class (m_sizeclass (MR st pm)) * ip) * 16) by lia.
      rewrite Z_mod_plus_full. exact A16. }
  unfold rd16.
  rewrite (rd8_known st' (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [apply KN; exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [apply KN; exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd p (-3)) v3) by (eapply known_at; [apply KN; exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st' (aadd p (-4)) 0).
  2:{ eapply known_at; [apply KN; exact K4| rewrite Ep; cbn; unfold IB; lia| rewrite Ep; reflexivity]. }
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bpm).
  { rewrite Ep. unfold aadd, sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hpm). destruct bpm as [br bo]. cbn [fst snd] in *. f_equal. lia. }
  rewrite Ebase. unfold get_group. destruct Hpm' as [ai' Hg']. rewrite Hg'. cbn [g_meta]. rewrite E3. fold (MR st' pm). rewrite !K_MR.
  rewrite (guard_true 11) by (rewrite (hosts_mem _ _ _ IM _ _ Hpm); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  pose proof (is_part _ _ _ IS _ _ _ ip Hgpm Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hpm), <- Ep in P. unfold one5 in P.
  assert (D : s_groups st !! p <> None) by (rewrite Hg; discriminate).
  rewrite (guard_true 13) by (unfold testbit; destruct (Z.testbit (m_avail (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
  rewrite (guard_true 14) by (unfold testbit; destruct (Z.testbit (m_freed (MR st pm)) ip) eqn:E; [exfalso; unfold tbit in P; tauto| reflexivity]).
  pose proof (g_present _ _ _ _ _ _ GOpm) as Pr. destruct (s_metas st !! pm) as [mr|] eqn:Em; [| congruence].
  destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
  destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
  destruct K_cf as (cf1 & _).
  rewrite (guard_true 15) by (rewrite K_areas, Emk, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; unfold ctx; rewrite cf1; exact Hck).
  pose proof (size_class_bound (m_sizeclass (MR st pm))) as SB.
  rewrite (guard_true 16).
  2:{ clear KN K2 K1 K3 K4 P D Ebase. destruct (Z.ltb_spec (m_sizeclass (MR st pm)) 48); [| lia]. rewrite Hstr in Hq.
      assert (Eq : q = size_class (m_sizeclass (MR st pm)) * ip) by (unfold UNIT in Hq; lia).
      assert (G0 : 0 <= m_sizeclass (MR st g)) by (destruct (g_sc _ _ _ _ _ _ GO) as [[[G0 _] _]|(G63 & _)]; lia).
      rewrite Eq. specialize (SB ltac:(lia)). apply Bool.andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt]. rewrite Z.mul_add_distr_l. lia. }
  rewrite (guard_true 17).
  2:{ destruct (Z.eqb_spec (m_maplen (MR st pm)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      destruct (g_top _ _ _ _ _ _ GOpm NM) as (B0 & _ & _ & _ & _ & GE). apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite (hosts_gbase _ _ _ IM _ _ Hpm), B0 in GE.
      pose proof (stride_ge _ _ _ IG _ _ Hpm) as [S16 _]. unfold UNIT in S16, Hq, GE.
      clear KN K2 K1 K3 K4 P D Ebase SB.
      eapply (guard17_arith (get_stride (MR st pm)) ip 0 0 q (m_last_idx (MR st pm)) (m_maplen (MR st pm))); try lia. }
  reflexivity.
Qed.
End KILL.

(* [comment removed for export] *)
Lemma fg_st1 X st L BL LS g p ai (INV : INVL X st L BL LS) (Hg : s_groups st !! p = Some (mkGhdr (Some g) ai)) :
  let sc := m_sizeclass (MR st g) in
  let cnt := m_last_idx (MR st g) + 1 in
  let st1 := if sc <? 48 then set_usage sc (usage st sc - cnt) st else st in
  (exists U, st1 = upd_ctx (fun c => set_usage_map U c) st)
  /\ (forall sc', 0 <= sc' < 48 -> usage st1 sc' = if sc' =? sc then usage st sc - cnt else usage st sc')
  /\ (forall sc0 v, c_usage (s_ctx st1) !! sc0 = Some v -> 0 <= sc0 < 48).
Proof.
  cbn zeta. pose proof (ia_usage_keys _ (proj1 (proj2 INV))) as UK.
  pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as SC.
  destruct (Z.ltb_spec (m_sizeclass (MR st g)) 48) as [LT|GE].
  - split; [eexists; reflexivity|]. split.
    + intros sc' Hsc'. apply usage_set_usage.
    + intros sc0 v. cbn. destruct (Z.eq_dec sc0 (m_sizeclass (MR st g))) as [->|NE].
      * intros _. destruct SC as [[A _]|(A & _)]; lia.
      * rewrite lookup_insert_ne by congruence. apply UK.
  - split; [| split; [| exact UK]].
    + exists (c_usage (s_ctx st)). destruct st as [c ? ? ? ? ? ? ? ? ? ?]; destruct c; reflexivity.
    + intros sc' Hsc'. destruct (Z.eqb_spec sc' (m_sizeclass (MR st g))); [lia| reflexivity].
Qed.


End CeilWrap.
End MI_WKill.

(* [comment removed for export] *)
Module MI_WNtf.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_WKill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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


End CeilWrap.
End MI_WNtf.

(* [comment removed for export] *)
Module MI_WCreate.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith MI_Bits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_WKill MI_WNtf MI_WGroup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma res_excl a o : a mod 16 = 0 -> 12 <= o mod 16 -> ~ (a <= o < a + 12).
Proof.
  intros Ha Ho [H1 H2]. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod o 16 ltac:(lia)) as Do.
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)) as Bo. rewrite Ha in Da.
  set (qa := a / 16) in *. set (qo := o / 16) in *. set (r := o mod 16) in *. clearbody qa qo r. lia.
Qed.

(* [comment removed for export] *)
Lemma one5_iff_create (A B E : Prop) (C D : Prop) : one5 A B False False E -> ~ C -> ~ D -> one5 A B C D E.
Proof. unfold one5. tauto. Qed.

Section CREATE.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m p : aptr) (ai : Z) (mr' : meta).
Hypothesis INV : INVL X st L BL LS.
Hypothesis IDLE : In m (x_idle X).

(* [comment removed for export] *)
Let sc' := m_sizeclass mr'.
Let last' := m_last_idx mr'.
Let cnt := last' + 1.
Let stride' := get_stride mr'.
Hypothesis R_prev : m_prev mr' = None.
Hypothesis R_next : m_next mr' = None.
Hypothesis R_mem : m_mem mr' = Some p.
Hypothesis R_freeable : m_freeable mr' = 1.
Hypothesis R_maplen : 0 <= m_maplen mr'.
Hypothesis R_li : 0 <= last' <= 31.
Hypothesis R_ai : 0 <= ai <= last'.
Hypothesis R_full0 : sc' = 0 -> ai = last'.
Hypothesis R_sc : (0 <= sc' < 48 /\ m_maplen mr' <= 256) \/ (sc' = 63 /\ last' = 0 /\ m_maplen mr' <> 0).
Hypothesis R_masks : 0 <= m_avail mr' /\ 0 <= m_freed mr'
  /\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit (m_freed mr') i = true -> i <= last')
  /\ (forall i, 0 <= i -> tbit (m_avail mr') i = true -> tbit (m_freed mr') i = true -> False)
  /\ (forall i, ai < i <= last' -> tbit (m_freed mr') i = true).
Hypothesis R_stride : sc' < 48 ->
  (stride' <= UNIT * size_class sc' \/ 28 <= sc') /\ (last' = 0 -> m_maplen mr' <> 0 /\ 27 <= sc') /\ stride' * cnt < 2^20.
Hypothesis R_stride16 : 16 <= stride' /\ stride' mod 16 = 0.
Hypothesis R_align : 0 <= snd p /\ snd p mod UNIT = 0.

(* [comment removed for export] *)
Hypothesis X_fresh : x_fresh X' = Some m \/ (sc' = 63 /\ x_fresh X' = x_fresh X).
Hypothesis X_fresh_old : x_fresh X = None.
Hypothesis X_idle : forall x, In x (x_idle X') -> In x (x_idle X) /\ x <> m.
Hypothesis X_zomb : x_zomb X' = x_zomb X.
Hypothesis X_nozomb : x_zomb X = [].
Hypothesis X_part : forall i, 0 <= i <= last' ->
  one5 (tbit (m_avail mr') i = true) (tbit (m_freed mr') i = true) False False (x_pend X' = Some (fst p, snd p + UNIT + stride' * i)).
Hypothesis X_pend' : forall s, x_pend X' = Some s -> exists i, 0 <= i <= last' /\ s = (fst p, snd p + UNIT + stride' * i).
(* [comment removed for export] *)
Hypothesis NOPART : ai < last' -> LS (LActive sc') = [].

(* [comment removed for export] *)
Hypothesis SITE :
  (m_maplen mr' <> 0 /\ snd p = 0 /\ x_orph X = Some (fst p) /\ x_orph X' = None /\ x_pend X = None
     /\ exists r, s_regions st !! (fst p) = Some r /\ r_kind r = RKGroup /\ m_maplen mr' * 4096 = round_up_pg (r_len r)
        /\ snd p + UNIT + stride' * cnt <= m_maplen mr' * 4096)
  \/ (m_maplen mr' = 0 /\ x_pend X = Some p /\ x_pend X' = None /\ x_orph X' = x_orph X /\ x_orph X = None
     /\ exists pm ip bpm, s_slots st !! p = Some (pm, ip) /\ hosts st bpm pm /\ fst bpm = fst p /\ 0 <= ip <= m_last_idx (MR st pm)
        /\ p = (fst bpm, sstart (MR st pm) ip)
        /\ snd p + UNIT + stride' * cnt <= sstart (MR st pm) ip + get_stride (MR st pm)
        /\ sc' < m_sizeclass (MR st pm) < 48 /\ get_stride (MR st pm) = UNIT * size_class (m_sizeclass (MR st pm))
        /\ (exists v3, known st (fst p, snd p - 3) v3 /\ Z.land v3 31 = ip /\ 0 <= v3 < 256)
        /\ known st (fst p, snd p - 2) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 0)
        /\ known st (fst p, snd p - 1) (byte_of ((snd p - snd bpm - UNIT) / UNIT) 1)
        /\ 0 <= (snd p - snd bpm - UNIT) / UNIT < 2^16).

(* [comment removed for export] *)
Hypothesis SH_hdr0 : forall i, 0 <= i <= cnt -> known st (fst p, snd p + UNIT + stride' * i - IB) 0.
Hypothesis SH_ghdr : forall o v tk, snd p <= o < snd p + 12 -> r_cells (get_shadow st (fst p)) !! o = Some (v, tk) -> (tk < s_tick st)%N.

(* [comment removed for export] *)
Hypothesis E_metas : s_metas st' = <[m := mr']> (s_metas st).
Hypothesis E_groups : s_groups st' = <[p := mkGhdr (Some m) ai]> (s_groups st).
Hypothesis E_slots : forall s, s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride' =? 0) && ((snd s - snd p - UNIT) / stride' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride') else s_slots st !! s.
Hypothesis E_shadow : s_shadow st' = s_shadow (hdr_havoc p st).
Hypotheses (E_regions : s_regions st' = s_regions st) (E_areas : s_areas st' = s_areas st) (E_next_rid : s_next_rid st' = s_next_rid st)
           (E_tick : s_tick st' = s_tick st) (E_secret : s_secret st' = s_secret st) (E_reserved : s_reserved st' = s_reserved st).
Hypothesis E_ctx :
  c_secret (s_ctx st') = c_secret (s_ctx st) /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st) /\ c_avail_meta (s_ctx st') = c_avail_meta (s_ctx st)
  /\ c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) /\ c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st)
  /\ c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st) /\ c_meta_area_head (s_ctx st') = c_meta_area_head (s_ctx st)
  /\ c_meta_area_tail (s_ctx st') = c_meta_area_tail (s_ctx st) /\ c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st)
  /\ c_active (s_ctx st') = c_active (s_ctx st) /\ c_unmap_seq (s_ctx st') = c_unmap_seq (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st) /\ c_brk (s_ctx st') = c_brk (s_ctx st).
Hypothesis E_mc : 0 <= c_mmap_counter (s_ctx st') < 2^32.
Hypothesis E_usage : forall sc0, 0 <= sc0 < 48 -> usage st' sc0 = usage st sc0 + (if sc0 =? sc' then cnt else 0).
Hypothesis E_usage_keys : forall sc0 v, c_usage (s_ctx st') !! sc0 = Some v -> 0 <= sc0 < 48.

(* [comment removed for export] *)
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Ltac slim := try clear SITE; try clear E_ctx; try clear E_slots; try clear X_part; try clear X_pend'; try clear R_masks; try clear R_stride; try clear R_sc;
             try clear E_usage; try clear E_usage_keys; try clear SH_hdr0; try clear SH_ghdr; try clear X_idle; try clear NOPART.
Local Tactic Notation "lia" := slim; Lia.lia.
Local Tactic Notation "nia" := slim; Lia.nia.

Lemma m_meta0 : s_metas st !! m = Some meta0. Proof. exact (proj1 (im_idle _ _ _ IM m IDLE)). Qed.
Lemma m_unlisted h : ~ In m (LS h). Proof. intros H. apply (proj2 (im_idle _ _ _ IM m IDLE)). exists h. exact H. Qed.
Lemma MRm : MR st m = meta0. Proof. unfold MR, get_meta_rec. rewrite m_meta0. reflexivity. Qed.
Lemma m_not_live : ~ live_group st m. Proof. exact (idle_not_live _ _ _ _ _ INV m IDLE). Qed.

Lemma C_MR x : MR st' x = if aptr_eqb x m then mr' else MR st x.
Proof. unfold MR, get_meta_rec. rewrite E_metas. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
Lemma C_MR_other x : x <> m -> MR st' x = MR st x. Proof. intros NE. rewrite C_MR, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma C_MR_m : MR st' m = mr'. Proof. rewrite C_MR, aptr_eqb_refl. reflexivity. Qed.
Lemma C_keys x : s_metas st' !! x <> None <-> s_metas st !! x <> None.
Proof. rewrite E_metas. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite lookup_insert_eq, m_meta0; split; discriminate| rewrite lookup_insert_ne by congruence; tauto]. Qed.

(* [comment removed for export] *)
Lemma p_free : s_groups st !! p = None.
Proof.
  destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & _)].
  - destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). apply NG. reflexivity.
  - destruct Hpm as [aipm Hpm]. pose proof (is_part _ _ _ IS _ _ _ ip Hpm Hip) as P. cbn zeta in P.
    rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm)), <- Ep, HP in P. unfold one5 in P.
    destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.

Lemma C_groups b : s_groups st' !! b = if aptr_eqb b p then Some (mkGhdr (Some m) ai) else s_groups st !! b.
Proof. rewrite E_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. Qed.
Lemma C_hosts b x : hosts st' b x <-> (b = p /\ x = m) \/ (b <> p /\ hosts st b x).
Proof.
  unfold hosts. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
  - split; [intros [a H]; inversion H; auto| intros [[_ ->]|[NE _]]; [exists ai; reflexivity| congruence]].
  - split; [intros H; right; auto| intros [[E _]|[_ H]]; [congruence| exact H]].
Qed.
Lemma C_hosts_old b x : hosts st b x -> hosts st' b x.
Proof. intros H. apply C_hosts. destruct (aptr_eq_dec b p) as [->|NE]; [| right; auto]. destruct H as [a H]. rewrite p_free in H. discriminate. Qed.
Lemma C_hosts_old_ne b x : hosts st b x -> x <> m.
Proof. intros H ->. exact (m_not_live (ex_intro _ b H)). Qed.
Lemma C_MR_hosted b x : hosts st b x -> MR st' x = MR st x.
Proof. intros H. apply C_MR_other. exact (C_hosts_old_ne b x H). Qed.

(* [comment removed for export] *)
Lemma gbase' : gbase mr' = p. Proof. unfold gbase. rewrite R_mem. reflexivity. Qed.
Lemma sstart' i : sstart mr' i = snd p + UNIT + stride' * i. Proof. unfold sstart. rewrite gbase'. reflexivity. Qed.
Lemma slot' i : slot_start' mr' i = (fst p, snd p + UNIT + stride' * i). Proof. rewrite slot_start'_sstart, gbase', sstart'. reflexivity. Qed.

(* [comment removed for export] *)
Definition nslot (s : aptr) : Prop := exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j).
Lemma C_slots s : (s_slots st' !! s = s_slots st !! s /\ ~ nslot s) \/ (exists j, 0 <= j < cnt /\ s = (fst p, snd p + UNIT + stride' * j) /\ s_slots st' !! s = Some (m, j)).
Proof.
  unfold nslot. pose proof (E_slots s) as ES. destruct R_stride16 as [SP SM]. clear - ES SP SM. subst cnt last'.
  rewrite ES. clear ES. set (d := snd s - snd p - UNIT).
  destruct ((fst s =? fst p)%N && (0 <=? d) && (d mod stride' =? 0) && (d / stride' <? m_last_idx mr' + 1)) eqn:E.
  - right. apply Bool.andb_true_iff in E as [E E4]. apply Bool.andb_true_iff in E as [E E3]. apply Bool.andb_true_iff in E as [E1 E2].
    apply N.eqb_eq in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. apply Z.ltb_lt in E4.
    exists (d / stride'). split; [split; [apply Z.div_pos; lia| exact E4]|]. split; [| reflexivity].
    pose proof (Z.div_mod d stride' ltac:(lia)) as DM. rewrite E3, Z.add_0_r in DM.
    destruct s as [sr so]. cbn in E1, d |- *. subst sr. f_equal. lia.
  - left. split; [reflexivity|]. intros (j & Hj & Es). subst s. cbn in d.
    assert (Ed : d = stride' * j) by (unfold d; lia). clearbody d.
    rewrite N.eqb_refl in E. cbn in E.
    assert (E2 : (0 <=? d) = true) by (apply Z.leb_le; rewrite Ed; nia). rewrite E2 in E. cbn in E.
    assert (E3 : (d mod stride' =? 0) = true) by (apply Z.eqb_eq; rewrite Ed, Z.mul_comm; apply Z_mod_mult). rewrite E3 in E. cbn in E.
    assert (E4 : (d / stride' <? m_last_idx mr' + 1) = true) by (apply Z.ltb_lt; rewrite Ed, Z.mul_comm, Z_div_mult by lia; lia). rewrite E4 in E. discriminate.
Qed.
Lemma C_slots_old s : ~ nslot s -> s_slots st' !! s = s_slots st !! s.
Proof. intros N. destruct (C_slots s) as [[E _]|(j & Hj & Es & _)]; [exact E|]. exfalso. apply N. exists j. auto. Qed.
Lemma C_slots_new j : 0 <= j < cnt -> s_slots st' !! (fst p, snd p + UNIT + stride' * j) = Some (m, j).
Proof.
  intros Hj. destruct (C_slots (fst p, snd p + UNIT + stride' * j)) as [[_ N]|(j' & Hj' & Es & E)]; [exfalso; apply N; exists j; auto|].
  rewrite E. inversion Es. destruct R_stride16 as [SP _]. assert (j' = j) by (clear - H0 SP Hj Hj'; nia). subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma new_key_range j : 0 <= j < cnt -> snd p < snd p + UNIT + stride' * j /\ snd p + UNIT + stride' * j + 16 <= snd p + UNIT + stride' * cnt.
Proof. intros Hj. destruct R_stride16 as [SP _]. clear - Hj SP. subst cnt last'. unfold UNIT. split; [nia|]. assert (stride' * j + stride' <= stride' * (m_last_idx mr' + 1)) by nia. lia. Qed.

Lemma old_slot_not_new s x i : s_slots st !! s = Some (x, i) -> ~ nslot s.
Proof.
  intros Hs (j & Hj & ->). destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es. inversion Es.
  destruct (new_key_range j Hj) as [K1 K2].
  destruct SITE as [(Hml & P0 & HO & _ & _ & r & Hr & Hk & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hf & Hip & Ep & FIT & _)].
  - (* [comment removed for export] *)
    destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx]. rewrite (NG bx) in Hxx; [discriminate|]. rewrite <- H0. reflexivity.
  - (* [comment removed for export] *)
    destruct Hpm as [aipm Hpm'].
    assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
    assert (Hf2 : fst bx = fst bpm) by (rewrite Ep in H0; cbn in H0; congruence).
    assert (Hi2 : 0 <= i <= m_last_idx (MR st x) + 1) by (clear - Hi; lia).
    pose proof (@sep_hdr0 _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi2) as D.
    rewrite sstart_succ in D. rewrite Ep in H1, K1, K2, FIT. cbn in H1, K1, K2, FIT.
    assert (NEQ : x <> pm \/ i <> ip).
    { destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->. clear - H1 K1. lia. }
    specialize (D NEQ). clear - D H1 K1 K2 FIT Hj. lia.
Qed.

Lemma old_hosts_not_new b x : hosts st b x -> ~ nslot b.
Proof.
  intros Hx N. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO).
  destruct (Z.eq_dec (m_maplen (MR st x)) 0) as [Hml|Hml].
  - destruct (g_nest _ _ _ _ _ _ GO Hml) as (px & ix & Hs & _). exact (old_slot_not_new _ _ _ Hs N).
  - destruct (g_top _ _ _ _ _ _ GO Hml) as [B0 _]. destruct N as (j & Hj & ->). cbn in B0. destruct (new_key_range j Hj) as [K1 K2]. destruct R_align as [A0 _]. clear - B0 K1 A0. lia.
Qed.

Lemma p_not_new : ~ nslot p.
Proof. intros (j & Hj & E). destruct (new_key_range j Hj) as [K _]. apply (f_equal snd) in E. cbn in E. clear - K E. lia. Qed.

Lemma blk_not_new k : In k BL -> ~ nslot (bslot k).
Proof. intros Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). exact (old_slot_not_new _ _ _ Hs). Qed.

(* [comment removed for export] *)
Lemma new_not_group j : 0 <= j < cnt -> s_groups st !! (fst p, snd p + UNIT + stride' * j) = None.
Proof.
  intros Hj. destruct (s_groups st !! (fst p, snd p + UNIT + stride' * j)) as [h|] eqn:E; [| reflexivity]. exfalso.
  destruct (im_hdr _ _ _ IM _ _ E) as (x & Ex & _). apply (old_hosts_not_new (fst p, snd p + UNIT + stride' * j) x); [| exists j; auto].
  destruct h as [hm ha]. cbn in Ex. subst hm. exists ha. exact E.
Qed.

Lemma gcnt_C sc0 : gcnt st' sc0 = (if sc' =? sc0 then cnt else 0) + gcnt st sc0.
Proof.
  rewrite !gcnt_unfold, E_groups.
  rewrite (zsum_perm _ _ (Permutation_map (gterm st' sc0) (map_to_list_insert (s_groups st) p (mkGhdr (Some m) ai) p_free))). cbn.
  unfold gterm at 1. cbn. rewrite C_MR_m. fold sc' cnt. f_equal.
  f_equal. apply map_ext_in. intros [b hb] Hin. apply In_map_to_list_regions in Hin || (apply (proj2 (list_elem_of_In _ _)) in Hin; apply elem_of_map_to_list in Hin).
  unfold gterm. cbn. destruct (g_meta hb) as [x|] eqn:Ex; [| reflexivity].
  rewrite (C_MR_other x); [reflexivity|]. intros ->.
  destruct (im_hdr _ _ _ IM _ _ Hin) as (x' & Ex' & Hmem & _). rewrite Ex in Ex'. inversion Ex'. subst x'. rewrite MRm in Hmem. discriminate.
Qed.

Lemma C_get_head h : get_head st' h = get_head st h.
Proof.
  destruct E_ctx as (_ & _ & F3 & _ & _ & _ & _ & _ & _ & _ & F11 & _). destruct h; cbn; unfold active, ctx; rewrite ?F11, ?F3; reflexivity.
Qed.
Lemma C_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. destruct E_ctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _). unfold frontier. rewrite F10. reflexivity. Qed.

(* [comment removed for export] *)
Lemma C_TK u hl : r_hav (get_shadow st (fst p)) !! u = Some hl -> hl_ticks hl (s_tick st).
Proof.
  intros Hu ch Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn in Hu.
  - exact (proj1 (proj2 (ish_ticks _ _ ISH _ _ E)) u hl ch Hu Hin).
  - rewrite lookup_empty in Hu. discriminate.
Qed.
Lemma C_read_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros Hq. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst q) E_shadow). apply (cell_read_hdr_havoc_out p st (proj2 R_align) C_TK q Hq). Qed.
Lemma C_known_out q v : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
Lemma C_unknown_out q : ~ (fst q = fst p /\ snd p <= snd q < snd p + 12) -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite C_read_out by exact Hq. exact K. Qed.
Lemma C_unknown_hdr o : 0 <= o < 12 -> unknown st' (fst p, snd p + o).
Proof.
  intros Ho. unfold unknown, SHd. cbn [fst snd]. rewrite (get_shadow_ext (hdr_havoc p st) st' (fst p) E_shadow).
  apply (cell_read_hdr_havoc_in p st (proj2 R_align) (fst p, snd p + o)); [reflexivity| cbn; lia|].
  cbn [fst snd]. intros v tk H. apply (SH_ghdr (snd p + o) v tk); [clear - Ho; lia| exact H].
Qed.

Lemma hdr0_res b x i : hosts st b x -> (sstart (MR st x) i - IB) mod 16 = 12.
Proof.
  intros Hx. pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG SM]. destruct (hosts_ok _ _ _ IG _ _ Hx) as (a & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [A0 A16].
  unfold sstart, IB, UNIT in *. rewrite (hosts_gbase _ _ _ IM _ _ Hx).
  pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as D1. rewrite A16 in D1. pose proof (Z.div_mod (get_stride (MR st x)) 16 ltac:(lia)) as D2. rewrite SM in D2.
  replace (snd b + 16 + get_stride (MR st x) * i - 4) with (12 + (snd b / 16 + get_stride (MR st x) / 16 * i) * 16) by nia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma C_unknown_any q : unknown st q -> unknown st' q.
Proof.
  intros U. destruct (N.eq_dec (fst q) (fst p)) as [E|NE]; [| apply C_unknown_out; [tauto| exact U]].
  destruct (Z.lt_ge_cases (snd q) (snd p)) as [L1|G1]; [apply C_unknown_out; [lia| exact U]|].
  destruct (Z.lt_ge_cases (snd q) (snd p + 12)) as [L2|G2]; [| apply C_unknown_out; [lia| exact U]].
  replace q with (fst p, snd p + (snd q - snd p)) by (destruct q; cbn in *; subst; f_equal; lia). apply C_unknown_hdr. lia.
Qed.

Lemma C_known_res q v : 12 <= snd q mod 16 -> known st q v -> known st' q v.
Proof. intros R K. apply C_known_out; [| exact K]. intros [_ H]. exact (res_excl _ _ (proj2 R_align) R H). Qed.

(* [comment removed for export] *)
Lemma blk_clear k x i : In k BL -> s_slots st !! bslot k = Some (x, i) -> fst (bslot k) = fst p ->
  snd (bslot k) + get_stride (MR st x) - IB <= snd p \/ snd p + 12 <= snd (bslot k) - IB.
Proof.
  intros Hk Hs Hf. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es).
  destruct SITE as [(Hml & P0 & HO & _)|(Hml & HP & _ & _ & _ & pm & ip & bpm & Hps & Hpm & Hfp & Hip & Ep & _)].
  - exfalso. destruct (ir_orph _ _ _ IR _ HO) as (r' & _ & _ & NG). destruct Hx as [a Hxx].
    rewrite (NG bx) in Hxx; [discriminate|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ a Hxx)) in Es. rewrite Es in Hf. exact Hf.
  - destruct Hpm as [aipm Hpm']. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx) in Es.
    assert (NH : s_groups st !! (fst bpm, sstart (MR st pm) ip) = None) by (rewrite <- Ep; exact p_free).
    assert (Hf2 : fst bx = fst bpm) by (rewrite Es, Ep in Hf; cbn in Hf; exact Hf).
    pose proof (is_part _ _ _ IS _ _ _ i (proj2 (hosts_ok _ _ _ IG _ _ Hx) ) Hi) as P5 || pose proof I as P5.
    destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx).
    pose proof (is_part _ _ _ IS _ _ _ i Hbx Hi) as Q5. cbn zeta in Q5. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hx), <- Es in Q5. unfold one5 in Q5.
    assert (U : In (bslot k) (map bslot BL)) by (apply in_map; exact Hk).
    assert (NH2 : s_groups st !! (fst bx, sstart (MR st x) i) = None).
    { rewrite <- Es. apply none_of. intros Hh. destruct Q5 as (_ & _ & _ & _ & _ & _ & _ & _ & nCD & _). apply nCD. split; [exact U| exact Hh]. }
    assert (NE : x <> pm \/ i <> ip).
    { destruct (aptr_eq_dec x pm) as [->|]; [right| left; congruence]. intros ->.
      pose proof (is_part _ _ _ IS _ _ _ ip Hpm' Hip) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ aipm Hpm')), <- Ep, HP in P.
      unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity].
      pose proof (hosts_inj _ _ _ IM _ _ _ Hx (ex_intro _ aipm Hpm')) as Ebx. rewrite Ebx in Es. rewrite Ep, <- Es. exact U. }
    pose proof (@sep_ext _ _ _ _ IM IG IS pm bpm ip (ex_intro _ aipm Hpm') Hip NH x bx i Hx Hf2 Hi NE NH2) as D.
    rewrite !sstart_succ in D. rewrite Es. cbn [snd]. rewrite Ep. cbn [snd].
    pose proof (stride_ge _ _ _ IG _ _ (ex_intro _ aipm Hpm')) as [SGp _]. unfold IB, UNIT in *. clear - D SGp. lia.
Qed.

Theorem INVL_create : INVL X' st' L BL LS.
Proof.
  destruct E_ctx as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
  destruct R_masks as (W1 & W2 & W3 & W4 & W5 & W6). destruct R_stride16 as [SP SM]. destruct R_align as [P0 P16].
  assert (XO : forall rid, x_orph X' = Some rid -> x_orph X = Some rid /\ m_maplen mr' = 0).
  { intros rid Ho. destruct SITE as [(_ & _ & _ & HO' & _)|(Hml & _ & _ & HO' & _)]; [rewrite HO' in Ho; discriminate| rewrite HO' in Ho; auto]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?E_regions, ?E_next_rid, ?E_reserved, ?F6, ?F7, ?F10, ?F15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite C_frontier. reflexivity.
    + intros rid r H1 H2. rewrite C_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite C_frontier. exact (ir_brkfront rid r H1 H2).
    + intros rid Ho. destruct (XO rid Ho) as [Ho' Hml]. destruct (ir_orph rid Ho') as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
      intros b Hb. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE]; [| exact (NG b Hb)]. exfalso.
      destruct SITE as [(Hml' & _)|(_ & _ & _ & _ & HO0 & _)]; [exact (Hml' Hml)| rewrite HO0 in Ho'; discriminate].
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?E_regions, ?E_areas, ?E_secret, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14; try assumption.
    + destruct ia_ctx as (_ & C2 & C3 & C4). split; [exact E_mc|]. auto.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite C_frontier. auto.
    + intros x mr Hx. assert (K : s_metas st' !! x <> None) by congruence. apply C_keys in K. destruct (s_metas st !! x) as [mr0|] eqn:E; [| congruence]. exact (ia_metas x mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply C_keys in K. apply K. apply Hk. exact Hk2.
    + intros sc0 Hsc0. rewrite (E_usage sc0 Hsc0), (ia_usage sc0 Hsc0), gcnt_C. rewrite Z.eqb_sym. destruct (sc' =? sc0); lia.
  - (* [comment removed for export] *) destruct IM as [Q1 Q2 Q3 Q4 Q5] eqn:EIM; constructor.
    + intros x Hx. destruct (aptr_eq_dec x m) as [E|NE]; [subst x; rewrite C_MR_m, R_mem in Hx; discriminate|]. rewrite (C_MR_other x NE) in Hx |- *. exact (Q1 x Hx).
    + intros x b Hx. rewrite X_zomb. destruct (aptr_eq_dec x m) as [E|NE].
      * subst x. rewrite C_MR_m, R_mem in Hx. inversion Hx. subst b. left. apply C_hosts. left. auto.
      * rewrite (C_MR_other x NE) in Hx. destruct (Q2 x b Hx) as [H|H]; [left; apply C_hosts_old; exact H| right; exact H].
    + intros b h. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NE].
      * intros E. inversion E. subst h. exists m. cbn. rewrite C_MR_m, R_mem. fold last'. auto.
      * intros Hb. destruct (Q3 b h Hb) as (x & Ex & Hmem & Hai). exists x.
        assert (NEx : x <> m) by (intros ->; rewrite MRm in Hmem; discriminate). rewrite (C_MR_other x NEx). auto.
    + intros x Hx. destruct (X_idle x Hx) as [Hx' NE]. destruct (Q4 x Hx') as [E NI]. split; [| exact NI]. rewrite E_metas, lookup_insert_ne by congruence. exact E.
    + intros z Hz. rewrite X_zomb, X_nozomb in Hz. destruct Hz.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. rewrite C_get_head. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite C_MR_other; try reflexivity; intros ->; apply (m_unlisted h); rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros x. destruct (aptr_eqb_spec x m) as [->|NE].
      * rewrite C_MR_m, R_next, R_prev. split; [| reflexivity]. split; [intros [h H]; exfalso; exact (m_unlisted h H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (C_MR_other x NE). apply L5.
    + intros x Hx. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE). apply L6. exact Hx.
    + intros sc x Hx. destruct (L7 sc x Hx) as (A1 & [b Hb] & A3).
      destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (m_unlisted _ Hx)|]. rewrite (C_MR_other x NE).
      split; [exact A1|]. split; [exists b; apply C_hosts_old; exact Hb| exact A3].
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5] eqn:EIG. constructor.
    + intros x b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
      * (* [comment removed for export] *)
        intros E. inversion E. subst x aix. constructor; rewrite ?C_MR_m, ?E_regions; fold sc' last' stride'.
        -- apply C_keys. rewrite m_meta0. discriminate.
        -- exact R_li.
        -- exact R_ai.
        -- destruct R_sc as [A|(A1 & A2 & A3)]; [left; exact A| right]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. intros [h H]. exact (m_unlisted h H).
        -- exact R_freeable.
        -- exact R_maplen.
        -- exact (conj W1 (conj W2 (conj W3 (conj W4 (conj W5 W6))))).
        -- intros NF Hlt. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)|]. destruct R_sc as [[A _]|(_ & L0 & _)]; unfold sc' in *; lia.
        -- intros NF Hsc NI. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
        -- intros NF sc Hin Hnh. exfalso. exact (m_unlisted _ Hin).
        -- exact R_stride.
        -- intros NF Hsc LT. exfalso. destruct X_fresh as [XF|[X63 _]]; [exact (NF XF)| unfold sc' in *; lia].
        -- exact (conj P0 P16).
        -- intros Hml. destruct SITE as [(_ & B0 & _ & _ & _ & r & Hr & Hk & Hlen & Hend)|(Hml0 & _)]; [| exfalso; exact (Hml Hml0)].
           split; [exact B0|]. exists r. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|].
           unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact Hend.
        -- intros Hml. destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & Hip & Ep & FIT & Hsc & Hstr & _)]; [exfalso; exact (Hml1 Hml)|].
           exists pm, ip. rewrite (C_MR_hosted _ _ Hpm). split; [rewrite C_slots_old; [exact Hs| exact p_not_new]|].
           rewrite (hosts_gbase _ _ _ IM _ _ Hpm). split; [exact Hf|]. split; [| split; [exact Hsc| exact Hstr]].
           unfold gend, cnt_of. rewrite sstart'. fold last' cnt. exact FIT.
        -- exact R_full0.
      * (* [comment removed for export] *)
        intros Hb. pose proof (G1 x b aix Hb) as GO. assert (Hx : hosts st b x) by (exists aix; exact Hb).
        pose proof (C_hosts_old_ne _ _ Hx) as NEx. assert (NF : x_fresh X <> Some x) by (rewrite X_fresh_old; discriminate).
        assert (NF' : x_fresh X' <> Some x) by (destruct X_fresh as [XF|[_ XF]]; rewrite XF; [congruence| rewrite X_fresh_old; discriminate]).
        destruct GO; constructor; rewrite ?(C_MR_other x NEx), ?E_regions; try assumption.
        -- apply C_keys. exact g_present.
        -- intros _. exact (g_partial NF).
        -- intros _. exact (g_unlisted NF).
        -- intros _. exact (g_rest NF).
        -- intros _. exact (g_under NF).
        -- intros Hml. destruct (g_nest Hml) as (px & ix & Hs & REST). exists px, ix.
           destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
           split; [rewrite C_slots_old; [exact Hs| exact (old_slot_not_new _ _ _ Hs)]| exact REST].
    + intros b aix. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb]; [discriminate| exact (G2 b aix)].
    + intros m1 m2 b1 b2 ai1 ai2. rewrite !C_groups.
      destruct (aptr_eqb_spec b1 p) as [->|N1]; destruct (aptr_eqb_spec b2 p) as [->|N2].
      * intros E1 E2. inversion E1. inversion E2. subst. reflexivity.
      * intros E1 H2. inversion E1. subst m1 ai1. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai2 H2)). fold last' sc'. intros P1 P2 Esc.
        exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H2) ltac:(rewrite X_fresh_old; discriminate) P2) as IN. rewrite <- Esc, (NOPART P1) in IN. exact IN.
      * intros H1 E2. inversion E2. subst m2 ai2. rewrite C_MR_m, (C_MR_hosted _ _ (ex_intro _ ai1 H1)). fold last' sc'. intros P1 P2 Esc.
        exfalso. pose proof (g_partial _ _ _ _ _ _ (G1 _ _ _ H1) ltac:(rewrite X_fresh_old; discriminate) P1) as IN. rewrite Esc, (NOPART P2) in IN. exact IN.
      * intros H1 H2. rewrite (C_MR_hosted _ _ (ex_intro _ ai1 H1)), (C_MR_hosted _ _ (ex_intro _ ai2 H2)). exact (G3 m1 m2 b1 b2 ai1 ai2 H1 H2).
    + intros rid r Hr Hk Ho. rewrite E_regions in Hr.
      destruct (N.eq_dec rid (fst p)) as [->|NE].
      * destruct SITE as [(Hml & B0 & HO & _)|(Hml & _ & _ & HO' & HO & _)].
        -- exists m. split; [apply C_hosts; left; split; [destruct p; cbn in B0 |- *; subst; reflexivity| reflexivity]|]. rewrite C_MR_m. exact Hml.
        -- destruct (G4 (fst p) r Hr Hk ltac:(rewrite HO; discriminate)) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
      * assert (Ho0 : x_orph X <> Some rid).
        { destruct SITE as [(_ & _ & HO & _)|(_ & _ & _ & HO' & HO & _)]; [rewrite HO; congruence| rewrite HO; discriminate]. }
        destruct (G4 rid r Hr Hk Ho0) as (x & Hx & Hmlx). exists x. split; [apply C_hosts_old; exact Hx| rewrite (C_MR_hosted _ _ Hx); exact Hmlx].
    + intros b h. rewrite C_groups, E_regions. destruct (aptr_eqb_spec b p) as [->|NEb]; [| exact (G5 b h)]. intros _.
      destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & Hpm & Hf & _)]; [exists r; auto|].
      destruct Hpm as [a Hpm]. destruct (G5 _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto.
  - (* [comment removed for export] *) destruct IS as [S1' S2 S3 S4 S5 S6] eqn:EIS. constructor.
    + intros s x i Hs. destruct (C_slots s) as [[Es NS]|(j & Hj & -> & Es)].
      * rewrite Es in Hs. destruct (S1' s x i Hs) as ([b Hb] & Hi & E). rewrite (C_MR_hosted _ _ Hb). split; [exists b; apply C_hosts_old; exact Hb| auto].
      * rewrite Es in Hs. inversion Hs. subst x i. rewrite C_MR_m. fold last'. split; [exists p; apply C_hosts; left; auto|]. split; [lia|]. rewrite slot'. reflexivity.
    + intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * rewrite C_MR_m in Hi |- *. rewrite slot'. apply C_slots_new. fold last' in Hi. lia.
      * rewrite (C_MR_hosted _ _ Hx) in Hi |- *. rewrite C_slots_old; [exact (S2 b x i Hx Hi)|].
        apply (old_hosts_not_new_slot b x i Hx Hi) || (intros N; destruct N as (j & Hj & E); exact (old_slot_not_new _ _ _ (S2 b x i Hx Hi) (ex_intro _ j (conj Hj E)))).
    + intros b x aix i. rewrite C_groups. destruct (aptr_eqb_spec b p) as [->|NEb].
      * intros E Hi. inversion E. subst x aix. rewrite C_MR_m in Hi |- *. cbn zeta. rewrite slot', C_groups. fold last' in Hi.
        pose proof (X_part i Hi) as P5.
        eapply one5_iff_create; [exact P5| |]; cbn.
        -- intros Hin. apply in_map_iff in Hin as (k & Ek & Hk). apply (blk_not_new k Hk). exists i. split; [clear -Hi; lia| exact Ek].
        -- destruct (aptr_eqb_spec (fst p, snd p + UNIT + stride' * i) p) as [Eip|NE]; [exfalso; apply p_not_new; exists i; split; [clear -Hi; lia| symmetry; exact Eip]|].
           rewrite (new_not_group i ltac:(clear -Hi; lia)). intros H; apply H; reflexivity.
      * intros Hb Hi. assert (Hx : hosts st b x) by (exists aix; exact Hb).
        rewrite (C_MR_hosted _ _ Hx) in Hi |- *. cbn zeta. rewrite C_groups.
        pose proof (S3 b x aix i Hb Hi) as P5. cbn zeta in P5.
        set (s := slot_start' (MR st x) i) in *.
        assert (NSs : ~ nslot s) by (apply (old_slot_not_new s x i); exact (S2 b x i Hx Hi)).
        destruct (aptr_eqb_spec s p) as [Esp|NEsp].
        -- (* [comment removed for export] *)
           destruct SITE as [(_ & B0 & _ & _ & HPX & _)|(_ & HPX & HPX' & _)].
           ++ exfalso. rewrite Esp in *. pose proof (S2 b x i Hx Hi) as Hs. fold s in Hs. rewrite Esp in Hs.
              destruct (S1' _ _ _ Hs) as ([bb Hbb] & _ & Eps). rewrite (slot_start'_eq _ _ _ IM _ _ _ Hbb) in Eps.
              pose proof (sstart0 _ _ _ IM _ _ Hbb). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hbb ltac:(lia)).
              destruct (hosts_ok _ _ _ IG _ _ Hbb) as (a0 & _ & GO0). pose proof (g_align _ _ _ _ _ _ GO0) as [A00 _].
              apply (f_equal snd) in Eps. cbn in Eps. unfold UNIT in *. clear - B0 Eps H H0 A00. lia.
           ++ rewrite Esp in P5 |- *. rewrite HPX in P5. rewrite HPX'.
              revert P5. unfold one5. clear. intros P5.
              assert (NN : ~ (@None aptr = Some p)) by discriminate. assert (SS : Some (mkGhdr (Some m) ai) <> None) by discriminate.
              tauto.
        -- eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P5].
           split.
           ++ intros HPs. exfalso. destruct SITE as [(_ & _ & _ & _ & HPX & _)|(_ & HPX & _)]; rewrite HPX in HPs; [discriminate| inversion HPs; exact (NEsp (eq_sym H0))].
           ++ intros HPs. exfalso. destruct (X_pend' _ HPs) as (j & Hj & Ej). apply NSs. exists j. split; [fold last' in Hj; lia| exact Ej].
    + intros s Hs. destruct (X_pend' _ Hs) as (j & Hj & ->). rewrite C_slots_new; [discriminate| fold last' in Hj; lia].
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (x & i & Hs & REST). exists x, i.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hbx] & _). rewrite (C_MR_hosted _ _ Hbx).
      split; [rewrite C_slots_old; [exact Hs| exact (blk_not_new k Hk)]| exact REST].
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6] eqn:EISH.
    assert (REGp : exists r, s_regions st !! fst p = Some r /\ r_kind r = RKGroup).
    { destruct SITE as [(_ & _ & _ & _ & _ & r & Hr & Hk & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs & [a Hpm] & Hf & _)]; [exists r; auto|].
      destruct (ig_region _ _ _ IG _ _ Hpm) as (r & Hr & Hk). exists r. rewrite <- Hf. auto. }
    constructor.
    + intros rid sh. rewrite E_shadow, E_regions. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst p)) as [->|NE].
      * intros _. exact REGp.
      * rewrite lookup_insert_ne by congruence. exact (D1 rid sh).
    + intros rid sh Hsh. rewrite E_tick. rewrite E_shadow in Hsh. exact (TKS_hdr_havoc st p D2 rid sh Hsh).
    + intros b x i Hx Hi. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * rewrite C_MR_m in Hi |- *. rewrite sstart'. apply C_known_out; [| apply SH_hdr0; unfold cnt_of in Hi; fold last' cnt in Hi; exact Hi].
        cbn. intros [_ H]. unfold IB, UNIT in H. destruct (Z.eq_dec i 0) as [->|NZ]; [lia|]. unfold cnt_of in Hi. assert (stride' * 1 <= stride' * i) by nia. lia.
      * rewrite (C_MR_hosted _ _ Hx) in Hi |- *. apply C_known_res; [cbn; rewrite (hdr0_res _ _ i Hx); lia| exact (D3 b x i Hx Hi)].
    + intros b x o Hx Ho. apply C_hosts in Hx as [[-> ->]|[NEb Hx]]; [apply C_unknown_hdr; exact Ho| apply C_unknown_any; exact (D4 b x o Hx Ho)].
    + intros b x px ix Hx Hml Hs. apply C_hosts in Hx as [[-> ->]|[NEb Hx]].
      * (* [comment removed for export] *)
        rewrite C_MR_m in Hml. rewrite (C_slots_old p p_not_new) in Hs.
        destruct SITE as [(Hml1 & _)|(_ & _ & _ & _ & _ & pm & ip & bpm & Hs0 & Hpm & Hf & Hip & Ep & _ & _ & _ & (v3 & K3 & E3 & R3) & K2 & K1 & Q)]; [exfalso; exact (Hml1 Hml)|].
        rewrite Hs0 in Hs. inversion Hs. subst px ix. rewrite (C_MR_hosted _ _ Hpm), (hosts_gbase _ _ _ IM _ _ Hpm). cbn zeta.
        split; [exists v3; split; [apply C_known_out; [cbn; lia| exact K3]| auto]|].
        split; [apply C_known_out; [cbn; lia| exact K2]|]. split; [apply C_known_out; [cbn; lia| exact K1]| exact Q].
      * rewrite (C_MR_hosted _ _ Hx) in Hml. rewrite (C_slots_old b (old_hosts_not_new _ _ Hx)) in Hs.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bpx Hpx] & _ & _). rewrite (C_MR_hosted _ _ Hpx).
        destruct (D5 b x px ix Hx Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn zeta.
        destruct (hosts_ok _ _ _ IG _ _ Hx) as (ax & Hbx & GOx). pose proof (g_align _ _ _ _ _ _ GOx) as [A0 A16]. unfold UNIT in A16.
        assert (RS : forall d r, 0 <= r < 16 -> d = r - 16 -> 12 <= r -> 12 <= (snd b + d) mod 16).
        { intros d r Hr -> H12. pose proof (Z.div_mod (snd b) 16 ltac:(lia)) as Db. rewrite A16 in Db.
          replace (snd b + (r - 16)) with (r + (snd b / 16 - 1) * 16) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. exact H12. }
        split; [exists v3; split; [apply C_known_res; [cbn; replace (snd b - 3) with (snd b + (13 - 16)) by lia; apply (RS _ 13); lia| exact K3]| auto]|].
        split; [apply C_known_res; [cbn; replace (snd b - 2) with (snd b + (14 - 16)) by lia; apply (RS _ 14); lia| exact K2]|].
        split; [apply C_known_res; [cbn; replace (snd b - 1) with (snd b + (15 - 16)) by lia; apply (RS _ 15); lia| exact K1]| exact Q].
    + intros k x i Hk Hs. rewrite (C_slots_old _ (blk_not_new k Hk)) in Hs.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bx Hx] & Hi & Es). rewrite (C_MR_hosted _ _ Hx).
      pose proof (D6 k x i Hk Hs) as B. cbn zeta in B |- *. destruct B as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      (* [comment removed for export] *)
      assert (OUT : forall o, snd (bslot k) - IB <= o < snd (bslot k) + get_stride (MR st x) - IB -> ~ (fst (bslot k) = fst p /\ snd p <= o < snd p + 12)).
      { intros o Ho [Hf Hin]. pose proof (blk_clear k x i Hk Hs Hf) as D. unfold IB in *. clear - Ho Hin D. lia. }
      destruct (is_blocks _ _ _ IS k Hk) as (x' & i' & Hs' & Hoff & Hn & Hfit). rewrite Hs in Hs'. inversion Hs'. subst x' i'.
      pose proof (stride_ge _ _ _ IG _ _ Hx) as [SG _]. unfold IB, UNIT in *.
      assert (K : forall o v, snd (bslot k) - 4 <= o < snd (bslot k) + get_stride (MR st x) - 4 -> known st (fst (bslot k), o) v -> known st' (fst (bslot k), o) v).
      { intros o v Ho Ko. apply C_known_out; [apply (OUT o Ho)| exact Ko]. }
      split; [apply K; [lia| exact A1]|]. split; [apply K; [lia| exact A2]|]. split; [apply K; [lia| exact A3]|]. split; [apply K; [lia| exact A4]|].
      split; [exact A5|]. split.
      * intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). split; [apply K; [lia| exact B1]|]. split; [apply K; [lia| exact B2]|]. split; [apply K; [lia| exact B3]|].
        split; [apply K; [lia| exact B4]|]. split; [apply K; [lia| exact B5]| exact B6].
      * split; [intros Hr; apply K; [lia| apply A7; exact Hr]|]. intros a Ha. apply C_unknown_any. apply A8. exact Ha.
Qed.

End CREATE.


End CeilWrap.
End MI_WCreate.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WFree2.
Import MI_WGroup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Cnt.
Import MI_TF2.
Import MI_WEnframe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma havoc_le0 p n st : n <= 0 -> havoc p n st = st.
Proof. intros H. unfold havoc. destruct (Z.leb_spec n 0); [reflexivity| lia]. Qed.

Section ENFRAME.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (idx n : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : hosts st bg g.
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let c : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some c.
Hypothesis Hn : 0 <= n.
Hypothesis Hfit : n + IB <= get_stride (MR st g).
Hypothesis TF : TF2 st.
Hypothesis Hres : get_stride (MR st g) - IB - n < 2 ^ 32.
Let X' := xpend X None.
Let stride := get_stride (MR st g).
Let slack := (stride - IB - n) / UNIT.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma ef_gbase : gbase (MR st g) = bg. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
Lemma ef_c : aadd (default (0%N, 0) (m_mem (get_meta_rec st g))) (UNIT + get_stride (get_meta_rec st g) * idx) = c.
Proof. fold (MR st g). change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. unfold c, sstart, aadd. rewrite ef_gbase. f_equal. lia. Qed.
Lemma ef_slot : slot_start' (MR st g) idx = c. Proof. exact (slot_start'_eq _ _ _ IM _ _ idx Hg). Qed.
Lemma ef_slots : s_slots st !! c = Some (g, idx). Proof. rewrite <- ef_slot. exact (is_total _ _ _ IS _ _ _ Hg Hidx). Qed.
Lemma ef_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma ef_c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X st L BL LS INV bg g idx Hg) as R. unfold c. cbn [snd]. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.
Lemma ef_NH : s_groups st !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity].
Qed.
Lemma ef_NB k : In k BL -> bslot k <> c.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ idx Hb Hidx) as P5. cbn zeta in P5. rewrite ef_slot, HP in P5.
  intros Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk.
Qed.
Lemma ef_q_range off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB -> 0 <= (snd c + UNIT * off - (snd bg + UNIT)) / UNIT < 2 ^ 16.
Proof.
  intros Ho Hf. destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  pose proof (g_stride _ _ _ _ _ _ GO) as GS. pose proof (g_sc _ _ _ _ _ _ GO) as SC. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold c. cbn [snd]. unfold sstart. rewrite ef_gbase. fold stride. pose proof ef_stride as [S16 SM].
  replace (snd bg + UNIT + stride * idx + UNIT * off - (snd bg + UNIT)) with ((stride / 16 * idx + off) * 16)
    by (unfold UNIT; pose proof (Z.div_mod stride 16 ltac:(lia)); nia).
  unfold UNIT. rewrite Z.div_mul by lia.
  assert (0 <= stride / 16 * idx) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  split; [lia|].
  destruct SC as [[SC1 _]|(SC63 & L0 & _)].
  - destruct (GS ltac:(lia)) as (_ & _ & LT). unfold cnt_of in LT. fold stride in LT.
    assert (stride * idx <= stride * (m_last_idx (MR st g))) by (apply Z.mul_le_mono_nonneg_l; lia).
    pose proof (Z.div_mod stride 16 ltac:(lia)). unfold IB, UNIT in Hf. nia.
  - rewrite L0 in Hidx. assert (idx = 0) by lia. subst idx. rewrite Z.mul_0_r. lia.
Qed.

(* [comment removed for export] *)
Definition pp (off : Z) : aptr := aadd c (UNIT * off).
Definition ee : aptr := aadd c (stride - IB).
Definition resv (off : Z) : Z := snd ee - snd (pp off) - n.
Definition qv (off : Z) : Z := (snd (pp off) - (snd bg + UNIT)) / UNIT.
Definition EL (off : Z) : list (aptr * Z) :=
  (if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd (pp off) (-4), 0)] else [])
  ++ [(aadd (pp off) (-2), qv off); (aadd (aadd (pp off) (-2)) 1, Z.shiftr (qv off) 8); (aadd (pp off) (-3), idx)]
  ++ (if negb (resv off =? 0) then [(aadd ee (- resv off), 0)] else [])
  ++ (if 5 <=? resv off then [(aadd ee (-4), resv off); (aadd (aadd ee (-4)) 1, Z.shiftr (resv off) 8); (aadd (aadd ee (-4)) 2, Z.shiftr (resv off) 16); (aadd (aadd ee (-4)) 3, Z.shiftr (resv off) 24); (aadd ee (-5), 0)] else [])
  ++ [(aadd (pp off) (-3), Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5)].

Lemma EL_eq off : ef_list st g idx n off = EL off.
Proof.
  unfold ef_list, EL. rewrite (p0_eq st g idx n off). rewrite ef_c. fold (MR st g). fold stride.
  change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). rewrite ef_gbase. reflexivity.
Qed.

Lemma enframe_at_EL off : enframe_at st g idx n off = (wrs (EL off) st, pp off).
Proof. rewrite (enframe_at_eq st g idx n off), EL_eq, (p0_eq st g idx n off), ef_c. reflexivity. Qed.

Definition stw (off : Z) : mstate := wrs (EL off) st.
Definition stf (off : Z) : mstate := havoc (pp off) n (stw off).

Lemma stw_TKS off : TKS (stw off) (s_tick st).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw_tick off : s_tick (stw off) = s_tick st. Proof. exact (proj2 (wrs_ctrl (EL off) st)). Qed.
Lemma stw_ctrl off : ctrl_eq st (stw off). Proof. exact (proj1 (wrs_ctrl (EL off) st)). Qed.
Lemma pp16 off : snd (pp off) mod 16 = 0.
Proof. unfold pp, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, ef_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.
Lemma stw_hav off u hl : r_hav (get_shadow (stw off) (fst (pp off))) !! u = Some hl -> hl_ticks hl (s_tick (stw off)).
Proof. intros Hu ch Hch. rewrite stw_tick. pose proof (stw_TKS off) as TK. rewrite <- (stw_tick off) in TK. rewrite <- (stw_tick off). exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.

Lemma stf_ctrl off : ctrl_eq st (stf off) /\ s_tick (stf off) = s_tick st.
Proof.
  destruct (havoc_ctrl (pp off) n (stw off)) as [C T]. split; [exact (ctrl_eq_trans _ _ _ (stw_ctrl off) C)| rewrite T; apply stw_tick].
Qed.

Lemma stf_read_out off r : ~ (fst r = fst bg /\ snd (pp off) <= snd r < snd (pp off) + n) ->
  cell_read (get_shadow (stf off) (fst r)) (snd r) = cell_read (get_shadow (stw off) (fst r)) (snd r).
Proof.
  intros Hr. unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off)). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma EL_addrs off a : 0 <= off -> UNIT * off + n <= stride - IB -> In a (map fst (EL off)) ->
  fst a = fst bg /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd (pp off) <= snd a < snd (pp off) + n).
Proof.
  intros Ho Hf Hin. pose proof ef_stride as [S16 _].
  assert (R : 0 <= resv off) by (unfold resv, ee, pp, aadd; cbn [fst snd]; unfold IB, UNIT in *; lia).
  unfold EL in Hin.
  destruct (Z.eqb_spec off 0) as [O0|O0]; destruct (Z.eqb_spec (resv off) 0) as [R0|R0]; destruct (Z.leb_spec 5 (resv off)) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold resv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; unfold c; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

(* [comment removed for export] *)
Lemma stf_known_w off x w : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = Some w -> known (stf off) (fst bg, x) (Z.land w 255).
Proof.
  intros Ho Hf Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.

Lemma stf_known_old off x v : 0 <= off -> UNIT * off + n <= stride - IB ->
  ~ (snd (pp off) <= x < snd (pp off) + n) ->
  lastw (EL off) (fst bg, x) None = None -> known st (fst bg, x) v -> known (stf off) (fst bg, x) v.
Proof.
  intros Ho Hf Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out off (fst bg, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw (EL off) st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.

Lemma EL_not_in off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> ~ In (fst bg, a) (map fst (EL off)).
Proof. intros Ho Hf Ha Hin. destruct (EL_addrs off _ Ho Hf Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

Lemma stf_unknown off a : 0 <= off -> UNIT * off + n <= stride - IB ->
  snd (pp off) <= a < snd (pp off) + n -> unknown (stf off) (fst bg, a).
Proof.
  intros Ho Hf Ha. unfold unknown, SHd, stf. cbn [fst snd].
  destruct (cell_read_havoc_in (pp off) n (stw off) (pp16 off) ltac:(lia) (stw_hav off) (fst bg, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc. rewrite wrs_cells_other in Hc by (apply EL_not_in; assumption).
  rewrite stw_tick. change (fst (pp off)) with (fst bg) in Hc.
  apply (TF2_interior_old X st L BL LS INV g bg idx Hg Hidx ef_NH TF a v tk Hc).
  unfold pp, aadd, c in Ha. cbn [fst snd] in Ha. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia.
Qed.

(* [comment removed for export] *)
Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd, c; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd, c; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.
Ltac lastw_eval :=
  unfold EL; cbn [lastw app negb]; repeat aeq; reflexivity.

Lemma res_eq off : resv off = stride - IB - UNIT * off - n.
Proof. unfold resv, ee, pp, aadd. cbn [snd]. lia. Qed.
Lemma qv_eq off : qv off = (snd c + UNIT * off - (snd bg + UNIT)) / UNIT.
Proof. reflexivity. Qed.

Lemma blk_ok off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  blk_shadow_ok (stf off) ((c, off), n) g idx.
Proof.
  intros Ho Hf. pose proof ef_stride as [S16 SM].
  destruct (stf_ctrl off) as [CE TK].
  assert (MRE : MR (stf off) g = MR st g) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof (res_eq off) as RE.
  destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ef_gbase. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with (resv off) by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bg - UNIT) / UNIT) with (qv off) by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
  pose proof (ef_q_range off Ho Hf) as QR.
  replace ((snd c + UNIT * off - (snd bg + UNIT)) / UNIT) with (qv off) in QR by (unfold qv, pp, aadd; cbn [snd]; f_equal; lia).
  assert (R0 : 0 <= resv off) by (rewrite RE; unfold IB, UNIT in *; lia).
  assert (NP : forall x, x < snd (pp off) \/ snd (pp off) + n <= x -> ~ (snd (pp off) <= x < snd (pp off) + n)) by (intros; lia).
  assert (PP : snd (pp off) = snd c + UNIT * off) by reflexivity.
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - (* [comment removed for export] *) destruct (Z.eqb_spec off 0) as [O0|O0].
    + apply (stf_known_old off); [lia| exact Hf| apply NP; lia| |].
      * unfold EL. rewrite O0 at 1. cbn [Z.eqb negb app lastw].
        destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
      * subst off. pose proof (ish_hdr0 _ _ ISH bg g idx (ex_intro _ ai Hb) ltac:(unfold cnt_of; lia)) as K.
        unfold c. cbn [snd]. replace (sstart (MR st g) idx + UNIT * 0 - 4) with (sstart (MR st g) idx - IB) by (unfold IB, UNIT; lia). exact K.
    + apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
      unfold EL. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0). cbn [negb app lastw].
      destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (idx + 32 * Z.min (resv off) 5) with (Z.land (Z.land idx 31 + Z.shiftl (if 5 <=? resv off then 5 else resv off) 5) 255).
    2:{ replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 (resv off)).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (negb (resv off =? 0)); destruct (5 <=? resv off); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_1_r.
    apply (stf_known_w off); [lia| exact Hf| apply NP; lia|].
    unfold EL. destruct (off =? 0); destruct (Z.eqb_spec (resv off) 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : resv off < 2 ^ 32).
    { rewrite RE. fold stride in Hres. unfold UNIT. lia. }
    assert (E5 : (5 <=? resv off) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply (stf_known_w off); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|];
         unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; rewrite ?RE; unfold IB, UNIT in *; lia|].
    unfold EL; rewrite E5, EZ; destruct (off =? 0); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - resv off) with (snd (pp off) + n) by (rewrite RE, PP; lia).
    apply (stf_known_w off _ 0); [lia| exact Hf| apply NP; lia|].
    assert (EZ : (resv off =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold EL; rewrite EZ. destruct (off =? 0); destruct (Z.leb_spec 5 (resv off)); cbn [negb lastw app];
      try (destruct (Z.eq_dec (resv off) 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. apply (stf_unknown off); [lia| exact Hf|]. rewrite PP. exact Ha.
Qed.


(* [comment removed for export] *)
Lemma ef_INVL off : 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
  INVL X' (stf off) L (((c, off), n) :: BL) LS.
Proof.
  intros Ho Hf. destruct (stf_ctrl off) as [CE TK]. pose proof ef_stride as [S16 _].
  destruct Hg as [ai Hb] eqn:EHg.
  apply (INVL_add_block X st (stf off) L BL LS c off n INV HP CE TK).
  - intros m i Hs q Hq. rewrite ef_slots in Hs. inversion Hs. subst m i.
    assert (NQ : ~ (fst q = fst bg /\ snd (pp off) <= snd q < snd (pp off) + n)).
    { intros [F R]. apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|]. unfold pp, aadd, c in R. cbn [snd] in R. rewrite sstart_succ. fold stride. unfold IB, UNIT in *. lia. }
    rewrite (stf_read_out off q NQ). unfold stw. apply wrs_read_other.
    intros Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & R & _). apply Hq. unfold inT, c. cbn [fst snd]. split; [exact F|].
    rewrite sstart_succ. fold stride. unfold c in R. cbn [snd] in R. unfold IB in *. lia.
  - intros rid sh Hsh. assert (REG' : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hb).
    revert rid sh Hsh. change (DOMS st (stf off)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
    + apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (EL_addrs off q ltac:(lia) Hf Hin) as (F & _). rewrite F. exact REG'.
  - change (TKS (stf off) (s_tick st)). unfold stf. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply stw_TKS.
    + rewrite <- (stw_tick off). apply TKS_havoc; [apply pp16| lia| rewrite stw_tick; apply stw_TKS].
  - intros m i Hs. rewrite ef_slots in Hs. inversion Hs. subst m i. split; [exact Ho|]. split; [exact Hn|]. split; [exact Hf|].
    apply blk_ok; assumption.
Qed.

Theorem enframe_ft ctr (Post : mled -> mstate * optr -> Prop) :
  (forall off st' , 0 <= off <= 255 -> UNIT * off + n <= stride - IB ->
     INVL X' st' L (((c, off), n) :: BL) LS -> ctrl_eq st st' -> s_tick st' = s_tick st ->
     Post L (st', Some (aadd c (UNIT * off)))) ->
  ftree L (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) Post.
Proof.
  intros HPost. pose proof ef_stride as [S16 SM].
  assert (KR : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) by (intros q v; apply (known_range _ _ _ _ _ q v INV)).
  assert (SL : 0 <= slack) by (unfold slack; apply Z.div_pos; unfold IB, UNIT in *; lia).
  assert (SL16 : UNIT * slack <= stride - IB - n).
  { unfold slack, UNIT, IB in *. pose proof (Z.div_mod (stride - 4 - n) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (stride - 4 - n) 16 ltac:(lia)). lia. }
  assert (GO : forall v, 0 <= v < 256 ->
    ftree L (let '(st1, p) := enframe_at st g idx n (fold_off v slack) in ret (havoc p n st1, Some p)) Post).
  { intros v Hv. pose proof (fold_off_le v slack Hv SL) as FO.
    assert (F255 : fold_off v slack <= 255).
    { unfold fold_off in *. destruct (Z.ltb_spec slack v); [| lia]. cbn zeta in FO. unfold fold_off in FO. lia. }
    rewrite enframe_at_EL. cbn [ftree ret]. apply HPost.
    - lia.
    - unfold UNIT, IB in *. lia.
    - apply ef_INVL; [lia|]. unfold UNIT, IB in *. lia.
    - exact (proj1 (stf_ctrl _)).
    - exact (proj2 (stf_ctrl _)). }
  unfold enframe_full, enframe_read_off. fold (MR st g). fold stride. rewrite ef_slot.
  change ((stride - IB - n) / UNIT) with slack.
  apply rd8_ftree; [intros v; apply KR|]. intros b3 Hb3.
  destruct (b3 =? 0); cbn [negb].
  - apply GO. apply land255_range.
  - apply rd16_ftree; [intros q v; apply KR|]. intros o16 Ho16. apply GO. apply land255_range.
Qed.
End ENFRAME.


End CeilWrap.
