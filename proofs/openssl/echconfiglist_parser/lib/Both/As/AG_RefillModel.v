(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AllocRep AllocRepFacts AW_Efs AW_Populate AG_WFHit AS_Refill1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma zlen_app {A} : forall (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_firstn {A} : forall k (l : list A), (k <= length l)%nat -> zlen (firstn k l) = Z.of_nat k.
Proof. intros. unfold zlen. rewrite length_firstn. lia. Qed.
Lemma zlen_skipn {A} : forall k (l : list A), zlen (skipn k l) = zlen l - Z.of_nat (Nat.min k (length l)).
Proof. intros. unfold zlen. rewrite length_skipn. lia. Qed.

Lemma carve_asc_length' : forall b s i k, length (carve_asc b s i k) = k.
Proof. intros b s i k. revert i. induction k as [|k IH]; intros i; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma in_carve_asc : forall b s i k x, In x (carve_asc b s i k) <-> exists j, 0 <= j < Z.of_nat k /\ x = Z.shiftr (b + (i + j) * s) kCompactPtrScale.
Proof.
  intros b s i k. revert i. induction k as [|k IH]; intros i x.
  - cbn. split; [intros []| intros (j & Hj & _); lia].
  - cbn [carve_asc]. rewrite Nat2Z.inj_succ. split.
    + intros [<-|Hin].
      * exists 0. split; [lia|]. rewrite Z.add_0_r. reflexivity.
      * apply IH in Hin. destruct Hin as (j & Hj & ->). exists (j + 1). split; [lia|]. f_equal. f_equal. lia.
    + intros (j & Hj & ->). destruct (Z.eq_dec j 0) as [->|NZ].
      * left. rewrite Z.add_0_r. reflexivity.
      * right. apply IH. exists (j - 1). split; [lia|]. f_equal. f_equal. lia.
Qed.

Lemma shiftr4_mul16 : forall y, Z.shiftr (y * 16) kCompactPtrScale = y.
Proof. intros y. unfold kCompactPtrScale. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. apply Z.div_mul. lia. Qed.

(* [comment removed for export] *)
Lemma nodup_slots_length : forall (f : Z -> Z) (l : list Z) (K : Z),
  NoDup l -> 0 <= K ->
  (forall x, In x l -> 0 <= f x < K) ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  zlen l <= K.
Proof.
  intros f l K ND HK RNG INJ.
  assert (NDf : NoDup (map f l)).
  { clear RNG. induction l as [|x l IH]; cbn; constructor.
    - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & E & Hy).
      inversion ND; subst. assert (y = x) by (apply INJ; [right; exact Hy| left; reflexivity| exact E]). subst y. contradiction.
    - inversion ND; subst. apply IH; [assumption|]. intros a b Ha Hb. apply INJ; right; assumption. }
  assert (INCL : incl (map f l) (map Z.of_nat (seq 0 (Z.to_nat K)))).
  { intros v Hv. apply in_map_iff in Hv. destruct Hv as (x & <- & Hx). specialize (RNG x Hx).
    apply in_map_iff. exists (Z.to_nat (f x)). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length NDf INCL) as LEN. rewrite !length_map, length_seq in LEN. unfold zlen. lia.
Qed.

(* [comment removed for export] *)
Lemma NoDup_app_intro : forall (l1 l2 : list Z), NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2 N1 N2 D; cbn; [exact N2|].
  inversion N1; subst. constructor.
  - intros Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [contradiction| exact (D x (or_introl eq_refl) Hin)].
  - apply IH; [assumption| assumption|]. intros y Hy1 Hy2. apply (D y); [right; exact Hy1| exact Hy2].
Qed.

(* [comment removed for export] *)
Lemma flat_map_perm_add : forall (g g' : Z -> list Z) (L : list Z) (c : Z) (extra : list Z),
  NoDup L -> In c L ->
  (forall x, In x L -> x <> c -> g' x = g x) ->
  Permutation (g' c) (extra ++ g c) ->
  Permutation (flat_map g' L) (extra ++ flat_map g L).
Proof.
  intros g g' L c extra ND Hin EQ P. revert ND Hin EQ. induction L as [|x L IH]; intros ND Hin EQ; [destruct Hin|].
  inversion ND; subst. cbn [flat_map]. destruct Hin as [->|Hin].
  - rewrite (flat_map_ext_in g g' L) by (intros y Hy; apply EQ; [right; exact Hy| intros ->; contradiction]).
    rewrite app_assoc. apply Permutation_app_tail. exact P.
  - assert (NE : x <> c) by (intros ->; contradiction).
    rewrite (EQ x (or_introl eq_refl) NE).
    eapply Permutation_trans; [apply Permutation_app_head; apply IH; [assumption| assumption| intros y Hy; apply EQ; right; exact Hy]|].
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma free_array_count : forall st c, WF st -> 0 <= c < kNumClasses -> class_size c <> 0 ->
  class_size c * rg_num_freed (get_region st c) <= rg_allocated_user (get_region st c).
Proof.
  intros st c W Hc NZ. pose proof (WF_region st c W Hc) as RO.
  pose proof (class_size_table_facts c ltac:(unfold kNumClasses in Hc; lia)) as (T1 & T2 & _).
  rewrite (ro_numfreed _ _ RO).
  assert (POS : 0 < class_size c) by lia.
  assert (AMOD : rg_allocated_user (get_region st c) mod class_size c = 0) by (apply (ro_alloc_mod _ _ RO); exact NZ).
  assert (A0 : 0 <= rg_allocated_user (get_region st c)) by (apply (ro_alloc_nonneg _ _ RO)).
  (* [comment removed for export] *)
  assert (ND : NoDup (rg_free_array (get_region st c))).
  { destruct W as (_ & ND & _). unfold carved_addr_list in ND.
    apply NoDup_app_l in ND.
    assert (INc : In c (map Z.of_nat (seq 0 32))) by (apply classes_in; unfold kNumClasses in Hc; lia).
    apply in_split in INc. destruct INc as (l1 & l2 & EL). rewrite EL, flat_map_app in ND. cbn [flat_map] in ND.
    apply NoDup_app_r, NoDup_app_l, NoDup_app_l in ND.
    remember (rg_free_array (get_region st c)) as l eqn:El. clear - ND.
    induction l as [|x l IH]; constructor.
    - inversion ND; subst. intros Hx. apply H1. apply in_map_iff. exists x. split; [reflexivity| exact Hx].
    - inversion ND; subst. apply IH. assumption. }
  set (csz := class_size c) in *. set (au := rg_allocated_user (get_region st c)) in *.
  assert (X : zlen (rg_free_array (get_region st c)) <= au / csz).
  { apply (nodup_slots_length (fun cp => cp * 16 / csz)); [exact ND| apply Z.div_pos; lia| |].
    - intros x Hx. destruct (ro_fa_elems _ _ RO x Hx) as (E1 & E2 & _ & E4). rewrite shiftl4 in E2, E4. fold csz au in E2, E4 |- *.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      pose proof (mult_below csz (x * 16) au POS E4 AMOD E2). Z.div_mod_to_equations. nia.
    - intros x y Hx Hy E. destruct (ro_fa_elems _ _ RO x Hx) as (_ & _ & _ & Ex). destruct (ro_fa_elems _ _ RO y Hy) as (_ & _ & _ & Ey).
      rewrite shiftl4 in Ex, Ey. fold csz in Ex, Ey. Z.div_mod_to_equations. nia. }
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RefillModel.
  Variables (st : astate) (c : Z).
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c. Let csz := class_size c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.

  Definition refill_region : region := mkRegion mu' au' (nf1 - n) (skipn (Z.to_nat n) fl1) mfa'.
  Definition refill_pc : pclass := mkPC n (firstn (Z.to_nat n) fl1).
  Definition refill_newmaps : list mapping :=
       (if mfa <? mfa' then [mkMap (free_array_base st c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false] else [])
    ++ (if mu <? mu' then [mkMap (region_beg st c + mu) (mu' - mu) (MkUserMap c) PROT_RW false] else []).
  Definition refilled : astate :=
    mkState (as_space_beg st) (as_ptr_array st) (upd_nth (as_regions st) (zidx c) refill_region) true
            (upd_nth (as_cache st) (zidx c) refill_pc) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
            (as_internal_init st) (refill_newmaps ++ as_maps st) (as_shadow st) (as_env st) (as_track_shadow st)
            (as_qmax st) (as_qmin st) (as_qcache st).

  Hypothesis W : WF st.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.
  (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.

  Let RO : region_ok st c. Proof. apply WF_region; [exact W| unfold kNumClasses; lia]. Qed.
  Let CO : cache_ok st c. Proof. apply WF_cache; [exact W| unfold kNumClasses; lia]. Qed.
  Let T : 32 <= csz <= 65536 /\ csz mod 32 = 0 /\ 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
  Proof. pose proof (class_size_table_facts c ltac:(lia)) as (T1 & T2 & T3 & T4 & T5 & T6). subst csz. repeat split; try lia. Qed.
  Let NR : 1 <= n <= 8 /\ n + n = max_count c.
  Proof. subst n. unfold rf_n. lia. Qed.
  Let PCS : pc_chunks (get_pc st c) = [].
  Proof. pose proof (co_count _ _ CO) as E. rewrite EMPTY in E. destruct (pc_chunks (get_pc st c)); [reflexivity| rewrite zlen_cons in E; unfold zlen in E; lia]. Qed.
  Let FLL : zlen fl = nf. Proof. symmetry. exact (ro_numfreed _ _ RO). Qed.
  Let NFAU : csz * nf <= au. Proof. apply free_array_count; [exact W| unfold kNumClasses; lia| destruct T; lia]. Qed.
  Let AUR : 0 <= au <= mu /\ mu mod kUserMapSize = 0 /\ mu + 2 * kUserMapSize <= kFreeArrayOffset /\ au mod csz = 0
            /\ mu - au < csz + (if au =? 0 then kUserMapSize else 0).
  Proof.
    pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_mod _ _ RO). pose proof (ro_alloc_mod _ _ RO ltac:(destruct T; lia)).
    pose proof (ro_tail_small _ _ RO ltac:(destruct T; lia)) as TS. fold r au mu csz in TS |- *.
    repeat split; try assumption; try lia.
  Qed.
  Let NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize /\ mfa mod kFreeArrayMapSize = 0.
  Proof.
    pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_mod _ _ RO). pose proof (ro_fa_bound _ _ RO). fold r nf mfa in H, H0, H1 |- *.
    assert (0 <= nf) by (rewrite <- FLL; unfold zlen; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_facts :
       n <= nf1 /\ zlen fl1 = nf1 /\ 0 <= nnew /\ nf1 = nf + nnew /\ au' = au + nnew * csz
    /\ au <= au' <= mu' /\ mu <= mu' <= mu + kUserMapSize /\ mu' mod kUserMapSize = 0 /\ au' mod csz = 0
    /\ mu' - au' < csz + (if au' =? 0 then kUserMapSize else 0)
    /\ 4 * nf1 <= mfa' /\ mfa <= mfa' <= kFreeArraySize /\ mfa' mod kFreeArrayMapSize = 0
    /\ (nf < n -> rf_total c nf au <= mu' /\ nnew = (mu' - au) / csz)
    /\ (n <= nf -> mu' = mu /\ nnew = 0 /\ mfa' = mfa).
  Proof.
    destruct T as (T1 & T2 & T3 & T4). destruct NR as [N1 N2]. destruct AUR as (A1 & A2 & A3 & A4 & A5). destruct NFR as (F1 & F2 & F3 & F4).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    assert (ENF1 : nf1 = nf + nnew) by (subst nf1; unfold rf_nf1; reflexivity).
    assert (EAU : au' = au + nnew * csz) by (subst au'; unfold rf_au'; reflexivity).
    assert (LFL1 : zlen fl1 = Z.of_nat (Z.to_nat nnew) + nf).
    { subst fl1. unfold rf_fl1. rewrite zlen_app. unfold zlen at 1. rewrite carve_asc_length'. fold nnew. clear - FLL. lia. }
    destruct (Z.lt_ge_cases nf n) as [NF|NF].
    - (* [comment removed for export] *)
      pose proof (rf_batch_small c HC) as [BSM _]. fold n csz in BSM.
      assert (TOT : au + csz <= rf_total c nf au <= au + 65536) by (unfold rf_total, rf_k; fold n csz; clear - BSM NF N1 T1 F1; nia).
      assert (EMU : mu' = (if mu <? rf_total c nf au then mu + 262144 else mu) /\ rf_total c nf au <= mu').
      { subst mu'. unfold rf_mu'. fold n. rewrite (proj2 (Z.ltb_lt _ _) NF).
        destruct (Z.ltb_spec mu (rf_total c nf au)) as [LT|GE]; [| split; [reflexivity| exact GE]].
        assert (MS : pop_ms (rf_total c nf au) mu = 262144) by (unfold pop_ms, round_up, kUserMapSize; clear - TOT LT A1 T1; Z.div_mod_to_equations; lia).
        rewrite MS. split; [reflexivity| clear - TOT LT A1 T1; lia]. }
      destruct EMU as [EMU TOTLE].
      assert (MUR : mu <= mu' <= mu + 262144 /\ mu' mod 262144 = 0) by (rewrite EMU; destruct (mu <? _); clear - A2; Z.div_mod_to_equations; lia).
      assert (ENN : nnew = (mu' - au) / csz) by (subst nnew; unfold rf_nnew; fold n; rewrite (proj2 (Z.ltb_lt _ _) NF); reflexivity).
      assert (NNR : n - nf <= nnew /\ 1 <= nnew /\ csz * nnew <= mu' - au /\ mu' - au < csz * nnew + csz /\ 4 * nnew <= 65540).
      { rewrite ENN. unfold rf_total, rf_k in TOTLE. fold n csz in TOTLE. assert (A5' : mu - au < csz + 262144) by (destruct (au =? 0); clear - A5; lia). clear - TOTLE MUR A5' A1 T1 NF N1.
        assert (n - nf <= (mu' - au) / csz) by (apply Z.div_le_lower_bound; [lia| nia]).
        assert ((mu' - au) / csz <= 16385) by (apply Z.div_le_upper_bound; [lia|]; nia).
        split; [lia| split; [lia| split; [Z.div_mod_to_equations; nia| split; [Z.div_mod_to_equations; nia| lia]]]]. }
      assert (FAR : 4 * (nf + nnew) <= 469762048).
      { assert (X : nf + nnew <= mu' / csz).
        { rewrite ENN. replace mu' with (au + (mu' - au)) at 2 by (clear; lia). clear - NFAU T1 A1 MUR.
          rewrite <- (Z.div_add_l nf csz (mu' - au)) by lia. apply Z.div_le_mono; [lia| nia]. }
        assert (Y : mu' / csz <= 3758096384 / 32) by (eapply Z.le_trans; [apply Z.div_le_mono; [clear - T1; lia|]| apply Z.div_le_compat_l]; clear - A1 A3 MUR T1; lia).
        change (3758096384 / 32) with 117440512 in Y. clear - X Y. lia. }
      assert (EMFA : mfa' = (if 4 * (nf + nnew) <=? mfa then mfa else efs_new (nf + nnew))).
      { subst mfa'. unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt _ _) NF). fold nf1. rewrite ENF1. reflexivity. }
      assert (MFR : 4 * (nf + nnew) <= mfa' /\ mfa <= mfa' <= 536870912 /\ mfa' mod 262144 = 0).
      { rewrite EMFA. destruct (Z.leb_spec (4 * (nf + nnew)) mfa) as [LE|GT]; [clear - LE F2 F3 F4 NNR F1; lia|].
        unfold efs_new, round_up, kFreeArrayMapSize. clear - GT FAR F1 F3 F4 NNR. Z.div_mod_to_equations. lia. }
      rewrite Z2Nat.id in LFL1 by (clear - NNR; lia).
      rewrite ENF1, EAU. split; [clear - NNR; lia|]. split; [clear - LFL1; lia|]. split; [clear - NNR; lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [clear - NNR T1 A1; nia|]. split; [exact (proj1 MUR)|]. split; [exact (proj2 MUR)|].
      split; [rewrite Z.mod_add by (clear - T1; lia); exact A4|].
      split; [destruct (au + nnew * csz =? 0); clear - NNR T1; nia|].
      split; [clear - MFR; lia|]. split; [clear - MFR; lia|]. split; [clear - MFR; lia|].
      split; [intros _; split; [exact TOTLE| exact ENN]| intros GE; exfalso; clear - GE NF; lia].
    - (* [comment removed for export] *)
      assert (E1 : mu' = mu) by (subst mu'; unfold rf_mu'; fold n; rewrite (proj2 (Z.ltb_ge _ _) NF); reflexivity).
      assert (E2 : nnew = 0) by (subst nnew; unfold rf_nnew; fold n; rewrite (proj2 (Z.ltb_ge _ _) NF); reflexivity).
      assert (E3 : mfa' = mfa) by (subst mfa'; unfold rf_mfa'; fold n; rewrite (proj2 (Z.ltb_ge _ _) NF); reflexivity).
      rewrite E2 in ENF1, EAU, LFL1. cbn [Z.to_nat Z.of_nat] in LFL1.
      rewrite E1, E3, ENF1, EAU, E2. clear - NF A1 A2 A5 A4 F1 F2 F3 F4 LFL1 ENF1.
      rewrite Z.mul_0_l, !Z.add_0_r in *.
      repeat match goal with |- _ /\ _ => split end; try lia; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_mfa_delta : mfa' <= mfa + kFreeArrayMapSize.
  Proof.
    pose proof rf_facts as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    destruct T as (T1 & _). destruct AUR as (A1 & _ & _ & _ & A5). destruct NFR as (F1 & F2 & F3 & F4).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    destruct (Z.lt_ge_cases nf n) as [NF|NF].
    - destruct (Q14 NF) as [_ ENN].
      assert (NN : 4 * nnew <= 131076).
      { assert (A5' : mu - au < csz + 262144) by (destruct (au =? 0); clear - A5; lia).
        assert (X : (mu' - au) / csz <= 32769) by (apply Z.div_le_upper_bound; [clear - T1; lia| clear - A5' Q7 T1 A1; nia]).
        rewrite <- ENN in X. clear - X. lia. }
      subst mfa'. unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt _ _) NF). fold nf1.
      destruct (4 * nf1 <=? mfa); [clear; lia|]. unfold efs_new, round_up, kFreeArrayMapSize. rewrite Q4. clear - NN F2 F4 F1 Q3.
      Z.div_mod_to_equations. lia.
    - destruct (Q15 NF) as (_ & _ & E). rewrite E. clear. lia.
  Qed.

  (* [comment removed for export] *)
  Let LENR : length (as_regions st) = 32%nat.
  Proof. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
  Let LENC : length (as_cache st) = 32%nat.
  Proof. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
  Lemma rfd_region_c : get_region refilled c = refill_region.
  Proof. unfold refilled, get_region. cbn [as_regions]. apply znth_upd_nth_eq. rewrite LENR. unfold zidx. lia. Qed.
  Lemma rfd_region_o : forall c', 0 <= c' -> c' <> c -> get_region refilled c' = get_region st c'.
  Proof using W HC ROOM. intros c' H1 H2. unfold refilled, get_region. cbn [as_regions]. apply znth_upd_nth_neq. unfold zidx. clear - H1 H2 HC. lia. Qed.   (* [comment removed for export] *)
  Lemma rfd_pc_c : get_pc refilled c = refill_pc.
  Proof. unfold refilled, get_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold zidx. lia. Qed.
  Lemma rfd_pc_o : forall c', 0 <= c' -> c' <> c -> get_pc refilled c' = get_pc st c'.
  Proof using W HC ROOM. intros c' H1 H2. unfold refilled, get_pc. cbn [as_cache]. apply znth_upd_nth_neq. unfold zidx. clear - H1 H2 HC. lia. Qed.   (* [comment removed for export] *)
  Lemma rfd_same : as_space_beg refilled = as_space_beg st /\ as_ptr_array refilled = as_ptr_array st /\ as_n_reserved refilled = as_n_reserved st
    /\ as_sec refilled = as_sec st /\ as_chunks refilled = as_chunks st /\ as_tq refilled = as_tq st /\ as_gq refilled = as_gq st
    /\ as_internal_init refilled = as_internal_init st /\ as_cache_inited refilled = true
    /\ as_qmax refilled = as_qmax st /\ as_qmin refilled = as_qmin st /\ as_qcache refilled = as_qcache st
    /\ chunk_list refilled = chunk_list st /\ (forall c', region_beg refilled c' = region_beg st c')
    /\ (forall c' cp, compact_to_addr refilled c' cp = compact_to_addr st c' cp) /\ (forall a, in_primary refilled a = in_primary st a)
    /\ (forall a, class_of_addr refilled a = class_of_addr st a) /\ (forall c', free_array_base refilled c' = free_array_base st c').
  Proof. repeat split; reflexivity. Qed.

  Theorem WF_refill : WF refilled.
  Proof.
    pose proof rf_facts as RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    pose proof W as WW.
    destruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
    destruct T as (T1 & T2 & T3 & T4). destruct NR as [N1 N2]. destruct AUR as (A1 & A2 & A3 & A4 & A5). destruct NFR as (F1 & F2 & F3 & F4).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kNumClasses in *.
    assert (A16 : au mod 16 = 0) by (clear - A4 T1 T2; Z.div_mod_to_equations; nia).
    (* [comment removed for export] *)
    assert (CARVE : forall cp, In cp (carve_asc au csz 0 (Z.to_nat nnew)) ->
              exists j, 0 <= j < nnew /\ cp * 16 = au + j * csz /\ 0 <= cp).
    { intros cp Hin. apply in_carve_asc in Hin. destruct Hin as (j & Hj & E). rewrite Z2Nat.id in Hj by (clear - Q3; lia).
      exists j. rewrite Z.add_0_l in E.
      assert (M16 : (au + j * csz) mod 16 = 0) by (clear - A16 T2 Hj; Z.div_mod_to_equations; nia).
      assert (E' : cp = (au + j * csz) / 16) by (rewrite E; unfold kCompactPtrScale; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
      clear - Hj M16 E' A1 T1. split; [lia|]. Z.div_mod_to_equations. nia. }
    (* [comment removed for export] *)
    assert (FL1E : forall cp, In cp fl1 -> 0 <= cp /\ Z.shiftl cp kCompactPtrScale < au' /\ class_size c <> 0 /\ Z.shiftl cp kCompactPtrScale mod class_size c = 0).
    { intros cp Hin. rewrite shiftl4. fold csz. subst fl1. unfold rf_fl1 in Hin. fold nnew in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - destruct (CARVE cp Hin) as (j & Hj & E & POS). rewrite E, Q5. clear - Hj POS T1 A4 A1. split; [lia|]. split; [nia|]. split; [lia|].
        rewrite Z.mod_add by lia. exact A4.
      - destruct (ro_fa_elems _ _ RO cp Hin) as (E1 & E2 & E3 & E4). rewrite shiftl4 in E2, E4. fold r au csz in E2, E3, E4 |- *.
        clear - E1 E2 E3 E4 Q6. repeat split; try assumption. lia. }
    (* [comment removed for export] *)
    assert (OLDC : forall a, In a (carved_addr_list st) -> exists c0, carved st c0 a).
    { intros a Hin. unfold carved_addr_list in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| apply in_app_iff in Hin; destruct Hin as [Hin|Hin]].
      - apply in_flat_map in Hin. destruct Hin as (c0 & Hc0 & Hin). apply in_map_iff in Hc0. destruct Hc0 as (k & <- & Hk). apply in_seq in Hk.
        apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; apply in_map_iff in Hin; destruct Hin as (cp & <- & Hin); exists (Z.of_nat k).
        + apply carved_free; [exact W| unfold kNumClasses; clear - Hk; lia| exact Hin].
        + apply carved_cache; [exact W| unfold kNumClasses; clear - Hk; lia| exact Hin].
      - apply in_map_iff in Hin. destruct Hin as (x & <- & Hx). apply filter_In in Hx. destruct Hx as [Hx PX].
        pose proof (Wch x Hx) as CO0. unfold chunk_ok in CO0. destruct CO0 as (U1 & U2 & U3 & U4 & REST). rewrite PX in REST.
        destruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
        exists (ch_class x).
        assert (HC' : 0 <= ch_class x < 32).
        { rewrite P3. unfold class_of_addr. pose proof (Z.land_ones (Z.shiftr (ch_alloc_beg x - as_space_beg st) kRegionSizeLog) 5 ltac:(clear; lia)) as LO.
          change (Z.ones 5) with 31 in LO. rewrite LO. pose proof (Z.mod_pos_bound (Z.shiftr (ch_alloc_beg x - as_space_beg st) kRegionSizeLog) (2^5)). clear - H. lia. }
        unfold carved, kNumClasses. pose proof (class_size_table_facts (ch_class x) HC') as (V1 & V2 & V3 & _).
        pose proof (compute_req_facts (ch_used x) ltac:(clear - U1; lia)) as (_ & X2 & X3 & _ & X5 & _). rewrite P1 in X5.
        clear - HC' P5 P6 P7 P8 V1 X2 X3 X5. repeat split; try assumption; lia.
      - apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). exists kBatchClass.
        pose proof (WF_batch st b W Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _).
        unfold carved. change (class_size kBatchClass) with 8192 in *. unfold kBatchClass, kNumClasses in *. clear - B5 B6 B7. repeat split; try assumption; lia. }
    (* [comment removed for export] *)
    assert (FRESH : forall a cp, In a (carved_addr_list st) -> In cp (carve_asc au csz 0 (Z.to_nat nnew)) -> a <> compact_to_addr st c cp).
    { intros a cp Ha Hcp E. destruct (OLDC a Ha) as [c0 CV]. destruct (CARVE cp Hcp) as (j & Hj & Ecp & POS).
      rewrite compact_to_addr_eq, Ecp in E. destruct CV as (C1 & C2 & C3 & C4 & C5).
      destruct (Z.eq_dec c0 c) as [->|NE].
      - fold r au in C5. clear - E C3 C5 Hj T1 C2. subst a. nia.
      - pose proof (regions_disjoint st c0 c ltac:(clear - C1; lia) ltac:(clear - HC; lia) NE) as D.
        pose proof (class_size_table_facts c0 ltac:(clear - C1; unfold kNumClasses in C1; lia)) as (V1 & _).
        pose proof (ro_mapped_bound _ _ (WF_region st c0 W C1)) as MB. pose proof (ro_alloc_le _ _ (WF_region st c0 W C1)) as AL.
        unfold kUserMapSize, kFreeArrayOffset in MB.
        clear - E C3 C5 Hj T1 D V1 MB AL A1 A3 Q6 Q7 Q5. subst a. nia. }
    assert (LEN1 : length fl1 = Z.to_nat nf1) by (clear - Q2; unfold zlen in Q2; lia).
    assert (NK : (Z.to_nat n <= length fl1)%nat) by (rewrite LEN1; clear - Q1 N1; lia).
    assert (INfl1 : forall cp, In cp (skipn (Z.to_nat n) fl1) \/ In cp (firstn (Z.to_nat n) fl1) -> In cp fl1).
    { intros cp H. rewrite <- (firstn_skipn (Z.to_nat n) fl1). apply in_app_iff. clear - H. tauto. }
    unfold WF.
    split.
    { intros c0 Hc0. destruct (Wrc c0 Hc0) as [R0 C0]. unfold kNumClasses in Hc0. destruct (Z.eq_dec c0 c) as [->|NE].
      - split.
        + constructor; rewrite rfd_region_c; cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array refill_region]; fold csz.
          * clear - Q6 A1; lia.
          * clear - Q6; lia.
          * exact Q8.
          * unfold kUserMapSize, kFreeArrayOffset. clear - ROOM Q7. lia.
          * intros _. exact Q9.
          * intros _. exact Q10.
          * intros Z0. exfalso. clear - Z0 T1. subst csz. lia.
          * rewrite zlen_skipn, LEN1. clear - Q1 N1 Q2 LEN1 F1 Q4 Q3. rewrite Nat.min_l by lia. lia.
          * clear - Q11 Q1 N1. lia.
          * exact Q13.
          * unfold kFreeArraySize. clear - Q12; lia.
          * intros cp Hin. apply FL1E. apply INfl1. left. exact Hin.
        + constructor; rewrite rfd_pc_c; cbn [pc_count pc_chunks refill_pc].
          * rewrite zlen_firstn by exact NK. clear - N1; lia.
          * change (as_cache_inited refilled) with true. cbv iota. clear - N1 N2; lia.
          * intros cp Hin. rewrite rfd_region_c. cbn [rg_allocated_user refill_region]. apply FL1E. apply INfl1. right. exact Hin.
      - split.
        + destruct R0; constructor; rewrite (rfd_region_o c0) by (clear - Hc0 NE; lia); try assumption.
        + destruct C0 as [X1 X2 X3]; constructor; rewrite (rfd_pc_o c0) by (clear - Hc0 NE; lia).
          * exact X1.
          * change (as_cache_inited refilled) with true. cbv iota. pose proof (class_size_table_facts c0 ltac:(clear - Hc0; lia)) as (_ & _ & _ & M & _).
            destruct (as_cache_inited st); clear - X2 M; lia.
          * rewrite (rfd_region_o c0) by (clear - Hc0 NE; lia). exact X3. }
    split. 2:{
    pose proof rfd_same as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
    rewrite !S13, !S4, !S3, !S6, !S7, !S10, !S11, !S12, !S5.
    assert (AUmono : forall c1, 0 <= c1 < 32 -> rg_allocated_user (get_region st c1) <= rg_allocated_user (get_region refilled c1)).
    { intros c1 Hc1. destruct (Z.eq_dec c1 c) as [->|NE]; [rewrite rfd_region_c; cbn [rg_allocated_user refill_region]; fold r au; clear - Q6; lia| rewrite (rfd_region_o c1) by (clear - Hc1 NE; lia); clear; lia]. }
    split. { intros x Hx. pose proof (Wch x Hx) as CO0. unfold chunk_ok in CO0 |- *. rewrite !S16, !S17, !S14.
      destruct CO0 as (U1 & U2 & U3 & U4 & REST). refine (conj U1 (conj U2 (conj U3 (conj U4 _)))).
      destruct (ch_primary x); [| exact REST].
      destruct REST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj _ P8))))))).
      assert (HC' : 0 <= ch_class x < 32).
      { rewrite P3. unfold class_of_addr. pose proof (Z.land_ones (Z.shiftr (ch_alloc_beg x - as_space_beg st) kRegionSizeLog) 5 ltac:(clear; lia)) as LO.
        change (Z.ones 5) with 31 in LO. rewrite LO. pose proof (Z.mod_pos_bound (Z.shiftr (ch_alloc_beg x - as_space_beg st) kRegionSizeLog) (2^5)). clear - H. lia. }
      pose proof (AUmono (ch_class x) HC'). clear - P7 H. lia. }
    split. { exact Winj. } split. { exact Wsec. } split. { exact Wsnd. } split. { exact Wres1. } split. { exact Wres2. }
    assert (QOK : forall q, qcache_ok st q -> qcache_ok refilled q).
    { intros q [X1 X2]. split; [| exact X2]. intros b Hb. pose proof (X1 b Hb) as BO. unfold batch_ok in BO |- *.
      rewrite !S16, !S17, !S14, !S5. destruct BO as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
      refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj _ (conj B8 B9)))))))).
      pose proof (AUmono kBatchClass ltac:(unfold kBatchClass; clear; lia)). clear - B7 H. lia. }
    split. { apply QOK. exact Wtq. } split. { apply QOK. exact Wgq. }
    split. { exact Wtqb. } split. { exact Wgqb. } split. { exact Wndb. } split. { exact Wq. }
    split. { rewrite (rfd_region_o 0) by (clear - HC; lia). exact Wm0. }
    split. { rewrite (rfd_region_o 31) by (clear - HC; lia). exact Wm31. }
    split. { rewrite (rfd_pc_o 0) by (clear - HC; lia). exact Wpc0. }
    split. { rewrite (rfd_pc_o 31) by (clear - HC; lia). exact Wpc31. }
    split. { unfold refilled. cbn [as_regions]. rewrite length_upd_nth. exact WlenR. }
    split. { unfold refilled. cbn [as_cache]. rewrite length_upd_nth. exact WlenC. }
    split. { exact Wqmax. } split. { exact Wqmin. } split. { exact Wqc. } exact Wkeys. }
    (* [comment removed for export] *)
    pose proof rfd_same as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18).
    assert (S15f : forall c', compact_to_addr refilled c' = compact_to_addr st c') by reflexivity.
    set (extra := map (compact_to_addr st c) (carve_asc au csz 0 (Z.to_nat nnew))).
    apply (Permutation_NoDup (l := extra ++ carved_addr_list st)).
    - apply Permutation_sym. unfold carved_addr_list. rewrite !S13, !S6, !S7.
      set (L := map Z.of_nat (seq 0 32)).
      set (g := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st c0))).
      set (g' := fun c0 : Z => map (compact_to_addr refilled c0) (rg_free_array (get_region refilled c0)) ++ map (compact_to_addr refilled c0) (pc_chunks (get_pc refilled c0))).
      set (REST := map ch_alloc_beg (filter ch_primary (chunk_list st)) ++ map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st))).
      replace (extra ++ flat_map g L ++ REST) with ((extra ++ flat_map g L) ++ REST) by (first [apply app_assoc | symmetry; apply app_assoc]).
      apply Permutation_app_tail.
      apply (flat_map_perm_add g g' L c extra).
      + apply classes_nodup.
      + apply classes_in. clear - HC; lia.
      + intros x Hx Hne. unfold g, g'. assert (0 <= x) by (unfold L in Hx; apply in_map_iff in Hx as [y [<- _]]; clear; lia).
        rewrite (rfd_region_o x), (rfd_pc_o x), !S15f by (clear - H Hne; lia). reflexivity.
      + unfold g, g'. rewrite rfd_region_c, rfd_pc_c, PCS, !S15f. cbn [rg_free_array refill_region pc_chunks refill_pc map]. rewrite app_nil_r.
        rewrite <- map_app. eapply Permutation_trans; [apply Permutation_map; apply Permutation_app_comm|]. rewrite firstn_skipn.
        subst extra. unfold fl1, rf_fl1. fold nnew. rewrite map_app. apply Permutation_refl.
    - apply NoDup_app_intro; [| exact Wnd|].
      + (* [comment removed for export] *)
        subst extra. clear - CARVE T1.
        assert (INJ : forall x y, In x (carve_asc au csz 0 (Z.to_nat nnew)) -> In y (carve_asc au csz 0 (Z.to_nat nnew)) ->
                        compact_to_addr st c x = compact_to_addr st c y -> x = y).
        { intros x y Hx Hy E. rewrite !compact_to_addr_eq in E. lia. }
        assert (ND : NoDup (carve_asc au csz 0 (Z.to_nat nnew))).
        { assert (GEN : forall k i, NoDup (carve_asc au csz i k)); [| apply GEN]. clear - T1.
          induction k as [|k IH]; intros i; cbn; constructor; [| apply IH].
          intros Hin. apply in_carve_asc in Hin. destruct Hin as (j & Hj & E).
          unfold kCompactPtrScale in E. rewrite !Z.shiftr_div_pow2 in E by lia. change (2^4) with 16 in E.
          assert (X : csz <= (i + 1 + j) * csz - i * csz) by nia. Z.div_mod_to_equations. lia. }
        remember (carve_asc au csz 0 (Z.to_nat nnew)) as l eqn:El. clear El CARVE T1.
        induction l as [|x l IH]; cbn; constructor.
        * intros Hin. apply in_map_iff in Hin. destruct Hin as (y & E & Hy). inversion ND; subst.
          assert (y = x) by (apply INJ; [right; exact Hy| left; reflexivity| exact E]). subst y. contradiction.
        * inversion ND; subst. apply IH; [| assumption]. intros a b Ha Hb. apply INJ; right; assumption.
      + intros a Ha Hin. subst extra. apply in_map_iff in Ha. destruct Ha as (cp & <- & Hcp). exact (FRESH _ cp Hin Hcp eq_refl).
  Qed.
End RefillModel.

End HCW.

