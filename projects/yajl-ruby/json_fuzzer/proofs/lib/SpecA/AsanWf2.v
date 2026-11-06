(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section WF.
Variable E : aenv.
Variable P : list Z.        (* [comment removed for export] *)
Variable D : list batch.    (* [comment removed for export] *)
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gmapped (s0 s1 : astate) (c : Z) : Prop :=
  grows s0 s1 c [] /\ rg_alloc_user (get_region s1 c) = rg_alloc_user (get_region s0 c)
  /\ rg_free (get_region s1 c) = rg_free (get_region s0 c)
  /\ rg_mapped_user (get_region s0 c) <= rg_mapped_user (get_region s1 c)
  /\ rg_mapped_fa (get_region s0 c) <= rg_mapped_fa (get_region s1 c).

Lemma gmapped_refl : forall s c, gmapped s s c.
Proof. intros. split; [apply grows_refl|]. repeat split; lia. Qed.

Lemma grows_trans_nil : forall a b d c fr, grows a b c [] -> grows b d c fr -> grows a d c fr.
Proof.
  intros a b d c fr (A1&A2&A3&A4&A5&A6&A7&A8&A9&A9n&A10&A11&A12&A13) (B1&B2&B3&B4&B5&B6&B7&B8&B9&B9n&B10&B11&B12&B13).
  unfold grows. repeat split; try congruence; try lia.
  - intros c' H. rewrite (B10 c' H), (A10 c' H). reflexivity.
  - rewrite B12, A12, app_nil_r. reflexivity.
  - intros x Hx. specialize (B13 x Hx). lia.
Qed.

Lemma gmapped_trans : forall a b d c, gmapped a b c -> gmapped b d c -> gmapped a d c.
Proof.
  intros a b d c (G1 & E1 & F1 & M1 & N1) (G2 & E2 & F2 & M2 & N2). split; [eapply grows_trans_nil; eauto|].
  repeat split; try congruence; lia.
Qed.

(* [comment removed for export] *)
Definition room (s : astate) (c : Z) : Prop :=
  rg_mapped_user (get_region s c) + kUserMapSize <= kFreeArrayOffset.

Lemma populate_free_array_spec : forall s0 c requested,
  1 <= c <= kLargestClassID -> 0 <= requested <= hint c ->
  AWF s0 -> as_cache_inited s0 = true -> room s0 c ->
  hoare (fun s => s = s0) (populate_free_array E c requested)
        (fun s' ok => AWF s' /\ as_cache_inited s' = true
                      /\ (exists fresh, grows s0 s' c fresh)
                      /\ (ok = true -> rg_num_freed (get_region s0 c) + requested <= rg_num_freed (get_region s' c))).
Proof.
  intros s0 c requested Hc Hreq WF HI ROOM.
  pose proof (class_size_mod c Hc) as [SZM SZB].
  unfold populate_free_array. apply hoare_get_bind. intros s ->.
  set (r0 := get_region s0 c). set (size := class_size c).
  set (total := rg_alloc_user r0 + requested * size).
  (* [comment removed for export] *)
  eapply hoare_bind with (Q := fun s1 ok1 => AWF s1 /\ as_cache_inited s1 = true /\ gmapped s0 s1 c
                                           /\ rg_mapped_user (get_region s1 c) <= kFreeArrayOffset
                                           /\ (ok1 = true -> total <= rg_mapped_user (get_region s1 c))).
  { match goal with |- hoare _ (if ?b then _ else _) _ => destruct b eqn:HB end.
    - apply Z.ltb_lt in HB.
      unfold acheck. match goal with |- hoare _ (abind (if ?b then _ else _) _) _ => destruct b eqn:HB2 end.
      2:{ exfalso. apply Z.leb_gt in HB2.
          destruct WF as (_ & (_ & R2) & _). specialize (R2 c Hc). unfold region_of in R2. fold r0 in R2.
          destruct R2 as (A1 & _).
          pose proof (hint_size_bound c Hc) as [HS HP].
          assert (RS : requested * size <= hint c * class_size c) by (subst size; apply Z.mul_le_mono_nonneg_r; lia).
        assert (TM : 0 < total - rg_mapped_user r0 <= kUserMapSize) by (subst total size; unfold kUserMapSize; clear -RS HS HB A1; lia).
          rewrite (round_up_small (total - rg_mapped_user r0) kUserMapSize ltac:(reflexivity) TM) in HB2. unfold room in ROOM. subst r0. lia. }
      apply Z.leb_le in HB2.
      eapply hoare_bind with (Q := fun s1 _ => s1 = s0); [apply hoare_ret; intros s1 ->; reflexivity|]. intros [].
      eapply hoare_bind with (Q := fun s1 _ => s1 = s0); [apply call_mmap_fixed_frame|].
      intros ok. apply hoare_pre. intros s1 ->. destruct ok.
      + apply hoare_upd_bind. apply hoare_ret. intros s' (s1 & -> & ->).
        destruct WF as (WE & (R1 & R2) & WREST) eqn:EWF. clear EWF.
        pose proof (R2 c Hc) as RC. unfold region_of in RC. fold r0 in RC. destruct RC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
        pose proof (hint_size_bound c Hc) as [HS HP].
        assert (RS : requested * size <= hint c * class_size c) by (subst size; apply Z.mul_le_mono_nonneg_r; lia).
        assert (TM : 0 < total - rg_mapped_user r0 <= kUserMapSize) by (subst total size; unfold kUserMapSize; clear -RS HS HB A1; lia).
        rewrite (round_up_small (total - rg_mapped_user r0) kUserMapSize ltac:(reflexivity) TM) in *.
        set (s' := upd_cache_mapped _ (upd_ts _ (set_region c _ s0))).
        assert (GC : get_region s' c = mkRegion (rg_mapped_user r0 + kUserMapSize) (rg_alloc_user r0) (rg_free r0) (rg_mapped_fa r0) (rg_n_allocated r0) (rg_n_freed r0)).
        { subst s'. rewrite get_region_upd_cache_mapped, get_region_upd_ts, get_set_region_eq. reflexivity. }
        assert (GO : forall c', c' <> c -> get_region s' c' = get_region s0 c').
        { intros c' NE. subst s'. rewrite get_region_upd_cache_mapped, get_region_upd_ts, get_set_region_ne by auto. reflexivity. }
        assert (GR : grows s0 s' c []).
        { unfold grows. subst s'. repeat split; try reflexivity.
          - exact GO.
          - rewrite GC; cbn; subst r0; lia. - rewrite GC; cbn; subst r0; rewrite app_nil_r; reflexivity. - intros x []. }
        assert (WF' : AWF s').
        { eapply AWf_frame_grows; [exact Hc| exact HI| exact GR| | ].
          2:{ split; [exact WE|]. split; [split; [exact R1| exact R2]|]. exact WREST. }
          split.
          - subst s'. rewrite as_regions_set3. intros c0 r1 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|].
            rewrite lookup_insert_ne in Hl by auto. eapply R1; exact Hl.
          - intros c0 Hc0. cbn zeta. unfold region_of. destruct (Z.eq_dec c c0) as [<-|NE].
            + rewrite GC. cbn. unfold rg_num_freed in *. cbn.
              assert (P2 : (rg_mapped_user r0 + kUserMapSize) mod kUserMapSize = 0) by (apply mod_add_multiple; [reflexivity| exact A2| reflexivity]).
              assert (P1 : 0 <= rg_alloc_user r0 <= rg_mapped_user r0 + kUserMapSize) by (unfold kUserMapSize; lia).
              match goal with |- _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ ?G /\ _ /\ _ => assert (P10 : G) end.
              { intros x Hx. destruct (A10 x Hx) as [Cx Mx]. split; [|exact Mx]. eapply carved_mono; [|exact Cx]. rewrite GC; cbn; subst r0; lia. }
              exact (conj P1 (conj P2 (conj HB2 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj P10 (conj A11 A12))))))))))).
            + rewrite GO by auto. specialize (R2 c0 Hc0). unfold region_of in R2.
              destruct R2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
              refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj B8 (conj B9 (conj _ (conj B11 B12))))))))))).
              intros x Hx. destruct (B10 x Hx) as [Cx Mx]. split; [|exact Mx]. eapply carved_mono; [|exact Cx]. rewrite GO by auto; lia. }
        split; [exact WF'|]. split; [subst s'; cbn; exact HI|]. split.
        { split; [exact GR|]. rewrite GC; cbn; subst r0. repeat split; unfold kUserMapSize; lia. }
        split; [rewrite GC; cbn; exact HB2|]. intros _. rewrite GC; cbn. subst r0. lia.
      + apply hoare_ret. intros s1 ->. split; [exact WF|]. split; [exact HI|]. split; [apply gmapped_refl|].
        split; [unfold room in ROOM; unfold kUserMapSize in ROOM; lia|]. discriminate.
    - apply Z.ltb_ge in HB. apply hoare_ret. intros s1 ->. split; [exact WF|]. split; [exact HI|]. split; [apply gmapped_refl|].
      split; [unfold room in ROOM; unfold kUserMapSize in ROOM; lia|]. intros _. exact HB. }
  intros ok1. apply hoare_pre. intros s1 (WF1 & HI1 & GM1 & MB1 & TOT1).
  destruct ok1; cbn [negb].
  2:{ apply hoare_ret. intros s2 ->. split; [exact WF1|]. split; [exact HI1|]. split; [exists []; exact (proj1 GM1)| discriminate]. }
  specialize (TOT1 eq_refl).
  apply hoare_get_bind. intros s2 ->.
  destruct GM1 as (GR1 & AL1 & FR1 & MU1 & FA1).
  pose proof WF1 as WF1c. destruct WF1c as (WE1 & (R11 & R12) & WREST1).
  pose proof (R12 c Hc) as RC1. unfold region_of in RC1.
  destruct RC1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  set (r1 := get_region s1 c) in *.
  set (new_chunks := (rg_mapped_user r1 - rg_alloc_user r1) / size).
  set (total_freed := rg_num_freed r1 + new_chunks).
  assert (NC0 : 0 <= new_chunks) by (subst new_chunks size; apply Z.div_pos; lia).
  assert (NCB : new_chunks * size <= rg_mapped_user r1 - rg_alloc_user r1) by (subst new_chunks; apply div_mul_le; lia).
  (* [comment removed for export] *)
  assert (S16 : size = 16 * (size / 16)).
  { subst size. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)).
    assert (class_size c mod 16 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in SZM; [|lia]. destruct SZM as [q Hq]. exists (2*q); lia. }
    lia. }
  (* [comment removed for export] *)
  assert (NF1 : rg_num_freed r1 * size <= rg_alloc_user r1).
  { unfold rg_num_freed.
    assert (K0 : 0 <= rg_alloc_user r1 / size) by (apply Z.div_pos; lia).
    assert (HX : forall x, In x (rg_free r1) -> exists k, 0 <= k < rg_alloc_user r1 / size /\ x = k * (size / 16)).
    { intros x Hx. destruct (A10 x Hx) as [(k & Hk & Ha & Hb) Mx]. exists k.
      unfold chunk_of_compact, region_of in Ha. unfold region_of in Hb. fold r1 in Hb. subst size.
      assert (E16 : 16 * x = k * class_size c) by lia.
      split; [| clear -E16 S16; rewrite S16 in E16; lia]. split; [exact Hk|].
      assert (k + 1 <= rg_alloc_user r1 / class_size c); [| clear -H; lia].
      apply Z.div_le_lower_bound; clear -Hb SZB; lia. }
    pose proof (pigeonhole_multiples (rg_free r1) (rg_alloc_user r1 / size) (size / 16) ltac:(lia) K0 A9 HX) as PG.
    pose proof (div_mul_le (rg_alloc_user r1) size ltac:(lia) ltac:(lia)) as DM.
    eapply Z.le_trans; [| exact DM]. apply Z.mul_le_mono_nonneg_r; [lia| exact PG]. }
  assert (TFB : 4 * total_freed <= kFreeArraySize).
  { subst total_freed. unfold kFreeArraySize. unfold kFreeArrayOffset in MB1. fold r1 in MB1.
    assert (total_le : (rg_num_freed r1 + new_chunks) * size <= rg_mapped_user r1) by (rewrite Z.mul_add_distr_r; lia).
    assert (NN : 0 <= rg_num_freed r1 + new_chunks) by (unfold rg_num_freed; lia).
    assert (M32 : (rg_num_freed r1 + new_chunks) * 32 <= (rg_num_freed r1 + new_chunks) * size) by (apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  eapply hoare_bind.
  { apply (ensure_free_array_space_spec E P D s1 c total_freed Hc TFB WF1 HI1). subst total_freed. fold r1. lia. }
  intros ok2. apply hoare_pre. intros s3 (WF2 & HI2 & GR2 & AL2 & MU2 & FA2 & OK2).
  destruct ok2; cbn [negb].
  2:{ apply hoare_ret. intros s4 ->. split; [exact WF2|]. split; [exact HI2|]. split; [|discriminate].
      exists []. eapply grows_trans_nil; [exact GR1| exact GR2]. }
  specialize (OK2 eq_refl).
  apply hoare_get_bind. intros s4 ->.
  apply hoare_upd_bind. apply hoare_ret. intros s' (s4 & -> & ->).
  fold r1 in AL2, MU2, FA2, OK2 |- *.
  set (r2 := get_region s3 c) in *.
  set (fresh := rev (map (fun i => (rg_alloc_user r2 + i * size) / 16) (ziota 0 (Z.to_nat new_chunks)))).
  set (rn := mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + new_chunks * size) (rg_free r2 ++ fresh) (rg_mapped_fa r2) (rg_n_allocated r2) (rg_n_freed r2)).
  pose proof WF2 as WF2c. destruct WF2c as (WE2 & (R21 & R22) & WREST2).
  pose proof (R22 c Hc) as RC2. unfold region_of in RC2. fold r2 in RC2.
  destruct RC2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  (* [comment removed for export] *)
  assert (QA : exists q, 0 <= q /\ rg_alloc_user r2 = q * size).
  { apply Z.mod_divide in B4; [|lia]. destruct B4 as [q Hq]. exists q. subst size. split; [|exact Hq].
    destruct (Z.le_gt_cases 0 q) as [|NEG]; [assumption|]. exfalso.
    assert (q * class_size c <= (-1) * class_size c) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  destruct QA as (q & Hq0 & HqA).
  assert (FRESHv : forall x, In x fresh <-> exists i, 0 <= i < new_chunks /\ x = (q + i) * (size / 16)).
  { intros x. subst fresh. rewrite <- in_rev, in_map_iff. split.
    - intros (i & Hx & Hi). apply In_ziota in Hi. exists i. split; [lia|]. subst x. rewrite HqA.
      rewrite S16 at 1 2. replace (q * (16 * (size / 16)) + i * (16 * (size / 16))) with (((q + i) * (size / 16)) * 16) by lia.
      rewrite Z.div_mul by lia. reflexivity.
    - intros (i & Hi & ->). exists i. split; [|apply In_ziota; lia]. rewrite HqA.
      rewrite S16 at 1 2. replace (q * (16 * (size / 16)) + i * (16 * (size / 16))) with (((q + i) * (size / 16)) * 16) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
  assert (FRESHlo : forall x, In x fresh -> rg_alloc_user r2 <= 16 * x).
  { intros x Hx. apply FRESHv in Hx as (i & Hi & ->). rewrite HqA.
    assert (0 <= i * size) by (apply Z.mul_nonneg_nonneg; lia).
    replace (16 * ((q + i) * (size / 16))) with ((q + i) * (16 * (size / 16))) by lia. rewrite <- S16. lia. }
  assert (GR3 : grows s3 (set_region c rn s3) c fresh).
  { unfold grows. repeat split; try reflexivity.
    - intros c' NE; rewrite get_set_region_ne by auto; reflexivity.
    - rewrite get_set_region_eq. subst rn; cbn. fold r2. assert (0 <= new_chunks * size) by (apply Z.mul_nonneg_nonneg; lia). lia.
    - rewrite get_set_region_eq. subst rn; cbn. reflexivity.
    - exact FRESHlo. }
  assert (LENF : Z.of_nat (length fresh) = new_chunks).
  { subst fresh. rewrite length_rev, length_map, length_ziota. lia. }
  (* [comment removed for export] *)
  assert (FR2 : rg_free r2 = rg_free r1).
  { destruct GR2 as (_&_&_&_&_&_&_&_&_&_&_&_&X&_). subst r2 r1. rewrite X, app_nil_r. reflexivity. }
  assert (NCS : 0 <= new_chunks * size) by (apply Z.mul_nonneg_nonneg; lia).
  (* [comment removed for export] *)
  assert (OLDlo : forall x, In x (rg_free r2) -> 16 * x + size <= rg_alloc_user r2).
  { intros x Hx. destruct (B10 x Hx) as [Cx _].
    pose proof (carved_below E s3 c _ Hc Cx) as CB. rewrite compact_chunk_id in CB. subst r2 size. exact CB. }
  assert (NDf : List.NoDup fresh).
  { subst fresh. apply NoDup_rev. apply NoDup_map_NoDup_ForallPairs; [| apply NoDup_ziota].
    intros i j Hi Hj Eq. apply In_ziota in Hi. apply In_ziota in Hj.
    rewrite HqA in Eq. rewrite S16 in Eq at 1 2 3 4.
    replace (q * (16 * (size / 16)) + i * (16 * (size / 16))) with (((q + i) * (size / 16)) * 16) in Eq by lia.
    replace (q * (16 * (size / 16)) + j * (16 * (size / 16))) with (((q + j) * (size / 16)) * 16) in Eq by lia.
    rewrite !Z.div_mul in Eq by lia.
    assert (U : 0 < size / 16) by lia.
    destruct (Z.lt_trichotomy i j) as [LT|[EQ|GT]]; [| exact EQ |]; exfalso.
    - assert ((q + i) * (size / 16) < (q + j) * (size / 16)) by (apply Z.mul_lt_mono_pos_r; lia). lia.
    - assert ((q + j) * (size / 16) < (q + i) * (size / 16)) by (apply Z.mul_lt_mono_pos_r; lia). lia. }
  assert (ND' : List.NoDup (rg_free r2 ++ fresh)).
  { apply NoDup_app; [exact B9| exact NDf|]. intros x Ho Hf. specialize (OLDlo x Ho). specialize (FRESHlo x Hf). lia. }
  assert (CARV' : forall x, In x (rg_free r2 ++ fresh) ->
            carved E (set_region c rn s3) c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0).
  { intros x Hx. apply in_app_iff in Hx as [Hx|Hx].
    - destruct (B10 x Hx) as [Cx Mx]. split; [|exact Mx]. eapply carved_mono; [|exact Cx].
      rewrite get_set_region_eq. subst rn; cbn. fold r2. lia.
    - apply FRESHv in Hx as (i & Hi & ->). split.
      + exists (q + i). split; [lia|]. split.
        * unfold chunk_of_compact. replace (16 * ((q + i) * (size / 16))) with ((q + i) * (16 * (size / 16))) by lia.
          rewrite <- S16. subst size. reflexivity.
        * unfold region_of. rewrite get_set_region_eq. subst rn; cbn. rewrite HqA.
          rewrite <- Z.mul_add_distr_r. apply Z.mul_le_mono_nonneg_r; lia.
      + replace (16 * ((q + i) * (size / 16))) with ((q + i) * (16 * (size / 16))) by lia. rewrite <- S16. subst size. apply Z_mod_mult. }
  assert (WF' : AWF (set_region c rn s3)).
  { eapply AWf_frame_grows; [exact Hc| exact HI2| exact GR3| | exact WF2].
    split.
    - rewrite as_regions_set_region. intros c0 r3 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|].
      rewrite lookup_insert_ne in Hl by auto. eapply R21; exact Hl.
    - intros c0 Hc0. cbn zeta. unfold region_of. destruct (Z.eq_dec c c0) as [<-|NE].
      + rewrite get_set_region_eq. subst rn. cbn [rg_alloc_user rg_mapped_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed].
        assert (P1 : 0 <= rg_alloc_user r2 + new_chunks * size <= rg_mapped_user r2) by lia.
        assert (P4 : (rg_alloc_user r2 + new_chunks * size) mod class_size c = 0).
        { subst size. rewrite HqA. replace (q * class_size c + new_chunks * class_size c) with ((q + new_chunks) * class_size c) by lia. apply Z_mod_mult. }
        assert (P8 : 4 * rg_num_freed {| rg_mapped_user := rg_mapped_user r2; rg_alloc_user := rg_alloc_user r2 + new_chunks * size;
                       rg_free := rg_free r2 ++ fresh; rg_mapped_fa := rg_mapped_fa r2; rg_n_allocated := rg_n_allocated r2; rg_n_freed := rg_n_freed r2 |}
                     <= rg_mapped_fa r2).
        { unfold rg_num_freed. cbn [rg_free]. rewrite length_app, Nat2Z.inj_add, LENF, FR2.
          subst total_freed. unfold rg_num_freed in OK2. subst r2. lia. }
        exact (conj P1 (conj B2 (conj B3 (conj P4 (conj B5 (conj B6 (conj B7 (conj P8 (conj ND' (conj CARV' (conj B11 B12))))))))))).
      + rewrite get_set_region_ne by exact NE. specialize (R22 c0 Hc0). unfold region_of in R22.
        destruct R22 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
        refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj _ (conj C11 C12))))))))))).
        intros x Hx. destruct (C10 x Hx) as [Cx Mx]. split; [|exact Mx]. eapply carved_mono; [|exact Cx]. rewrite get_set_region_ne by exact NE. lia. }
  split; [exact WF'|]. split; [cbn; exact HI2|]. split.
  { exists fresh. eapply grows_trans_nil; [exact GR1|]. eapply grows_trans_nil; [exact GR2| exact GR3]. }
  intros _. rewrite get_set_region_eq. subst rn. unfold rg_num_freed. cbn [rg_free]. rewrite length_app, Nat2Z.inj_add, LENF, FR2, FR1.
  fold r0. 
  assert (RQ : requested <= new_chunks).
  { subst new_chunks. apply Z.div_le_lower_bound; [lia|].
    assert (X : rg_alloc_user r0 + requested * size <= rg_mapped_user r1) by exact TOT1.
    assert (Y : rg_alloc_user r1 = rg_alloc_user r0) by exact AL1.
    clear -X Y. rewrite Z.mul_comm. lia. }
  lia.
Qed.

End WF.
End RC__1.
