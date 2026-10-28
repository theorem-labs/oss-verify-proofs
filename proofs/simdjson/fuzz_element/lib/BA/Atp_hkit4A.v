(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_setcapA Atp_hkit3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma live_remove_mid : forall (l1 l2 : list (Z * Z)) p n, List.NoDup (map fst (l1 ++ (p, n) :: l2)) -> live_remove p (l1 ++ (p, n) :: l2) = l1 ++ l2.
Proof.
  intros l1 l2 p n ND. rewrite map_app in ND. cbn [map fst] in ND.
  pose proof (NoDup_remove_2 _ _ _ ND) as NI.
  unfold live_remove. rewrite stdpp.list_basics.list.filter_app.
  rewrite stdpp.list_basics.list.filter_cons_False by (cbn [fst]; rewrite Z.eqb_refl; intros X; exact X).
  fold (live_remove p l1). fold (live_remove p l2).
  rewrite (live_remove_none l1), (live_remove_none l2); [reflexivity| |].
  - intros e He E. apply NI. apply in_or_app. right. rewrite <- E. apply in_map. exact He.
  - intros e He E. apply NI. apply in_or_app. left. rewrite <- E. apply in_map. exact He.
Qed.

Lemma nodup_starts_of_disj : forall l : list (Z * Z),
  (forall l1 p1 n1 l2 p2 n2, l = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) -> p1 + n1 <= p2 \/ p2 + n2 <= p1) ->
  (forall p n, In (p, n) l -> 0 < n) -> List.NoDup (map fst l).
Proof.
  induction l as [|[p n] r IH]; intros HD HP; [constructor|]. cbn [map fst]. constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as ([q k] & E & Hq). cbn [fst] in E. subst q.
    pose proof (HD [] p n r p k eq_refl Hq) as D. pose proof (HP p n (or_introl eq_refl)). pose proof (HP p k (or_intror Hq)). lia.
  - apply IH.
    + intros l1 p1 n1 l2 p2 n2 E Hin. apply (HD ((p, n) :: l1) p1 n1 l2 p2 n2); [rewrite E; reflexivity| right; exact Hin].
    + intros q k Hq. apply (HP q k). right. exact Hq.
Qed.

Lemma six_nodup : forall (copy ia oc idx impl tape sbuf : Z) (r : list Z),
  List.NoDup (copy :: ia :: oc :: idx :: impl :: tape :: sbuf :: r) ->
  List.NoDup [sbuf; tape; ia; oc; idx; impl] /\ ~ In copy [sbuf; tape; ia; oc; idx; impl].
Proof.
  intros copy ia oc idx impl tape sbuf r ND.
  assert (ND7 : List.NoDup (copy :: [ia; oc; idx; impl; tape; sbuf])).
  { change (copy :: ia :: oc :: idx :: impl :: tape :: sbuf :: r) with ((copy :: [ia; oc; idx; impl; tape; sbuf]) ++ r) in ND.
    exact (NoDup_app_remove_r _ _ ND). }
  assert (PM : Permutation [ia; oc; idx; impl; tape; sbuf] [sbuf; tape; ia; oc; idx; impl]).
  { change [ia; oc; idx; impl; tape; sbuf] with ([ia; oc; idx; impl] ++ [tape; sbuf]).
    eapply perm_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_swap. }
  inversion ND7 as [|x l NI ND6]; subst. split.
  - exact (Permutation_NoDup PM ND6).
  - intros Hin. apply NI. exact (Permutation_in _ (Permutation_sym PM) Hin).
Qed.

Lemma six_nodup0 : forall (ia oc idx impl tape sbuf : Z) (r : list Z),
  List.NoDup (ia :: oc :: idx :: impl :: tape :: sbuf :: r) -> List.NoDup [sbuf; tape; ia; oc; idx; impl].
Proof.
  intros ia oc idx impl tape sbuf r ND.
  assert (ND6 : List.NoDup [ia; oc; idx; impl; tape; sbuf]).
  { change (ia :: oc :: idx :: impl :: tape :: sbuf :: r) with ([ia; oc; idx; impl; tape; sbuf] ++ r) in ND. exact (NoDup_app_remove_r _ _ ND). }
  assert (PM : Permutation [ia; oc; idx; impl; tape; sbuf] [sbuf; tape; ia; oc; idx; impl]).
  { change [ia; oc; idx; impl; tape; sbuf] with ([ia; oc; idx; impl] ++ [tape; sbuf]).
    eapply perm_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_swap. }
  exact (Permutation_NoDup PM ND6).
Qed.

Lemma stk_wmono : forall (m m' : mem) lo hi, stk asegs m lo hi -> wmono asegs m m' -> lo <= hi -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) WM LH.
  assert (W : wr_at asegs m lo (hi - lo)).
  { split; [exact H0|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). }
  pose proof (wr_at_stk m' lo (hi - lo) (wr_at_transport asegs m m' _ _ W WM)) as S. replace (lo + (hi - lo)) with hi in S by lia. exact S.
Qed.

Lemma bytes_at_nil_any : forall (m m' : mem) d, bytes_at asegs m d [] -> bytes_at asegs m' d [].
Proof. intros m m' d (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma u32s_of_bytes : forall (k : nat) (bs : list byte), length bs = (4 * k)%nat -> exists ws, u32s ws = bs /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [|discriminate]. exists []. split; reflexivity.
  - destruct bs as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in L; try lia.
    destruct (IH r ltac:(lia)) as (ws & E & LW).
    exists (Z_to_bv 64 (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))) :: ws).
    split; [| cbn [length]; lia]. cbn [u32s]. rewrite E. f_equal.
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
    pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
    unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
    set (z := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
    unfold le4. rewrite unsigned_lit by (subst z; lia). cbn [Z_to_le_bytes].
    assert (BY : forall (b : byte) q, Z_to_bv 8 (bv_unsigned b + 256 * q) = b).
    { intros b q. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      replace (bv_unsigned b + 256 * q) with (bv_unsigned b + q * 256) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. }
    assert (D1 : z / 256 = bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))
      by (symmetry; apply (Z.div_unique_pos z 256 _ (bv_unsigned b0)); subst z; lia).
    assert (D2 : (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)) / 256 = bv_unsigned b2 + 256 * bv_unsigned b3)
      by (symmetry; apply (Z.div_unique_pos _ 256 _ (bv_unsigned b1)); lia).
    assert (D3 : (bv_unsigned b2 + 256 * bv_unsigned b3) / 256 = bv_unsigned b3)
      by (symmetry; apply (Z.div_unique_pos _ 256 _ (bv_unsigned b2)); lia).
    rewrite ?Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite D1, D2, D3.
    subst z. rewrite !BY. replace (bv_unsigned b3) with (bv_unsigned b3 + 256 * 0) at 1 by lia. rewrite BY. reflexivity.
Qed.

Lemma u32arr_of_wr : forall (m : mem) A (k : nat), wr_at asegs m A (4 * Z.of_nat k) -> exists ws, u32arr asegs m A ws /\ length ws = k.
Proof.
  intros m A k W. destruct (wr_at_rw_CB m A _ W ltac:(lia)) as (junk & H).
  pose proof (u8arr_of_rw_cells asegs m A _ junk H) as [HB HW].
  destruct H as [[[HL _] _] _]. cbn [cell_wf] in HL.
  destruct (u32s_of_bytes k junk ltac:(lia)) as (ws & Ews & LW).
  exists ws. split; [| exact LW]. split; [rewrite Ews; exact HB|]. rewrite LW. exact W.
Qed.

Lemma u8arr_of_wr : forall (m : mem) A (k : nat), wr_at asegs m A (Z.of_nat k) -> exists bs, u8arr asegs m A bs /\ length bs = k.
Proof.
  intros m A k W. destruct (wr_at_rw_CB m A _ W ltac:(lia)) as (junk & H).
  pose proof (u8arr_of_rw_cells asegs m A _ junk H) as U.
  destruct H as [[[HL _] _] _]. cbn [cell_wf] in HL. exists junk. split; [exact U| lia].
Qed.

Definition BOM_LIT : Z := 0x237e0.
Definition BOM_BYTES : list byte := [Z_to_bv 8 0xef; Z_to_bv 8 0xbb; Z_to_bv 8 0xbf].
Lemma bom_image : ro_bytes_b asegs BOM_LIT BOM_BYTES = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bom_at : forall m : mem, mem_inv asegs m -> bytes_at asegs m BOM_LIT BOM_BYTES.
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold BOM_LIT; lia| unfold BOM_LIT; cbn; lia|]. apply ro_bytes_b_sound. exact bom_image. Qed.

Lemma padded_of_copy : forall (m : mem) copy (bs : list byte),
  bytes_at asegs m copy bs -> bytes_at asegs m (copy + Z.of_nat (length bs)) (repeat z8 64) ->
  bytes_at asegs m copy (padded_bytes (map bv_unsigned bs)).
Proof.
  intros m copy bs H1 H2. unfold padded_bytes. rewrite zbytes_unsigned. apply bytes_at_app. split; [exact H1| exact H2].
Qed.

Lemma padded_skip3 : forall (m : mem) copy (bs : list byte), (3 <= length bs)%nat ->
  bytes_at asegs m copy (padded_bytes (map bv_unsigned bs)) ->
  bytes_at asegs m (copy + 3) (padded_bytes (map bv_unsigned (skipn 3 bs))).
Proof.
  intros m copy bs L H. unfold padded_bytes in *. rewrite zbytes_unsigned in *.
  rewrite <- (firstn_skipn 3 bs) in H at 1. rewrite <- app_assoc in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma cap_arith : forall len blen cap, cap = Z.max len 32 -> 0 <= blen <= len -> len < 2^26 ->
  32 <= cap <= 2^26 /\ blen + 3 <= roundup64 (cap + 3) /\ roundup64 (cap + 3) <= 2^40
  /\ 5 * blen + 5 <= 3 * al_sbuf cap /\ al_sbuf cap <= 2^40 /\ al_sbuf cap mod 8 = 0
  /\ blen + 4 <= roundup64 cap + 9 /\ roundup64 cap + 9 < 2^40 /\ 0 <= roundup64 cap + 9
  /\ al_tape cap = 8 * roundup64 (cap + 3) /\ sc_idx cap = 4 * (roundup64 cap + 9).
Proof.
  intros len blen cap -> B L. unfold al_sbuf, al_tape, sc_idx, roundup64. change (2^26) with 67108864 in *. change (2^40) with 1099511627776.
  assert (C : 32 <= Z.max len 32 <= 67108864) by lia. assert (BC : blen <= Z.max len 32) by lia.
  set (cap := Z.max len 32) in *. clearbody cap. clear L B.
  repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.

Section Kit4.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma live_starts_nodup : forall Σ m, ART RT Σ m -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
  intros Σ m HA HP. apply nodup_starts_of_disj; [| exact HP].
  intros l1 p1 n1 l2 p2 n2 E Hin. exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA E Hin).
Qed.

Lemma shz_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN + 8 <= a -> 0 <= n -> a + n <= USTACK_TOP -> shz m a n.
Proof using AF.
  intros Σ m a n HA LO N0 HI.
  pose proof (af_sp0_range RT AF Σ m HA) as SPR. pose proof (af_sp0_win RT AF Σ m HA) as SPW.
  set (a' := 8 * (a / 8)). set (e := 8 * ((a + n + 7) / 8)).
  assert (A' : a' <= a < a' + 8) by (subst a'; pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia).
  assert (A8 : a' mod 8 = 0) by (subst a'; rewrite Z.mul_comm; apply Z.mod_mul; lia).
  assert (E' : a + n <= e /\ e <= USTACK_TOP) by (subst e; unfold USTACK_TOP in *; Z.div_mod_to_equations; lia).
  assert (L8 : (e - a') mod 8 = 0).
  { subst e a'. replace (8 * ((a + n + 7) / 8) - 8 * (a / 8)) with (((a + n + 7) / 8 - a / 8) * 8) by lia. apply Z.mod_mul. lia. }
  pose proof (af_acc_stack RT AF Σ m a' (e - a') HA ltac:(lia) ltac:(lia)) as AC.
  pose proof (shz_of_acc m a' _ AC A8 ltac:(ul)) as S.
  eapply shz_sub; [exact S| lia|]. pose proof (Z.div_mod (e - a') 8 ltac:(lia)). lia.
Qed.

Lemma shz_static : forall Σ m a n, ART RT Σ m -> a mod 8 = 0 -> 0 <= a -> n mod 8 = 0 ->
  (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x16ed30 <= a + i < 0x170570)) -> shz m a n.
Proof using AF.
  intros Σ m a n HA A8 A0 N8 HC. pose proof (af_acc_static RT AF Σ m a n HA A0 HC) as AC.
  pose proof (shz_of_acc m a n AC A8 A0) as S. replace (8 * (n / 8)) with n in S; [exact S|].
  pose proof (Z.div_mod n 8 ltac:(lia)). lia.
Qed.

Lemma shz_lit : forall Σ m a n, ART RT Σ m -> In (a, n) ACC_LITS -> a mod 8 = 0 -> 0 <= a -> n mod 8 = 0 -> shz m a n.
Proof using AF.
  intros Σ m a n HA Hin A8 A0 N8. pose proof (shz_of_acc m a n (acc_lit RT AF Σ m a n HA Hin) A8 A0) as S.
  replace (8 * (n / 8)) with n in S; [exact S|]. pose proof (Z.div_mod n 8 ltac:(lia)). lia.
Qed.

End Kit4.
