(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ivl_disj (a b : Z * Z) : Prop := fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Fixpoint pairwise_disj (l : list (Z * Z)) : Prop :=
  match l with [] => True | x :: r => Forall (ivl_disj x) r /\ pairwise_disj r end.

Definition live_reg (RT : rt_sig) (Σ : rts RT) (X size : Z) : Prop :=
  exists p n, In (p, n) (rt_live RT Σ) /\ p mod 8 = 0 /\ p <= X /\ X + size <= p + n.

Lemma zbytes_unsigned : forall bs : list byte, zbytes (map bv_unsigned bs) = bs.
Proof.
  induction bs as [|b r IH]; [reflexivity|]. unfold zbytes in *. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma bytes_ok_unsigned : forall bs : list byte, SjS1Out.bytes_ok (map bv_unsigned bs).
Proof.
  intros bs. unfold SjS1Out.bytes_ok. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma blen_unsigned : forall bs : list byte, blen (map bv_unsigned bs) = Z.of_nat (length bs).
Proof. intros. unfold blen. rewrite length_map. reflexivity. Qed.

Lemma pairwise_disj_nth : forall l i j a b, pairwise_disj l -> nth_error l i = Some a -> nth_error l j = Some b -> (i < j)%nat -> ivl_disj a b.
Proof.
  induction l as [|x r IH]; intros i j a b H Hi Hj Hlt; [destruct i; discriminate|].
  destruct H as [HF HP]. destruct j as [|j]; [lia|]. cbn [nth_error] in Hj.
  destruct i as [|i].
  - cbn [nth_error] in Hi. injection Hi as ->. rewrite Forall_forall in HF. apply HF. eapply nth_error_In. exact Hj.
  - cbn [nth_error] in Hi. eapply IH; eauto. lia.
Qed.

Lemma u32arr_agree_nw : forall m m' a ws, u32arr asegs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> u32arr asegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA. split; [| exact (wr_at_agree_nw asegs m m' a _ Hw HA)].
  apply (bytes_at_agree asegs m m' a _ Hb). rewrite u32s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
Qed.
Lemma u8arr_agree_nw : forall m m' a bs, u8arr asegs m a bs ->
  agree_on (fun x => a <= x < a + Z.of_nat (length bs)) m m' -> u8arr asegs m' a bs.
Proof.
  intros m m' a bs [Hb Hw] HA. split; [| exact (wr_at_agree_nw asegs m m' a _ Hw HA)].
  exact (bytes_at_agree asegs m m' a _ Hb HA).
Qed.

Section Kit3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma live_reg_range : forall Σ m X n, ART RT Σ m -> live_reg RT Σ X n -> 0 <= n ->
  0 < X /\ X + n <= rt_sp0 RT Σ - STACK_WIN /\ (X + n <= 0x10000 \/ SEGTOP_A <= X).
Proof using AF.
  intros Σ m X n HA (p & k & Hin & _ & P1 & P2) N0. pose proof (af_live_range RT AF Σ m p k HA Hin) as (R0 & R1 & R2). lia.
Qed.

Lemma live_reg_client : forall Σ X n x sp, live_reg RT Σ X n -> X <= x < X + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x.
Proof.
  intros Σ X n x sp (p & k & Hin & _ & P1 & P2) Hx. right; right; left. exists p, k. split; [exact Hin| lia].
Qed.

Lemma live_reg_of_in : forall Σ p n, In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> live_reg RT Σ p n.
Proof. intros Σ p n Hin P8. exists p, n. split; [exact Hin|]. split; [exact P8| lia]. Qed.

Lemma fresh_apart : forall Σ Σ1 m1 l1 p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ rt_live RT Σ -> In (p, n) l1 -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ Σ1 m1 l1 p n usp a ART1 LV INP FRS SP0 LOW Ha Hr.
  assert (INP1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; left; exact INP).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INP1) as (R0 & R1 & R2). rewrite SP0 in R1.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (q & k & Hin & Hq). destruct (in_split _ _ INP) as (la & lb & EL).
    assert (E1 : rt_live RT Σ1 = la ++ (p, n) :: (lb ++ rt_live RT Σ)) by (rewrite LV, EL, <- app_assoc; reflexivity).
    assert (HIN2 : In (q, k) (la ++ (lb ++ rt_live RT Σ))) by (apply in_or_app; right; apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ1 m1 p n q k la (lb ++ rt_live RT Σ) ART1 E1 HIN2). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & X). specialize (X p n INP1). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (X & _). specialize (X p n INP1). lia.
Qed.

End Kit3.

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

Definition BOM_LIT : Z := 0x23140.
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
  (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x1115d0 <= a + i < 0x111e90)) -> shz m a n.
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

Lemma nodup_rm : forall (l1 : list (Z * Z)) p n l2, List.NoDup (map fst (l1 ++ (p, n) :: l2)) -> List.NoDup (map fst (l1 ++ l2)).
Proof. intros l1 p n l2 H. rewrite map_app in *. cbn [map fst] in H. exact (NoDup_remove_1 _ _ _ H). Qed.

Section Kit5.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma fobj_shadow_client : forall Σ m a n sp x, ART RT Σ m -> fobj RT Σ m a n -> shad a <= x < shad a + (n + 7) / 8 ->
  aclient (rt_live RT Σ) (rt_frames RT Σ) sp x /\ x < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m a n sp x HA FO Hx.
  destruct (fobj_shadow_range RT AF Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  split; [right; right; right; right; exists f, c; split; [exact Hin| lia]|].
  pose proof (af_frames_range RT AF Σ m f c HA Hin) as (F0 & F1 & _).
  pose proof (af_sp0_win RT AF Σ m HA) as SPW. pose proof (af_sp0_range RT AF Σ m HA) as SPR.
  assert (FSZ : 0 <= fs_size c) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (f + fs_size c) <= 17592186044416 + SHB).
  { unfold shad. assert ((f + fs_size c) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; ul). lia. }
  unfold SHB in *. ul.
Qed.

Lemma fobj_pres_ex_stack : forall Σ Σ' live sp d n0 m m' a n, ART RT Σ m -> fobj RT Σ m a n ->
  rt_pres_ex live (rt_frames RT Σ) sp d n0 m m' -> (forall e, In e (rt_live RT Σ) -> In e live) -> rt_frames RT Σ' = rt_frames RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= d -> fobj RT Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp d n0 m m' a n HA FO PRES SUB FRS DLO.
  apply (fobj_agree RT AF Σ Σ' m m' a n HA FO FRS).
  intros x Hx. cbv beta in Hx. destruct (fobj_shadow_client Σ m a n sp (bv_unsigned x) HA FO Hx) as (CL & XLO).
  apply PRES; [apply (aclient_mono _ _ _ _ _ _ _ CL); [exact SUB| auto| lia]| lia].
Qed.

Lemma live_disj_nth : forall Σ m (i j : nat) p1 n1 p2 n2, ART RT Σ m ->
  nth_error (rt_live RT Σ) i = Some (p1, n1) -> nth_error (rt_live RT Σ) j = Some (p2, n2) -> i <> j -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
  intros Σ m i j p1 n1 p2 n2 HA Hi Hj NE.
  pose proof Hi as Hi'. apply nth_error_split in Hi'. destruct Hi' as (l1 & l2 & EL & LEN).
  apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL).
  rewrite EL in Hj. apply in_or_app.
  destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
  - left. rewrite nth_error_app1 in Hj by exact LT. exact (nth_error_In _ _ Hj).
  - right. rewrite nth_error_app2 in Hj by exact GE. destruct (j - length l1)%nat as [|q] eqn:EQ; [lia|]. cbn [nth_error] in Hj. exact (nth_error_In _ _ Hj).
Qed.

Lemma fresh_apart_l : forall Σ1 m1 (l1 L : list (Z * Z)) p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ L -> In (p, n) l1 -> rt_sp0 RT Σ1 - STACK_WIN <= usp -> aclient L (rt_frames RT Σ1) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ1 m1 l1 L p n usp a ART1 LV INP LOW Ha Hr.
  assert (INP1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; left; exact INP).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INP1) as (R0 & R1 & R2).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (q & k & Hin & Hq). destruct (in_split _ _ INP) as (la & lb & EL).
    assert (E1 : rt_live RT Σ1 = la ++ (p, n) :: (lb ++ L)) by (rewrite LV, EL, <- app_assoc; reflexivity).
    assert (HIN2 : In (q, k) (la ++ (lb ++ L))) by (apply in_or_app; right; apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ1 m1 p n q k la (lb ++ L) ART1 E1 HIN2). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & X). specialize (X p n INP1). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (X & _). specialize (X p n INP1). lia.
Qed.

Lemma not_live_stack : forall Σ m x, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= x -> ~ in_live (rt_live RT Σ) x.
Proof using AF. intros Σ m x HA Hx (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n HA Hin). lia. Qed.

Lemma not_live_frame : forall Σ m f k x, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f <= x < f + fs_size k -> ~ in_live (rt_live RT Σ) x.
Proof using AF.
  intros Σ m f k x HA Hf Hx (p & n & Hin & Hp). pose proof (af_frames_range RT AF Σ m f k HA Hf) as (_ & _ & _ & X). specialize (X p n Hin). lia.
Qed.

Lemma not_live_fshadow : forall Σ m f k x, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> shad f <= x < shad (f + fs_size k) -> ~ in_live (rt_live RT Σ) x.
Proof using AF.
  intros Σ m f k x HA Hf Hx (p & n & Hin & Hp). pose proof (af_fshadow_apart RT AF Σ m f k HA Hf) as (X & _). specialize (X p n Hin). lia.
Qed.

Lemma not_live_static : forall Σ m x, ART RT Σ m -> client_static x -> ~ in_live (rt_live RT Σ) x.
Proof using AF.
  intros Σ m x HA Hs (p & n & Hin & Hp). pose proof (client_static_range x Hs). pose proof (af_live_range RT AF Σ m p n HA Hin) as (_ & _ & X).
  unfold SEGTOP_A in *. lia.
Qed.

End Kit5.

Lemma outside_of_not_live : forall (live : list (Z * Z)) (W : list (Z * Z)) x,
  (forall r, In r W -> exists p n, In (p, n) live /\ p <= fst r /\ snd r <= p + n) -> ~ in_live live x -> outside W x.
Proof.
  intros live W x HW NL. induction W as [|[l h] W IH]; [exact I|]. cbn [outside]. split.
  - intros Hr. apply NL. destruct (HW (l, h) (or_introl eq_refl)) as (p & n & Hin & P1 & P2). cbn [fst snd] in P1, P2. exists p, n. split; [exact Hin| lia].
  - apply IH. intros r Hr. apply HW. right. exact Hr.
Qed.

Lemma mcost_le : forall n, 0 <= n -> mcost n <= 2 * n + 16384 + 2097152.
Proof. intros n H. unfold mcost, DCOST. destruct (n <=? 64512); lia. Qed.
Lemma mcost_small : forall n, 0 <= n <= 64512 -> mcost n = 2097152.
Proof. intros n H. unfold mcost, DCOST. destruct (Z.leb_spec n 64512); lia. Qed.

Definition lposx (L : list (Z * Z)) : Prop := forall p n, In (p, n) L -> exists n', In (p, n') L /\ 0 < n'.

Lemma lposx_of_pos : forall L, (forall p n, In (p, n) L -> 0 < n) -> lposx L.
Proof. intros L H p n Hin. exists n. split; [exact Hin| exact (H p n Hin)]. Qed.

Lemma lposx_cons : forall p n L, 0 < n -> lposx L -> lposx ((p, n) :: L).
Proof.
  intros p n L Hn HL q k [E|Hin].
  - injection E as <- <-. exists n. split; [left; reflexivity| exact Hn].
  - destruct (HL q k Hin) as (n' & H1 & H2). exists n'. split; [right; exact H1| exact H2].
Qed.

Lemma lposx_app : forall L1 L2, lposx L1 -> lposx L2 -> lposx (L1 ++ L2).
Proof.
  intros L1 L2 H1 H2 q k Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 q k Hin) as (n' & A & B). exists n'. split; [apply in_or_app; left; exact A| exact B].
  - destruct (H2 q k Hin) as (n' & A & B). exists n'. split; [apply in_or_app; right; exact A| exact B].
Qed.

Lemma lposx_ann_block : forall A n v, 0 < v -> lposx (ann_block A n v).
Proof.
  intros A n v Hv q k Hin. pose proof (ann_block_fst A n v (q, k) Hin) as E. cbn [fst] in E. subst q.
  exists v. split; [apply ann_block_vis| exact Hv].
Qed.

Lemma live_remove_one : forall (x n : Z) (pre1 pre2 L : list (Z * Z)),
  (forall e, In e pre1 -> fst e <> x) -> (forall e, In e pre2 -> fst e <> x) -> (forall e, In e L -> fst e <> x) ->
  live_remove x (pre1 ++ (x, n) :: pre2 ++ L) = pre1 ++ pre2 ++ L.
Proof.
  intros x n pre1 pre2 L H1 H2 HL.
  rewrite live_remove_app', live_remove_cons'. cbn [fst]. rewrite Z.eqb_refl. rewrite live_remove_app'.
  rewrite (live_remove_none' x pre1 H1), (live_remove_none' x pre2 H2), (live_remove_none' x L HL). reflexivity.
Qed.

Section Kit6.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma pos_prefix_facts : forall Σ m (pre acc L : list (Z * Z)),
  ART RT Σ m -> rt_live RT Σ = acc ++ pre ++ L ->
  (forall e, In e pre -> 0 < snd e) -> lposx L ->
  List.NoDup (map fst pre) /\ (forall e e', In e pre -> In e' L -> fst e <> fst e').
Proof using AF.
  intros Σ m pre. induction pre as [|[p n] pre IH]; intros acc L HA E HP HL.
  - split; [constructor| intros e e' [] _].
  - assert (Hn : 0 < n) by exact (HP (p, n) (or_introl eq_refl)).
    assert (DJ : forall q k, In (q, k) (pre ++ L) -> p + n <= q \/ q + k <= p).
    { intros q k Hin. apply (af_live_disj RT AF Σ m p n q k acc (pre ++ L) HA); [rewrite E; reflexivity|].
      apply in_or_app. right. exact Hin. }
    destruct (IH (acc ++ [(p, n)]) L HA ltac:(rewrite E, <- app_assoc; reflexivity) ltac:(intros e He; apply HP; right; exact He) HL) as [ND NI].
    split.
    + cbn [map fst]. constructor; [| exact ND]. intros Hin. apply in_map_iff in Hin. destruct Hin as ([q k] & Eq & Hq). cbn [fst] in Eq. subst q.
      pose proof (HP (p, k) (or_intror Hq)) as Hk. cbn [snd] in Hk. destruct (DJ p k ltac:(apply in_or_app; left; exact Hq)); lia.
    + intros e e' [<-|He] He'; [| exact (NI e e' He He')]. cbn [fst]. destruct e' as [q k]. cbn [fst]. intros <-.
      destruct (HL p k He') as (n' & Hin' & Hn'). destruct (DJ p n' ltac:(apply in_or_app; right; exact Hin')); lia.
Qed.

End Kit6.
