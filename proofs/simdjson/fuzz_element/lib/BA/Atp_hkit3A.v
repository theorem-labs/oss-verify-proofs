(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_setcapA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_setmd Sj_h_deldtor Sj_stage2_iface Sj_h_layout.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition impl16 (vptr nsi : word) (p12 : list byte) (idx nxt : word) (p28 : list byte) (cap md : word) (b48 b49 : byte)
    (p50 : list byte) (oc ia bufv lenv docv : word) : list cell :=
  [C8 vptr; C4 nsi; CB 4 p12; C8 idx; C4 nxt; CB 4 p28; C8 cap; C8 md; C1 b48; C1 b49; CB 6 p50; C8 oc; C8 ia; C8 bufv; C8 lenv; C8 docv].

Lemma impl16_s2a : forall vptr n IDX capv OC IA BUF len nxt docv p12 p28 p50,
  s2a_impl_cells vptr n IDX capv OC IA BUF len nxt docv p12 p28 p50
  = impl16 vptr (Z_to_bv 64 n) p12 (Z_to_bv 64 IDX) nxt p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50
           (Z_to_bv 64 OC) (Z_to_bv 64 IA) (Z_to_bv 64 BUF) (Z_to_bv 64 len) docv.
Proof. reflexivity. Qed.

Definition mid16 (p28 : list byte) (cap md : word) (b48 b49 : byte) (p50 : list byte) (oc ia : word) : list byte :=
  p28 ++ le8 cap ++ le8 md ++ [b48] ++ [b49] ++ p50 ++ le8 oc ++ le8 ia.

Lemma impl16_wf : forall (m : mem) A vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv,
  rw_cells asegs m A (impl16 vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv) ->
  length p12 = 4%nat /\ length p28 = 4%nat /\ length p50 = 6%nat.
Proof.
  intros until docv. intros ((W & _) & _). unfold impl16 in W. cbn [cells_wf cell_wf] in W.
  destruct W as (_ & _ & L12 & _ & _ & L28 & _ & _ & _ & _ & L50 & _). auto.
Qed.

Lemma impl16_s1 : forall (m : mem) A vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv,
  rw_cells asegs m A (impl16 vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv) ->
  rw_cells asegs m A [C8 vptr; C4 nsi; CB 4 p12; C8 idx; C4 nxt; CB 44 (mid16 p28 cap md b48 b49 p50 oc ia); C8 bufv; C8 lenv; CB 8 (le8 docv)].
Proof.
  intros until docv. intros H. destruct (impl16_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (L12 & L28 & L50).
  apply (rw_cells_relayout m A _ _ H).
  - cbn [cells_wf cell_wf]. unfold mid16. rewrite !length_app, !length_le8, L28, L50, L12. cbn [length]. repeat split; reflexivity.
  - unfold impl16, mid16. cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma s1_impl16 : forall (m : mem) A vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv,
  length p28 = 4%nat -> length p50 = 6%nat ->
  rw_cells asegs m A [C8 vptr; C4 nsi; CB 4 p12; C8 idx; C4 nxt; CB 44 (mid16 p28 cap md b48 b49 p50 oc ia); C8 bufv; C8 lenv; CB 8 (le8 docv)] ->
  rw_cells asegs m A (impl16 vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv).
Proof.
  intros until docv. intros L28 L50 H.
  pose proof H as ((W & _) & _). cbn [cells_wf cell_wf] in W. destruct W as (_ & _ & L12 & _).
  apply (rw_cells_relayout m A _ _ H).
  - unfold impl16. cbn [cells_wf cell_wf]. repeat split; assumption.
  - unfold impl16, mid16. cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma dl_of_impl16 : forall (m : mem) A vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv,
  rw_cells asegs m A (impl16 vptr nsi p12 idx nxt p28 cap md b48 b49 p50 oc ia bufv lenv docv) ->
  exists pre8 mid rest, rw_cells asegs m A (dl_cells vptr pre8 idx mid oc ia rest).
Proof.
  intros until docv. intros H. destruct (impl16_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (L12 & L28 & L50).
  exists (le4 nsi ++ p12), (le4 nxt ++ p28 ++ le8 cap ++ le8 md ++ [b48] ++ [b49] ++ p50), (le8 bufv ++ le8 lenv ++ le8 docv).
  apply (rw_cells_relayout m A _ _ H).
  - unfold dl_cells. cbn [cells_wf cell_wf]. rewrite !length_app, !length_le8, !length_le4, L12, L28, L50. cbn [length]. repeat split; reflexivity.
  - unfold dl_cells, impl16. cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.

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
