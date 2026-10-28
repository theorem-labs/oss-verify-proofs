(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma u32arr_agree : forall m m' a ws, u32arr bsegs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> wmono bsegs m m' -> u32arr bsegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA WM. split; [| exact (wr_at_transport bsegs m m' a _ Hw WM)].
  apply (bytes_at_agree bsegs m m' a _ Hb). rewrite u32s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
Qed.

Lemma rw_cells_CB_intro : forall (m : mem) A (bs : list byte),
  bytes_at bsegs m A bs -> wr_at bsegs m A (Z.of_nat (length bs)) -> rw_cells bsegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Section ClientKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma asta_evt_c : forall Σ PMc Pm Q, mat_stable PMc -> (forall ms, Pm ms -> evt bsegs Q ms) ->
  cps bsegs (ASTA RT Σ PMc Pm) (ASTA RT Σ PMc Q).
Proof using AF.
  intros Σ PMc Pm Q HM H. unfold ASTA.
  apply (ast_evt bsegs SEGTOP_A asegs_wx asegs_below); [| exact H].
  apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact HM].
Qed.

Lemma aclient_split_c : forall Σ m usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m usp a ART0 [H|[H|[H|[H|H]]]].
  - left; lia.
  - right. pose proof (client_static_range a H). pose proof (af_sp0_range RT AF Σ m ART0). ul.
  - right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (F0 & H2 & _).
    pose proof (af_sp0_win RT AF Σ m ART0) as SPW. pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
    assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    assert (SH1 : shad (f + fs_size k) <= 17592186044416 + SHB).
    { unfold shad. assert ((f + fs_size k) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; ul). lia. }
    unfold SHB in *. ul.
Qed.

Lemma aclient_mono : forall live frames sp live' frames' sp' a,
  aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
  aclient live' frames' sp' a.
Proof.
  intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
  - left. lia.
  - right; left. exact H.
  - right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
  - right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
  - right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

Lemma art_client_write : forall Σ (m m' : mem) sp, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
  agree_on (fun a => ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp a) m m' -> wmono bsegs m m' -> ART RT Σ m'.
Proof using AF. intros Σ m m' sp HA Hsp AG WM. exact (af_frame RT AF Σ m m' sp HA Hsp AG WM). Qed.

Lemma shz_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> shz m p (8 * (n / 8)).
Proof using AF.
  intros Σ m p n HA Hin P8. destruct (af_acc_live RT AF Σ m p n HA Hin) as [_ AC].
  pose proof (af_live_range RT AF Σ m p n HA Hin) as (P0 & _).
  apply shz_of_acc; [exact AC| exact P8| lia].
Qed.

Lemma acc_lit : forall Σ m a n, ART RT Σ m -> In (a, n) ACC_LITS -> acc bsegs m a n.
Proof using AF.
  intros Σ m a n HA Hin. pose proof (af_acc_lits RT AF Σ m HA) as F. rewrite Forall_forall in F. exact (F (a, n) Hin).
Qed.

End ClientKit.
