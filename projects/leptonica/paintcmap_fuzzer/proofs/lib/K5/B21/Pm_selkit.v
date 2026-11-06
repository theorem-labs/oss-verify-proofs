(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Pm_iface Pm_walkkit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma pix_obj_keep_hc : forall live (m m' : mem) pix v cv,
  keeps_live [(pix, 64); (p_cmap v, 24)] m m' -> pix_obj live m pix v cv -> pix_obj live m' pix v cv.
Proof.
  intros live m m' pix v cv K (Hc & CH & HOK & HD & HCM).
  split; [| split; [exact CH| split; [exact HOK| split; [exact HD|]]]].
  - apply (keeps_live_cells _ m m' pix 64 pix _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact Hc].
  - destruct HCM as [HCM|(((pad & Hcm) & R1) & R2)]; [left; exact HCM| right]. split; [| exact R2]. split; [| exact R1].
    exists pad. apply (keeps_live_cells _ m m' (p_cmap v) 24 (p_cmap v) _ K ltac:(right; left; reflexivity)); [lia| cbn; lia| exact Hcm].
Qed.

Lemma keeps_live_sub : forall (L L' : list (Z * Z)) (m m' : mem), (forall e, In e L' -> In e L) -> keeps_live L m m' -> keeps_live L' m m'.
Proof. intros L L' m m' SUB K b k Hin a Ha. exact (K b k (SUB _ Hin) a Ha). Qed.

(* [comment removed for export] *)
Lemma keeps_live_of_agree : forall (P : Z -> Prop) (L : list (Z * Z)) (m m' : mem),
  agree_on P m m' -> (forall b k a, In (b, k) L -> b <= a < b + k -> P a) -> keeps_live L m m'.
Proof. intros P L m m' AG HP b k Hin a Ha. apply AG. exact (HP b k _ Hin Ha). Qed.
Lemma keeps_live_of_munch : forall W (L : list (Z * Z)) (m m' : mem),
  munch W m m' -> (forall b k a, In (b, k) L -> b <= a < b + k -> outside W a) -> keeps_live L m m'.
Proof. intros W L m m' MU HP b k Hin a Ha. apply MU. exact (HP b k _ Hin Ha). Qed.

Section PmSelKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma pm_live_apart_sz : forall Σ m p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> n <> k ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ m p n q k HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E). rewrite E in H2. apply in_app_or in H2. apply in_or_app.
  destruct H2 as [X|[X|X]]; [left; exact X| injection X as X1 X2; congruence | right; exact X].
Qed.

(* [comment removed for export] *)
Lemma live_outside_walk2r : forall Σ (m : mem) fr usp slo D N q n a,
  ART RT Σ m -> In (fr, 2%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (q, n) (rt_live RT Σ) -> (q + n <= D \/ D + N <= q) -> q <= a < q + n ->
  outside [(slo, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (D, D + N)] a.
Proof using AF.
  intros Σ m fr usp slo D N q n a HA FIN SLO QIN AP Ha.
  pose proof (live_outside_walk2 RT AF Σ m fr usp slo q n a HA FIN SLO QIN Ha) as O. cbn [outside] in O |- *.
  destruct O as (O1 & O2 & O3 & _). repeat split; try assumption. lia.
Qed.
Lemma keeps_live_walk2r : forall Σ (m m' : mem) fr usp slo D N (L : list (Z * Z)),
  ART RT Σ m -> In (fr, 2%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  (forall q n, In (q, n) L -> In (q, n) (rt_live RT Σ) /\ (q + n <= D \/ D + N <= q)) ->
  munch [(slo, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (D, D + N)] m m' -> keeps_live L m m'.
Proof using AF.
  intros Σ m m' fr usp slo D N L HA FIN SLO HL MU b k Hin a Ha. apply MU. destruct (HL b k Hin) as [QIN AP].
  exact (live_outside_walk2r Σ m fr usp slo D N b k _ HA FIN SLO QIN AP Ha).
Qed.
End PmSelKit.
