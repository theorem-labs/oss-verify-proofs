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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Pm_iface Pm_iface2.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma keeps_live_of_agf : forall lv frs sp (m m' : mem), agree_on (aclient lv frs sp) m m' -> keeps_live lv m m'.
Proof. intros lv frs sp m m' AG b k Hin a Ha. apply AG. right; right; left. exists b, k. split; [exact Hin| exact Ha]. Qed.

(* [comment removed for export] *)
Lemma keeps_live_of_agree : forall lv frs sp W (m m' : mem) L,
  agree_on (fun a => aclient lv frs sp a /\ outside W a) m m' ->
  (forall e, In e L -> In e lv) -> (forall b k x, In (b, k) L -> b <= x < b + k -> outside W x) -> keeps_live L m m'.
Proof.
  intros lv frs sp W m m' L AG S O b k Hin a Ha. apply AG. split; [| exact (O b k _ Hin Ha)].
  right; right; left. exists b, k. split; [exact (S _ Hin)| exact Ha].
Qed.

Lemma keeps_live_sub : forall L L' (m m' : mem), keeps_live L m m' -> (forall e, In e L' -> In e L) -> keeps_live L' m m'.
Proof. intros L L' m m' K S b k Hin a Ha. exact (K b k (S _ Hin) a Ha). Qed.

(* [comment removed for export] *)
Lemma chunk_mono : forall live live' p n, (forall e, In e live -> In e live') -> chunk live p n -> chunk live' p n.
Proof. intros live live' p n S (Hin & R). exact (conj (S _ Hin) R). Qed.
Lemma cmap_obj_mono : forall live live' (m : mem) cmap cv, (forall e, In e live -> In e live') ->
  cmap_obj live m cmap cv -> cmap_obj live' m cmap cv.
Proof.
  intros live live' m cmap cv S (C & CH1 & CH2 & R).
  exact (conj C (conj (chunk_mono _ _ _ _ S CH1) (conj (chunk_mono _ _ _ _ S CH2) R))).
Qed.
Lemma pix_obj_mono : forall live live' (m : mem) pix v cv, (forall e, In e live -> In e live') ->
  pix_obj live m pix v cv -> pix_obj live' m pix v cv.
Proof.
  intros live live' m pix v cv S (C & CH & HOK & HD & HCM).
  split; [exact C| split; [exact (chunk_mono _ _ _ _ S CH)| split; [exact HOK| split]]].
  - destruct HD as [HD|(HD & R)]; [left; exact HD| right; exact (conj (chunk_mono _ _ _ _ S HD) R)].
  - destruct HCM as [HCM|(HCM & R)]; [left; exact HCM| right; exact (conj (cmap_obj_mono _ _ _ _ _ S HCM) R)].
Qed.

(* [comment removed for export] *)
Lemma cmap_obj_keep1 : forall live (m m' : mem) cmap cv, keeps_live [(cmap, 24)] m m' -> cmap_obj live m cmap cv -> cmap_obj live m' cmap cv.
Proof.
  intros live m m' cmap cv K ((pad & Hc) & R). split; [| exact R]. exists pad.
  apply (keeps_live_cells [(cmap, 24)] m m' cmap 24 cmap _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact Hc].
Qed.

(* [comment removed for export] *)
Lemma pix_obj_retarget : forall live live' (m m' : mem) pix v v' cv,
  pix_obj live m pix v cv -> rw_cells asegs m' pix (pix_cells v') ->
  p_w v' = p_w v -> p_h v' = p_h v -> p_d v' = p_d v -> p_wpl v' = p_wpl v -> p_data v' = p_data v -> p_cmap v' = p_cmap v ->
  (forall e, In e live -> In e live') -> (p_cmap v <> 0 -> keeps_live [(p_cmap v, 24)] m m') ->
  pix_obj live' m' pix v' cv.
Proof.
  intros live live' m m' pix v v' cv (C & CH & HOK & HD & HCM) C' EW EH ED EWPL EDAT ECM S K.
  split; [exact C'| split; [exact (chunk_mono _ _ _ _ S CH)| split; [| split]]].
  - unfold pix_hdr_ok in *. rewrite EW, EH, ED, EWPL. exact HOK.
  - unfold rsize in *. rewrite EDAT, EWPL, EH. destruct HD as [HD|(HD & R)]; [left; exact HD| right; exact (conj (chunk_mono _ _ _ _ S HD) R)].
  - rewrite ECM, EDAT. destruct HCM as [HCM|(HCM & R)]; [left; exact HCM| right]. split; [| exact R].
    apply (cmap_obj_mono live live' m' _ cv S). apply (cmap_obj_keep1 live m m' _ cv); [| exact HCM].
    apply K. destruct HCM as (_ & (_ & P0 & _) & _). lia.
Qed.

Section OKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma fresh_chunk_apart : forall Σ' (m : mem) l1 p n live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: live0 -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n live0 frs usp a HA LV FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    assert (Hin' : In (p', n') (l1 ++ live0)) by (apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 live0 HA LV Hin') as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma live_apart2 : forall Σ (m : mem) p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> p <> q ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ m p n q k HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E). rewrite E in H2. apply in_app_or in H2.
  apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2| injection H2 as -> ->; contradiction| right; exact H2].
Qed.
End OKit.
