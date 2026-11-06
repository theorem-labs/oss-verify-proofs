(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Lept_objkit Gm_iface Gm_kit Gm_livekit Gm_livekit2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma keeps_live_of_munch : forall (live : list (Z * Z)) W (m m' : mem),
  munch W m m' -> (forall b k x, In (b, k) live -> b <= x < b + k -> outside W x) -> keeps_live live m m'.
Proof. intros live W m m' MU OUT b k Hin a Ha. apply MU. exact (OUT b k _ Hin Ha). Qed.

Lemma keeps_live_of_agree : forall (live : list (Z * Z)) frs sp W (m m' : mem),
  agree_on (fun a => aclient live frs sp a /\ outside W a) m m' ->
  (forall b k x, In (b, k) live -> b <= x < b + k -> outside W x) -> keeps_live live m m'.
Proof.
  intros live frs sp W m m' AG OUT b k Hin a Ha. apply AG.
  split; [right; right; left; exists b, k; split; [exact Hin| exact Ha]| exact (OUT b k _ Hin Ha)].
Qed.

Lemma keeps_live_sub : forall (live live' : list (Z * Z)) (m m' : mem),
  keeps_live live m m' -> (forall e, In e live' -> In e live) -> keeps_live live' m m'.
Proof. intros live live' m m' K S b k Hin a Ha. exact (K b k (S _ Hin) a Ha). Qed.

Section DrvKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_outside_frame1 : forall Σ (m : mem) fr usp slo b k x,
  ART RT Σ m -> In (fr, 1%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (b, k) (rt_live RT Σ) -> b <= x < b + k ->
  outside [(slo, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] x.
Proof using AF.
  intros Σ m fr usp slo b k x HA FIN SLO QIN Hx.
  pose proof (af_live_range RT AF Σ m b k HA QIN) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m fr 1%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV b k QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 1%nat HA FIN) as (SA1 & _). specialize (SA1 b k QIN).
  change (fs_size 1) with 128 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma live_outside_local : forall Σ (m : mem) fr kf off b k x,
  ART RT Σ m -> In (fr, kf) (rt_frames RT Σ) -> 0 <= off -> off + 8 <= fs_size kf ->
  In (b, k) (rt_live RT Σ) -> b <= x < b + k -> outside [(fr + off, fr + off + 8)] x.
Proof using AF.
  intros Σ m fr kf off b k x HA FIN O1 O2 QIN Hx.
  pose proof (af_frames_range RT AF Σ m fr kf HA FIN) as (_ & _ & _ & FLV). specialize (FLV b k QIN).
  cbn [outside]. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma live_nodup : forall Σ (m : mem), ART RT Σ m -> (forall q k, In (q, k) (rt_live RT Σ) -> 0 < k) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
  intros Σ m HA.
  assert (G : forall L : list (Z * Z),
             (forall l1 p n l2 q k, L = l1 ++ (p, n) :: l2 -> In (q, k) (l1 ++ l2) -> p + n <= q \/ q + k <= p) ->
             (forall q k, In (q, k) L -> 0 < k) -> List.NoDup (map fst L)).
  { induction L as [|[p n] L IH]; intros D P; [constructor|]. cbn [map fst]. constructor.
    - intros Hin. apply List.in_map_iff in Hin. destruct Hin as ([q k] & E & Hin). cbn [fst] in E. subst q.
      pose proof (D [] p n L p k eq_refl Hin) as Q. pose proof (P p n (or_introl eq_refl)) as Pn. pose proof (P p k (or_intror Hin)) as Pk. lia.
    - apply IH.
      + intros l1 p' n' l2 q k E Hin. apply (D ((p, n) :: l1) p' n' l2 q k); [rewrite E; reflexivity| right; exact Hin].
      + intros q k Hin. exact (P q k (or_intror Hin)). }
  intros P. apply G; [| exact P].
  intros l1 p n l2 q k E Hin. exact (af_live_disj RT AF Σ m p n q k l1 l2 HA E Hin).
Qed.

End DrvKit.

(* [comment removed for export] *)
Lemma live_remove_mid : forall p n (l1 l2 : list (Z * Z)), List.NoDup (map fst (l1 ++ (p, n) :: l2)) ->
  live_remove p (l1 ++ (p, n) :: l2) = l1 ++ l2.
Proof.
  intros p n l1. induction l1 as [|[q k] l1 IH]; intros l2 ND.
  - cbn [app] in *. rewrite live_remove_head. apply live_remove_fresh. intros e He E.
    cbn [map fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as (NI & _). apply NI. rewrite <- E. apply List.in_map. exact He.
  - cbn [app map fst] in *. apply List.NoDup_cons_iff in ND. destruct ND as (NI & ND).
    rewrite live_remove_other.
    + f_equal. exact (IH l2 ND).
    + intros E. apply NI. rewrite E. rewrite List.map_app. apply List.in_or_app. right. left. reflexivity.
Qed.

Lemma nodup_remove_mid : forall (e : Z * Z) (l1 l2 : list (Z * Z)), List.NoDup (map fst (l1 ++ e :: l2)) -> List.NoDup (map fst (l1 ++ l2)).
Proof. intros e l1 l2 ND. rewrite List.map_app in *. cbn [map] in ND. exact (List.NoDup_remove_1 _ _ _ ND). Qed.

(* [comment removed for export] *)
Lemma live_destroy_mid : forall pix v cv (pre post : list (Z * Z)), p_cmap v = 0 -> p_data v <> 0 ->
  List.NoDup (map fst (pre ++ (p_data v, rsize v) :: (pix, 64) :: post)) ->
  live_destroy pix v cv (pre ++ (p_data v, rsize v) :: (pix, 64) :: post) = pre ++ post.
Proof.
  intros pix v cv pre post CM DNZ ND. unfold live_destroy. rewrite CM. cbn [Z.eqb]. rewrite !rm_opt_0. rewrite (rm_opt_nz _ _ DNZ).
  rewrite (live_remove_mid (p_data v) (rsize v) pre ((pix, 64) :: post) ND).
  apply (live_remove_mid pix 64 pre post). exact (nodup_remove_mid _ _ _ ND).
Qed.

(* [comment removed for export] *)
Lemma pix_obj_carry : forall (liveK live live' : list (Z * Z)) (m m' : mem) pix v cv,
  pix_obj live m pix v cv -> p_cmap v = 0 -> p_data v <> 0 ->
  keeps_live liveK m m' -> In (pix, 64) liveK -> In (p_data v, rsize v) liveK ->
  In (pix, 64) live' -> In (p_data v, rsize v) live' -> pix_obj live' m' pix v cv.
Proof.
  intros liveK live live' m m' pix v cv (PXC & (PIN & P0 & P16 & PN) & HOK & PD & PCM) CM DNZ K KP KD LP LD.
  destruct PD as [PDZ|((DIN & D0 & D16 & DN) & DNE)]; [exfalso; exact (DNZ PDZ)|].
  split; [apply (keeps_live_cells liveK m m' pix 64 pix _ K KP); [lia| cbn; lia| exact PXC]|].
  split; [split; [exact LP| split; [exact P0| split; [exact P16| exact PN]]]|]. split; [exact HOK|].
  split; [right; split; [split; [exact LD| split; [exact D0| split; [exact D16| exact DN]]]| exact DNE]| left; exact CM].
Qed.

(* [comment removed for export] *)
Lemma pix8_opt_carry : forall (liveK live live' : list (Z * Z)) (m m' : mem) r v cv w h,
  (r = 0 \/ (pix_obj live m r v cv /\ p_w v = w /\ p_h v = h /\ p_d v = 8 /\ p_data v <> 0 /\ p_cmap v = 0)) ->
  keeps_live liveK m m' ->
  (r <> 0 -> In (r, 64) liveK /\ In (p_data v, rsize v) liveK /\ In (r, 64) live' /\ In (p_data v, rsize v) live') ->
  (r = 0 \/ (pix_obj live' m' r v cv /\ p_w v = w /\ p_h v = h /\ p_d v = 8 /\ p_data v <> 0 /\ p_cmap v = 0)).
Proof.
  intros liveK live live' m m' r v cv w h [Z0|(PO & R)] K INS; [left; exact Z0| right]. split; [| exact R].
  assert (NZ : r <> 0) by (destruct PO as (_ & (_ & P0 & _) & _); lia).
  destruct (INS NZ) as (I1 & I2 & I3 & I4). destruct R as (_ & _ & _ & DNZ & CM).
  exact (pix_obj_carry liveK live live' m m' r v cv PO CM DNZ K I1 I2 I3 I4).
Qed.

(* [comment removed for export] *)
Lemma pix_obj_chunks : forall (live : list (Z * Z)) (m : mem) pix v cv, pix_obj live m pix v cv -> p_data v <> 0 ->
  In (pix, 64) live /\ In (p_data v, rsize v) live /\ 0 < rsize v /\ 0 < pix /\ 0 < p_data v /\ p_data v <> pix.
Proof.
  intros live m pix v cv (_ & (PIN & P0 & _) & _ & PD & _) DNZ.
  destruct PD as [PDZ|((DIN & D0 & _ & DN) & DNE)]; [exfalso; exact (DNZ PDZ)|]. repeat split; assumption.
Qed.
