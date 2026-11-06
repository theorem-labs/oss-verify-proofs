(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Lept_objkit Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma pix_obj_carry_h : forall (liveK live live' : list (Z * Z)) (m m' : mem) pix v cv,
  pix_obj live m pix v cv -> p_cmap v = 0 -> p_data v <> 0 ->
  keeps_live liveK m m' -> In (pix, 64) liveK ->
  In (pix, 64) live' -> In (p_data v, rsize v) live' -> pix_obj live' m' pix v cv.
Proof.
  intros liveK live live' m m' pix v cv (PXC & (PIN & P0 & P16 & PN) & HOK & PD & PCM) CM DNZ K KP LP LD.
  destruct PD as [PDZ|((DIN & D0 & D16 & DN) & DNE)]; [exfalso; exact (DNZ PDZ)|].
  split; [apply (keeps_live_cells liveK m m' pix 64 pix _ K KP); [lia| cbn; lia| exact PXC]|].
  split; [split; [exact LP| split; [exact P0| split; [exact P16| exact PN]]]|]. split; [exact HOK|].
  split; [right; split; [split; [exact LD| split; [exact D0| split; [exact D16| exact DN]]]| exact DNE]| left; exact CM].
Qed.

Section DrvKit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma keeps_live_minus : forall Σ (m0 : mem) frs sp (l1 l2 : list (Z * Z)) d n (m m' : mem),
  ART RT Σ m0 -> rt_live RT Σ = l1 ++ (d, n) :: l2 ->
  agree_on (fun a => aclient (rt_live RT Σ) frs sp a /\ outside [(d, d + n)] a) m m' ->
  keeps_live (l1 ++ l2) m m'.
Proof using AF.
  intros Σ m0 frs sp l1 l2 d n m m' HA E AG b k Hin a Ha. apply AG.
  pose proof (af_live_disj RT AF Σ m0 d n b k l1 l2 HA E Hin) as D.
  split.
  - right; right; left. exists b, k. split; [| exact Ha]. rewrite E. apply List.in_or_app. apply List.in_app_or in Hin.
    destruct Hin as [H|H]; [left; exact H| right; right; exact H].
  - cbn [outside]. split; [lia| exact I].
Qed.

End DrvKit2.

(* [comment removed for export] *)
Lemma nodup_head_ne : forall (d n : Z) (l : list (Z * Z)), List.NoDup (map fst ((d, n) :: l)) -> forall e, In e l -> fst e <> d.
Proof.
  intros d n l ND e He E. cbn [map fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as (NI & _). apply NI. rewrite <- E.
  apply List.in_map. exact He.
Qed.
