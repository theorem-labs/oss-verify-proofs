(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Gm_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma chain_ok_lower : forall (m : mem) lo lo' f ra1 ras, chain_ok m lo f (ra1 :: ras) -> lo' <= lo -> chain_ok m lo' f (ra1 :: ras).
Proof.
  intros m lo lo' f ra1 ras H L. cbn [chain_ok] in *. destruct H as (H1 & H2 & H3 & H4 & fp1 & H5 & H6 & H7).
  split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exists fp1. auto.
Qed.

(* [comment removed for export] *)
Lemma traces_ra_lo' : Forall (Forall (fun x => 4096 <= x)) CLIENT_TRACES.
Proof.
  apply Forall_forall. intros t Ht. apply Forall_forall. intros x Hx.
  assert (B : forallb (fun t => forallb (fun x => 4096 <=? x) t) CLIENT_TRACES = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B t Ht). rewrite forallb_forall in B. specialize (B x Hx). apply Z.leb_le in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma hdr_args_ok_of : forall v, pix_hdr_ok v -> hdr_args_ok (p_w v) (p_h v) (p_d v).
Proof. intros v (HD & HW & HH & HWPL & HRS). rewrite HWPL in HRS. repeat split; auto; lia. Qed.

(* [comment removed for export] *)
Lemma cmap_obj_agree : forall (live : list (Z * Z)) (P : Z -> Prop) (m m' : mem) cmap cv,
  cmap_obj live m cmap cv -> agree_on P m m' -> (forall a, cmap <= a < cmap + 24 -> P a) -> cmap_obj live m' cmap cv.
Proof.
  intros live P m m' cmap cv ((pad & CMC) & R) AG PL. split; [| exact R].
  exists pad. apply (rw_cells_agree_nw asegs m m' _ _ CMC). intros a Ha. apply AG.
  cbn [cells_size cmap_cells csize Nat.add] in Ha. apply PL. lia.
Qed.

(* [comment removed for export] *)
Lemma live_apart2 : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) p n q k, ART RT Σ m ->
  In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> (p, n) <> (q, k) -> p + n <= q \/ q + k <= p.
Proof.
  intros RT AF Σ m p n q k HA Hp Hq NE. destruct (in_split _ _ Hp) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E).
  rewrite E in Hq. apply in_app_or in Hq. apply in_or_app. destruct Hq as [H|[H|H]]; [left; exact H| | right; exact H].
  exfalso. apply NE. exact H.
Qed.

(* [comment removed for export] *)
Lemma fresh_chunk_ne : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) l1 p n l2 e, ART RT Σ m ->
  rt_live RT Σ = l1 ++ (p, n) :: l2 -> In e (l1 ++ l2) -> 0 < n -> 0 < snd e -> fst e <> p.
Proof.
  intros RT AF Σ m l1 p n l2 [q k] HA E Hin Hn Hk. cbn [fst snd] in *.
  pose proof (af_live_disj RT AF Σ m p n q k l1 l2 HA E Hin) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. unfold le4, sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 (bv_unsigned v)) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap, bv_modulus, bv_half_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2 ^ (Z.of_N 32 - 1)) with (2^31).
  change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648. change (Z.of_N 32) with 32.
  Z.div_mod_to_equations. lia.
Qed.
