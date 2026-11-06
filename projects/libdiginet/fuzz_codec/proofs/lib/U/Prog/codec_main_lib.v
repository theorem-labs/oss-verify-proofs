From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_main_inv.
Import ListNotations.
Open Scope Z_scope.

(** ---- reshaping a region of the frame ---- *)

(** The same bytes described by a different list of cells: how a region of [fr] becomes the cells a
    callee's contract asks for (a byte block as a typed cell, or split in two). *)
Lemma rw_cells_same_bytes : forall m A cs1 cs2,
  cells_wf cs2 -> cells_bytes cs1 = cells_bytes cs2 -> cells_size cs1 = cells_size cs2 ->
  rw_cells rsegs m A cs1 -> rw_cells rsegs m A cs2.
Proof.
  intros m A cs1 cs2 W2 EB ES [[W1 B1] HW].
  split; [split; [exact W2 | rewrite <- EB; exact B1] |].
  rewrite <- ES. exact HW.
Qed.

Lemma rw_cells_CB1 : forall m A b, rw_cells rsegs m A [CB 1 [b]] -> rw_cells rsegs m A [C1 b].
Proof.
  intros m A b H. apply (rw_cells_same_bytes m A [CB 1 [b]] [C1 b]);
    [cbn; repeat split | reflexivity | reflexivity | exact H].
Qed.

Lemma rw_cells_C1B : forall m A b, rw_cells rsegs m A [C1 b] -> rw_cells rsegs m A [CB 1 [b]].
Proof.
  intros m A b H. apply (rw_cells_same_bytes m A [C1 b] [CB 1 [b]]);
    [cbn; repeat split | reflexivity | reflexivity | exact H].
Qed.

(** A byte block split at [k]: the two halves at their own bases. *)
Lemma rw_cells_CB_split : forall m A n k bs, length bs = n -> (k <= n)%nat ->
  rw_cells rsegs m A [CB n bs] ->
  rw_cells rsegs m A [CB k (firstn k bs)] /\
  rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros m A n k bs Hl Hk H.
  apply (rw_cells_same_bytes m A [CB n bs]
          ([CB k (firstn k bs)] ++ [CB (n - k) (skipn k bs)])) in H.
  - apply rw_cells_app_split in H.
    cbn [cells_size csize Nat.add] in H. rewrite Nat.add_0_r in H. exact H.
  - cbn. split; [rewrite length_firstn; lia|]. split; [rewrite length_skipn; lia | exact I].
  - cbn. rewrite !app_nil_r. symmetry. apply firstn_skipn.
  - cbn. lia.
Qed.

(** The two halves back together. *)
Lemma rw_cells_CB_join : forall m A n k bs, length bs = n -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k bs)] ->
  rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)] ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A n k bs Hl Hk H1 H2.
  apply (rw_cells_same_bytes m A ([CB k (firstn k bs)] ++ [CB (n - k) (skipn k bs)]) [CB n bs]).
  - cbn. split; [lia | exact I].
  - cbn. rewrite !app_nil_r. apply firstn_skipn.
  - cbn. lia.
  - apply rw_cells_app_join; [exact H1|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2.
Qed.

(** ---- the frame across a call ---- *)

(** A callee's window below the frame: the composed window of the walk is unchanged. *)
Lemma munch_frame : forall (s a : Z) (m0 m1 m2 : word -> option byte),
  munch [(s - 640, s)] m0 m1 -> munch [(a, s + -416)] m1 m2 -> s - 640 <= a ->
  munch [(s - 640, s)] m0 m2.
Proof.
  intros s a m0 m1 m2 H1 H2 Ha. apply (munch_trans _ m0 m1 m2 H1).
  apply (munch_weaken [(a, s + -416)]); [| exact H2].
  intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
Qed.

(** ... and the frame regions, all at or above the callee's stack pointer, keep their cells. *)
Lemma fr_munch : forall E m1 m2 kc cur nl u0 pj tj plj (a : Z),
  fr E m1 kc cur nl u0 pj tj plj ->
  munch [(a, bv_unsigned (c_sp E) + -416)] m1 m2 -> wmono rsegs m1 m2 ->
  fr E m2 kc cur nl u0 pj tj plj.
Proof.
  intros E m1 m2 kc cur nl u0 pj tj plj a (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV) MU WM.
  unfold fr.
  refine (conj HS (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))));
    (eapply rw_cells_transport;
       [ eassumption | exact MU | exact WM | cbn [disjoint_from]; split; [right; lia | exact I] ]).
Qed.

(** ---- a failing encoder writes nothing ---- *)

(** check_range's premise reads "out is what it was"; codec_agree's enc_fail_none says a non-zero
    code comes with no command, and cmd_out of no command is the bytes that were there. *)
Lemma cmd_out_fail : forall (before : list byte) kind od a b c delta bytes n,
  fst (enc_of_call kind od a b c delta bytes n) <> 0 ->
  cmd_out before (snd (enc_of_call kind od a b c delta bytes n)) = before.
Proof.
  intros before kind od a b c delta bytes n H.
  rewrite (enc_fail_none kind od a b c delta bytes n H). reflexivity.
Qed.
