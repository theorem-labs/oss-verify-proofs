(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require Import G_fmt_fp_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Inductive shp := S8 | S4 | SB4.
Definition shp_size (s : shp) : nat := match s with S8 => 8 | _ => 4 end%nat.
Fixpoint shp_sum (pat : list shp) : nat := match pat with [] => 0 | s :: pat' => shp_size s + shp_sum pat' end%nat.
Fixpoint shape_cells (pat : list shp) (bs : list byte) : list cell :=
  match pat with
  | [] => []
  | s :: pat' =>
    match s with
    | S8 => C8 (le_bytes_to_word (firstn 8 bs)) :: shape_cells pat' (skipn 8 bs)
    | S4 => C4 (le_bytes_to_word (firstn 4 bs)) :: shape_cells pat' (skipn 4 bs)
    | SB4 => CB 4 (firstn 4 bs) :: shape_cells pat' (skipn 4 bs)
    end
  end.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma shape_wf : forall pat bs, length bs = shp_sum pat -> cells_wf (shape_cells pat bs).
Proof.
  induction pat as [|s pat IH]; intros bs HL; cbn; [exact I|].
  destruct s; cbn in HL |- *; (split; [try exact I; rewrite length_firstn; lia | apply IH; rewrite length_skipn; lia]).
Qed.
Lemma shape_bytes : forall pat bs, length bs = shp_sum pat -> cells_bytes (shape_cells pat bs) = bs.
Proof.
  induction pat as [|s pat IH]; intros bs HL; cbn in HL |- *.
  - destruct bs; [reflexivity | cbn in HL; lia].
  - destruct s; cbn [shp_size] in HL; cbn [cells_bytes cbytes];
      [rewrite le8_of_bytes by (rewrite length_firstn; lia) | rewrite le4_of_bytes by (rewrite length_firstn; lia) |];
      rewrite IH by (rewrite length_skipn; lia); apply firstn_skipn.
Qed.
Lemma shape_size : forall pat bs, cells_size (shape_cells pat bs) = shp_sum pat.
Proof. induction pat as [|s pat IH]; intros bs; cbn; [reflexivity|]. destruct s; cbn; rewrite IH; reflexivity. Qed.

Lemma rw_cells_reshape : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb' Hs'. split; [split; [exact Hwf'|]|].
  - rewrite Hb'. exact Hb.
  - rewrite Hs'. exact Hw.
Qed.

Lemma rw_cells_shape : forall segs m A n bs pat,
  rw_cells segs m A [CB n bs] -> shp_sum pat = n -> rw_cells segs m A (shape_cells pat bs).
Proof.
  intros segs m A n bs pat H Hs. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
  apply (rw_cells_reshape segs m A [CB n bs]); [exact H | apply shape_wf; lia | | cbn; rewrite shape_size; lia].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. apply shape_bytes. lia.
Qed.

(* [comment removed for export] *)
Definition FILE_PAT : list shp :=
  [S4; SB4; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8; S4; S4; S8; S4; S4; S4; SB4; S8; S8; S8; S8; S8; S8; S8; S8; S8; S8].

Lemma file_cells_of_junk : forall segs m A junk, rw_cells segs m A [CB 232 junk] ->
  exists (fl : word) (p0 : list byte) (w8 w16 c24 c32 c40 c48 c56 c64 c72 c80 w88 c96 c104 c112 fd pp c128 md lk lbf : word)
         (p1 : list byte) (c152 c160 c168 c176 c184 c192 c200 c208 c216 c224 : word),
    rw_cells segs m A [C4 fl; CB 4 p0; C8 w8; C8 w16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80;
                       C8 w88; C8 c96; C8 c104; C8 c112; C4 fd; C4 pp; C8 c128; C4 md; C4 lk; C4 lbf; CB 4 p1;
                       C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; C8 c192; C8 c200; C8 c208; C8 c216; C8 c224]
    /\ length p0 = 4%nat /\ length p1 = 4%nat.
Proof.
  intros segs m A junk H. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
  pose proof (rw_cells_shape segs m A 232 junk FILE_PAT H eq_refl) as H'. cbn [shape_cells FILE_PAT] in H'.
  repeat (eexists; []). split; [exact H'|]. split; rewrite length_firstn, ?length_skipn; lia.
Qed.

(* [comment removed for export] *)
Lemma file_cells_zero : forall segs m A, rw_cells segs m A [CB 232 (repeat (Z_to_bv 8 0) 232)] ->
  rw_cells segs m A [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros segs m A H. apply (rw_cells_reshape segs m A _ _ H); [cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.
