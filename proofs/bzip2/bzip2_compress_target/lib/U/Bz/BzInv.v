(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_lit : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply sx32_small. rewrite unsigned_lit; lia. Qed.

Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
(* [comment removed for export] *)

Lemma byte_lit_unsigned : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma le1_lit : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_mod_divide. exists (2^56)%Z. reflexivity.
Qed.
Lemma le1_zxb' : forall b : byte, le1 (zxb b) = [b].
Proof. apply le1_zxb. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record dsh := DSH {
  sh_strm : Z;        (* [comment removed for export] *)
  sh_state : Z;       (* [comment removed for export] *)
  sh_soch : byte;     (* [comment removed for export] *)
  sh_p1 : list byte;
  sh_solen : Z;       (* [comment removed for export] *)
  sh_brand : byte;    (* [comment removed for export] *)
  sh_p2 : list byte;
  sh_rNToGo : Z;
  sh_rTPos : Z;
  sh_bsBuff : Z;      (* [comment removed for export] *)
  sh_bsLive : Z;
  sh_n : Z;           (* [comment removed for export] *)
  sh_small : byte;    (* [comment removed for export] *)
  sh_p3 : list byte;
  sh_cbn : Z;         (* [comment removed for export] *)
  sh_verb : Z;        (* [comment removed for export] *)
  sh_origPtr : Z;     (* [comment removed for export] *)
  sh_tPos : word;     (* [comment removed for export] *)
  sh_k0 : word        (* [comment removed for export] *)
}.
End ACeilS1.


Notation HEAD_CELLS h :=
  [C8 (Z_to_bv 64 (sh_strm h)); C4 (Z_to_bv 64 (sh_state h)); C1 (sh_soch h); CB 3 (sh_p1 h);
   C4 (Z_to_bv 64 (sh_solen h)); C1 (sh_brand h); CB 3 (sh_p2 h);
   C4 (Z_to_bv 64 (sh_rNToGo h)); C4 (Z_to_bv 64 (sh_rTPos h)); C4 (Z_to_bv 64 (sh_bsBuff h)); C4 (Z_to_bv 64 (sh_bsLive h));
   C4 (Z_to_bv 64 (sh_n h)); C1 (sh_small h); CB 3 (sh_p3 h); C4 (Z_to_bv 64 (sh_cbn h)); C4 (Z_to_bv 64 (sh_verb h));
   C4 (Z_to_bv 64 (sh_origPtr h)); C4 (sh_tPos h); C4 (sh_k0 h)] (only parsing).
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition dsh_wf (h : dsh) : Prop :=
  length (sh_p1 h) = 3%nat /\ length (sh_p2 h) = 3%nat /\ length (sh_p3 h) = 3%nat /\
  (0 <= sh_state h < 2^31)%Z /\ (0 <= sh_solen h < 2^32)%Z /\
  (0 <= sh_rNToGo h < 2^32)%Z /\ (0 <= sh_rTPos h < 2^32)%Z /\ (0 <= sh_bsBuff h < 2^32)%Z /\ (0 <= sh_bsLive h <= 32)%Z /\
  (1 <= sh_n h <= 9)%Z /\ (0 <= sh_cbn h < 2^31)%Z /\ sh_verb h = 0%Z /\ (0 <= sh_origPtr h < 2^32)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record dsm := DSM {
  sm_tt : Z; sm_ll16 : Z; sm_ll4 : Z;          (* [comment removed for export] *)
  sm_sbcrc : word; sm_sccrc : word; sm_cbcrc : word; sm_cccrc : word;   (* [comment removed for export] *)
  sm_nInUse : Z
}.
End ACeilS2.

Notation MID_CELLS d :=
  [C8 (Z_to_bv 64 (sm_tt d)); C8 (Z_to_bv 64 (sm_ll16 d)); C8 (Z_to_bv 64 (sm_ll4 d));
   C4 (sm_sbcrc d); C4 (sm_sccrc d); C4 (sm_cbcrc d); C4 (sm_cccrc d); C4 (Z_to_bv 64 (sm_nInUse d))] (only parsing).

(* [comment removed for export] *)
Notation SAVE_CELLS j1 snb j2 := [CB 44 j1; C4 (Z_to_bv 64 snb); CB 60 j2] (only parsing).
Section ACeilS3. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record bzs := BZS {
  bs_src : Z; bs_len : Z; bs_ai : Z;      (* [comment removed for export] *)
  bs_til : word; bs_tih : word; bs_q1 : list byte;
  bs_dst : Z; bs_dlen : Z; bs_av : Z;     (* [comment removed for export] *)
  bs_tol : word; bs_toh : word; bs_q2 : list byte;
  bs_S : Z; bs_bzalloc : word; bs_bzfree : word; bs_opaque : word
}.
End ACeilS3.

Notation STRM_CELLS b :=
  [C8 (Z_to_bv 64 (bs_src b + (bs_len b - bs_ai b))); C4 (Z_to_bv 64 (bs_ai b)); C4 (bs_til b); C4 (bs_tih b); CB 4 (bs_q1 b);
   C8 (Z_to_bv 64 (bs_dst b + (bs_dlen b - bs_av b))); C4 (Z_to_bv 64 (bs_av b)); C4 (bs_tol b); C4 (bs_toh b); CB 4 (bs_q2 b);
   C8 (Z_to_bv 64 (bs_S b)); C8 (bs_bzalloc b); C8 (bs_bzfree b); C8 (bs_opaque b)] (only parsing).
Section ACeilS4. Context {ACEIL__ : ACeil}.

Definition bzs_wf (b : bzs) : Prop :=
  length (bs_q1 b) = 4%nat /\ length (bs_q2 b) = 4%nat /\
  (0 <= bs_ai b <= bs_len b)%Z /\ (0 <= bs_av b <= bs_dlen b)%Z /\ (0 <= bs_len b < 2^27)%Z /\ (0 <= bs_dlen b < 2^27)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rand_inv (h : dsh) : Prop :=
  bv_unsigned (sh_brand h) <> 0%Z -> (0 <= sh_rNToGo h <= 998)%Z /\ (0 <= sh_rTPos h < 512)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_bits (b : bzs) (h : dsh) : Z := (8 * bs_ai b + sh_bsLive h)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Recell.
  Variable segs : list Segment.
  Lemma rw_cells_same_bytes : forall m A cs cs',
    cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
    rw_cells segs m A cs -> rw_cells segs m A cs'.
  Proof.
    intros m A cs cs' EB ES WF [H1 H2]. split; [| rewrite <- ES; exact H2].
    unfold cells_at in *. destruct H1 as [W1 B1]. split; [exact WF|]. rewrite <- EB. exact B1.
  Qed.
End Recell.

End ACeilS4.
