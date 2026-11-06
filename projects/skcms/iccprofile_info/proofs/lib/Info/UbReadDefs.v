(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition fds_file (path : list byte) (off : word) : list (word * FdEntry) :=
  (Z_to_bv 64 3, FdFile path off) :: fds_std.

Lemma fds_file_insert : forall path off off',
  fd_insert (fds_file path off) (Z_to_bv 64 3) (FdFile path off') = fds_file path off'.
Proof. intros. reflexivity. Qed.

Lemma fds_file_remove : forall path off, fd_remove (fds_file path off) (Z_to_bv 64 3) = fds_std.
Proof. intros. reflexivity. Qed.

Lemma fds_file_lookup3 : forall path off, fd_lookup (fds_file path off) (Z_to_bv 64 3) = Some (FdFile path off).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition model_pre {AMB : Amb} (path : list byte) (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs) (tid : word) : Model :=
  mkModelC (fds_file path (Z_to_bv 64 0)) VM stdin0 fs0 None (Some tid) None.
Definition model_post {AMB : Amb} (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs) (tid : word) : Model :=
  mkModelC fds_std VM stdin0 fs0 None (Some tid) None.
Definition modelG {AMB : Amb} (path : list byte) (stdin0 : InputStream) (fs0 : Fs) (tid : word) (off : Z) (V : VmMaps) : Model :=
  mkModelC (fds_file path (Z_to_bv 64 off)) V stdin0 fs0 None (Some tid) None.

Lemma modelG_read {AMB : Amb} : forall path stdin0 fs0 tid off V (off' : word),
  with_fds (fd_insert (m_fds (modelG path stdin0 fs0 tid off V)) (Z_to_bv 64 3) (FdFile path off'))
           (modelG path stdin0 fs0 tid off V)
  = mkModelC (fds_file path off') V stdin0 fs0 None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma modelG_close {AMB : Amb} : forall path stdin0 fs0 tid off V,
  with_fds (fd_remove (m_fds (modelG path stdin0 fs0 tid off V)) (Z_to_bv 64 3)) (modelG path stdin0 fs0 tid off V)
  = model_post V stdin0 fs0 tid.
Proof. intros. reflexivity. Qed.

Lemma modelG_0 {AMB : Amb} : forall path stdin0 fs0 tid V,
  modelG path stdin0 fs0 tid 0 V = model_pre path V stdin0 fs0 tid.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition mem_eq_outside (M M' : word -> option byte) (rs : list (word * Z)) : Prop :=
  forall a, outside a rs -> M' a = M a.

Lemma mem_eq_outside_refl : forall M rs, mem_eq_outside M M rs.
Proof. intros M rs a _. reflexivity. Qed.

Lemma mem_eq_outside_trans : forall M1 M2 M3 rs,
  mem_eq_outside M1 M2 rs -> mem_eq_outside M2 M3 rs -> mem_eq_outside M1 M3 rs.
Proof. intros M1 M2 M3 rs A B a Ha. rewrite (B a Ha). apply A, Ha. Qed.

Lemma mem_eq_outside_weaken : forall M M' rs rs',
  (forall a, outside a rs' -> outside a rs) -> mem_eq_outside M M' rs -> mem_eq_outside M M' rs'.
Proof. intros M M' rs rs' Hw H a Ha. apply H, Hw, Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pref (n : Z) (l : list byte) : list byte := firstn (Z.to_nat n) l.
Definition dropz (n : Z) (l : list byte) : list byte := skipn (Z.to_nat n) l.
End WithFP1.

Arguments pref : simpl never.
Arguments dropz : simpl never.
(* [comment removed for export] *)
Global Strategy 1000 [pref dropz].

Section WithFP2. Context {FP : PropExec.FPState}.
Local Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma pref_length : forall n l, (0 <= n)%Z -> Z.of_nat (length (pref n l)) = Z.min n (Z.of_nat (length l)).
Proof. intros n l Hn. unfold pref. rewrite length_firstn. lia. Qed.

Lemma dropz_length : forall n l, (0 <= n)%Z -> Z.of_nat (length (dropz n l)) = Z.max 0 (Z.of_nat (length l) - n).
Proof. intros n l Hn. unfold dropz. rewrite length_skipn. lia. Qed.

Lemma file_read_pref : forall data (off cnt : Z),
  (0 <= off < 2 ^ 64)%Z -> (0 <= cnt < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = pref cnt (dropz off data).
Proof.
  intros data off cnt Ho Hc. rewrite file_read_unguarded. unfold pref, dropz, word_to_nat. rewrite !u_small by lia. reflexivity.
Qed.

Lemma dropz_0 : forall l, dropz 0 l = l.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pref_app : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  pref a l ++ pref b (dropz a l) = pref (a + b) l.
Proof.
  intros a b l Ha Hb. unfold pref, dropz. rewrite Z2Nat.inj_add by lia. rewrite firstn_skipn_comm.
  transitivity (firstn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l) ++ skipn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l)).
  - f_equal. rewrite firstn_firstn. f_equal. lia.
  - apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma pref_dropz_app : forall n l, pref n l ++ dropz n l = l.
Proof. intros n l. unfold pref, dropz. apply firstn_skipn. Qed.

(* [comment removed for export] *)
Lemma pref_all : forall n l, (Z.of_nat (length l) <= n)%Z -> pref n l = l.
Proof. intros n l H. unfold pref. apply firstn_all2. lia. Qed.

Lemma dropz_dropz : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  dropz a (dropz b l) = dropz (b + a) l.
Proof.
  intros a b l Ha Hb. unfold dropz. rewrite skipn_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pref_chain : forall (len n m : Z) l, (0 <= len)%Z -> (0 <= n)%Z -> (0 <= m)%Z ->
  pref n (dropz len l) ++ pref m (dropz (len + n) l) = pref (n + m) (dropz len l).
Proof.
  intros len n m l Hl Hn Hm. rewrite <- (dropz_dropz n len) by lia. apply pref_app; lia.
Qed.

Lemma pref_0 : forall l, pref 0 l = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_chunk : forall content (len want : Z),
  (0 <= len <= Z.of_nat (length content))%Z -> (len < 2 ^ 62)%Z -> (0 <= want < 2 ^ 62)%Z ->
  let bs := file_read content (Z_to_bv 64 len) (Z_to_bv 64 want) in
  let n := Z.of_nat (length bs) in
  n = Z.min want (Z.of_nat (length content) - len) /\ bs = pref n (dropz len content).
Proof.
  intros content len want Hlen Hlen2 Hwant. cbn zeta.
  rewrite file_read_pref by lia.
  pose proof (pref_length want (dropz len content) ltac:(lia)) as PL.
  pose proof (dropz_length len content ltac:(lia)) as DL.
  split; [lia|].
  destruct (Z.le_gt_cases want (Z.of_nat (length content) - len)) as [Hle|Hgt].
  - f_equal. lia.
  - rewrite (pref_all want) by lia. symmetry. apply pref_all. lia.
Qed.
End WithFP2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
