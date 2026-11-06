(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk Frame SymExec SymExec2 SymExec2Sound RefNodes RefReadLib LibIface.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Definition fds_file (path : list byte) (off : word) : list (word * FdEntry) :=
  (Z_to_bv 64 3, FdFile path off) :: fds_std.

Definition pref (n : Z) (l : list byte) : list byte := firstn (Z.to_nat n) l.
Definition dropz (n : Z) (l : list byte) : list byte := skipn (Z.to_nat n) l.
Arguments pref : simpl never.
Arguments dropz : simpl never.

Global Strategy 1000 [pref dropz].

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

Lemma pref_app : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  pref a l ++ pref b (dropz a l) = pref (a + b) l.
Proof.
  intros a b l Ha Hb. unfold pref, dropz. rewrite Z2Nat.inj_add by lia. rewrite firstn_skipn_comm.
  transitivity (firstn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l) ++ skipn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l)).
  - f_equal. rewrite firstn_firstn. f_equal. lia.
  - apply firstn_skipn.
Qed.

Lemma pref_dropz_app : forall n l, pref n l ++ dropz n l = l.
Proof. intros n l. unfold pref, dropz. apply firstn_skipn. Qed.

Lemma pref_all : forall n l, (Z.of_nat (length l) <= n)%Z -> pref n l = l.
Proof. intros n l H. unfold pref. apply firstn_all2. lia. Qed.

Section ModelVocab.
Context {AC : AllocCeiling}.
  Context {AMB : Amb}.

  Definition at_off (path : list byte) (mo : Model) (held : Z) : Model :=
    with_fds (fds_file path (Z_to_bv 64 held)) mo.

  Definition closed3 (mo : Model) : Model := with_fds fds_std mo.

  Lemma at_off_read : forall path mo held (off' : word),
    with_fds (fd_insert (m_fds (at_off path mo held)) (Z_to_bv 64 3) (FdFile path off')) (at_off path mo held)
    = with_fds (fds_file path off') mo.
  Proof. intros. reflexivity. Qed.

  Lemma at_off_close : forall path mo held,
    with_fds (fd_remove (m_fds (at_off path mo held)) (Z_to_bv 64 3)) (at_off path mo held) = closed3 mo.
  Proof. intros. reflexivity. Qed.

  Lemma at_off_eta : forall path mo held,
    m_fds mo = fds_file path (Z_to_bv 64 held) -> at_off path mo held = mo.
  Proof.
    intros path mo held H. unfold at_off, with_fds. destruct mo as [fd vm io fsy pr li ti]. cbn.
    unfold m_fds in H. cbn in H. destruct fd as [tab pipes]. cbn in H |- *. subst tab. reflexivity.
  Qed.

  Lemma mstd_at_off : forall path mo held, mstd mo -> mstd (at_off path mo held).
  Proof. intros path mo held [A B C D]. constructor; assumption. Qed.

End ModelVocab.
