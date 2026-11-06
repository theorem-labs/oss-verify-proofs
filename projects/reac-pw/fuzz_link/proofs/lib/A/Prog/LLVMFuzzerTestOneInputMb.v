(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 447 of its 507 lines of code are new or changed and 344 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): MODEL_BEGIN,
   the five stores every operation arm makes before its library call (fuzz_link.c model_begin; listing
   (internal path) (internal record, sha256 e84d6f0c6974), op_refused +0x9b8 ..
   +0xa00 and the same five in the other arms):
     m + MD_SOCKET_ERRNO := g_nl.socket_errno     sw a1, 0(s6)          (a1 = lw 0x20c(s7))
     m + MD_SEND_ERRNO   := g_nl.send_errno       sw a1, 0(a2)          (a1 = lw 0x210(s7), a2 = [s1 + 0xe0])
     m + MD_NEXT         := 0                     sw zero, 0(a1)        (a1 = [s1 + 0xd8])
     m + MD_N_REQ        := 0                     sw zero, 0(a1)        (a1 = [s1 + 0xd0])
     g_nl.n_sent         := 0                     sw zero, 0x2a8(a1)    (a1 = [s1 + 0xc0] = g_nl + 0x42000)
   This file states, for every arm:
   1. the two byte lists after the stores, `lf_kbs_mb kbs` and `lf_mbs_mb kbs mbs`, written with slices of kbs,
      so that their bytes are the bytes the symbolic runner's chunks hold (YN3u.v byte_of_word_le);
   2. their pure facts: the fields the stores set, the fields they leave, nlk_wf, model_wf, marks_are,
      requests_are (plain image: lib/Prog/Slot/LC45RTr.v c45r_kbs_* / c45r_mbs_*, restated over these lists);
   3. `lf_data_mb`: the interface's lf_data at the old memory, the new memory equal to the old one off the five
      ranges, the five stored words in place and writability carried, give lf_data at the new memory with the
      new lists.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN3u.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Byte lists after a store
   ========================================================================== *)

(* bs over cs from index k (lib/Lib/Mem.v upd_bytes, restated here so this file does not load lib/Lib) *)
Definition lf_upd (cs : list byte) (k : nat) (bs : list byte) : list byte :=
  firstn k cs ++ bs ++ skipn (k + length bs) cs.

Lemma lf_upd_length : forall cs k bs, (k + length bs <= length cs)%nat -> length (lf_upd cs k bs) = length cs.
Proof. intros cs k bs H. unfold lf_upd. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma lf_upd_nth : forall cs k bs i, (k + length bs <= length cs)%nat ->
  nth_error (lf_upd cs k bs) i =
    if (Nat.leb k i && Nat.ltb i (k + length bs))%bool then nth_error bs (i - k) else nth_error cs i.
Proof.
  intros cs k bs i Hk. unfold lf_upd.
  destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length bs)); cbn [andb].
  - rewrite nth_error_app2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (Nat.min k (length cs)) with k by lia.
    rewrite nth_error_app1 by lia. reflexivity.
  - rewrite nth_error_app2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (Nat.min k (length cs)) with k by lia.
    rewrite nth_error_app2 by lia.
    rewrite nth_error_skipn. f_equal. lia.
  - rewrite nth_error_app1 by (rewrite length_firstn; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i k); [reflexivity | exfalso; lia].
  - rewrite nth_error_app1 by (rewrite length_firstn; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i k); [reflexivity | exfalso; lia].
Qed.

Lemma lf_slice_nth : forall (c : list byte) off len i, 0 <= off -> 0 <= len ->
  nth_error (slice c off len) i =
    if (i <? Z.to_nat len)%nat then nth_error c (Z.to_nat off + i) else None.
Proof. intros c off len i H0 H1. unfold slice. rewrite nth_error_firstn, nth_error_skipn. reflexivity. Qed.

Lemma lf_slice_length : forall (c : list byte) off len, 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> length (slice c off len) = Z.to_nat len.
Proof. intros c off len H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma lf_slice_upd_other : forall (cs bs : list byte) k off len, 0 <= off -> 0 <= len ->
  (k + length bs <= length cs)%nat ->
  (off + len <= Z.of_nat k \/ Z.of_nat (k + length bs) <= off) ->
  slice (lf_upd cs k bs) off len = slice cs off len.
Proof.
  intros cs bs k off len H0 H1 H2 H3. apply nth_error_ext. intros i.
  rewrite !lf_slice_nth by lia. destruct (Nat.ltb_spec i (Z.to_nat len)); [|reflexivity].
  rewrite lf_upd_nth by exact H2.
  destruct (Nat.leb_spec k (Z.to_nat off + i)), (Nat.ltb_spec (Z.to_nat off + i) (k + length bs));
    cbn; try reflexivity; lia.
Qed.

Lemma lf_rdn_upd_other : forall (cs bs : list byte) k off n, 0 <= off -> 0 <= n ->
  (k + length bs <= length cs)%nat ->
  (off + n <= Z.of_nat k \/ Z.of_nat (k + length bs) <= off) ->
  rdn (lf_upd cs k bs) off n = rdn cs off n.
Proof. intros. unfold rdn. rewrite lf_slice_upd_other by assumption. reflexivity. Qed.

Lemma lf_slice_upd_same : forall (cs xs : list byte) k, (k + length xs <= length cs)%nat ->
  slice (lf_upd cs k xs) (Z.of_nat k) (Z.of_nat (length xs)) = xs.
Proof.
  intros cs xs k H. apply nth_error_ext. intros i.
  rewrite lf_slice_nth by lia. rewrite !Nat2Z.id.
  destruct (Nat.ltb_spec i (length xs)) as [Hi|Hi].
  - rewrite lf_upd_nth by exact H.
    destruct (Nat.leb_spec k (k + i)), (Nat.ltb_spec (k + i) (k + length xs)); try lia.
    cbn [andb]. f_equal. lia.
  - symmetry. apply nth_error_None. exact Hi.
Qed.

(* four zero bytes, and the value of a 4-byte slice *)
Definition lf_z4 : list byte := repeat (Z_to_bv 8 0) 4.
Lemma lf_z4_len : length lf_z4 = 4%nat. Proof. reflexivity. Qed.
Lemma lf_z4_val : bytes_le_to_Z lf_z4 = 0. Proof. reflexivity. Qed.

Lemma lf_rdn_upd_same4 : forall (cs xs : list byte) (k : Z), 0 <= k -> length xs = 4%nat ->
  (Z.to_nat k + 4 <= length cs)%nat -> rdn (lf_upd cs (Z.to_nat k) xs) k 4 = bytes_le_to_Z xs.
Proof.
  intros cs xs k H0 Hl H1. unfold rdn.
  replace k with (Z.of_nat (Z.to_nat k)) at 2 by lia.
  replace 4 with (Z.of_nat (length xs)) by (rewrite Hl; reflexivity).
  rewrite lf_slice_upd_same by lia. reflexivity.
Qed.

Lemma lf_slice_slice4 : forall (c : list byte) off, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  slice (slice c off 4) 0 4 = slice c off 4.
Proof.
  intros c off H0 H1. unfold slice at 1. rewrite skipn_O. apply firstn_all2.
  rewrite lf_slice_length by lia. lia.
Qed.

(* ==========================================================================
   2. The two lists after model_begin, and their facts
   ========================================================================== *)

Definition lf_kbs_mb (kbs : list byte) : list byte := lf_upd kbs (Z.to_nat NK_N_SENT) lf_z4.

Definition lf_mbs_mb (kbs mbs : list byte) : list byte :=
  lf_upd (lf_upd (lf_upd (lf_upd mbs (Z.to_nat MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4))
                         (Z.to_nat MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4))
                 (Z.to_nat MD_NEXT) lf_z4)
         (Z.to_nat MD_N_REQ) lf_z4.

Section Kbs.
Variable kbs : list byte.
Hypothesis KL : Z.of_nat (length kbs) = NK_SIZE.

Lemma lf_kbs_mb_len : Z.of_nat (length (lf_kbs_mb kbs)) = NK_SIZE.
Proof.
  unfold lf_kbs_mb. rewrite lf_upd_length; [exact KL|]. rewrite lf_z4_len.
  unfold NK_N_SENT, NK_SIZE in *. lia.
Qed.

Lemma lf_kbs_mb_rdn : forall off n, 0 <= off -> 0 <= n ->
  (off + n <= NK_N_SENT \/ NK_N_SENT + 4 <= off) -> rdn (lf_kbs_mb kbs) off n = rdn kbs off n.
Proof.
  intros off n H0 H1 H2. unfold lf_kbs_mb. apply lf_rdn_upd_other; [lia | lia | |];
    rewrite ?lf_z4_len; unfold NK_N_SENT, NK_SIZE in *; lia.
Qed.

Lemma lf_kbs_mb_fld : forall off, 0 <= off -> (off + 4 <= NK_N_SENT \/ NK_N_SENT + 4 <= off) ->
  fld_u32 (lf_kbs_mb kbs) off = fld_u32 kbs off.
Proof. intros off H0 H1. unfold fld_u32. apply lf_kbs_mb_rdn; lia. Qed.

Lemma lf_kbs_mb_n_sent : nk_n_sent (lf_kbs_mb kbs) = 0.
Proof.
  unfold nk_n_sent, fld_u32, lf_kbs_mb. rewrite lf_rdn_upd_same4; [exact lf_z4_val | unfold NK_N_SENT; lia | reflexivity |].
  unfold NK_N_SENT, NK_SIZE in *. lia.
Qed.

Lemma lf_kbs_mb_wf : nlk_wf kbs -> nlk_wf (lf_kbs_mb kbs).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  assert (E : forall off, 0 <= off -> (off + 4 <= NK_N_SENT \/ NK_N_SENT + 4 <= off) ->
              fld_u32 (lf_kbs_mb kbs) off = fld_u32 kbs off) by exact lf_kbs_mb_fld.
  pose proof lf_kbs_mb_n_sent as NS.
  unfold nlk_wf. unfold nk_n_chunks, nk_next, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
    nk_end_errno, nk_socket_errno, nk_send_errno in *.
  rewrite NS.
  rewrite !E by (unfold NK_N_CHUNKS, NK_NEXT, NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_END_ERRNO,
                   NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_N_IF, NK_N_SENT; lia).
  split; [exact H1|]. split; [exact H2|]. split; [unfold NL_SENT_MAX; lia|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [exact H11|]. split.
  - intros j Hj. unfold fld_u64.
    rewrite lf_kbs_mb_rdn by (unfold NK_CHUNK_LEN, NK_N_SENT, NL_CHUNKS, NK_N_CHUNKS in *; lia).
    apply H12. exact Hj.
  - intros j Hj. lia.
Qed.

Lemma lf_kbs_mb_fields :
  nk_n_if (lf_kbs_mb kbs) = nk_n_if kbs /\ nk_open (lf_kbs_mb kbs) = nk_open kbs /\
  nk_opened (lf_kbs_mb kbs) = nk_opened kbs /\ nk_closed (lf_kbs_mb kbs) = nk_closed kbs /\
  nk_misuse (lf_kbs_mb kbs) = nk_misuse kbs /\ nk_next (lf_kbs_mb kbs) = nk_next kbs /\
  nk_n_chunks (lf_kbs_mb kbs) = nk_n_chunks kbs /\ nk_end_errno (lf_kbs_mb kbs) = nk_end_errno kbs /\
  nk_socket_errno (lf_kbs_mb kbs) = nk_socket_errno kbs /\ nk_send_errno (lf_kbs_mb kbs) = nk_send_errno kbs.
Proof.
  unfold nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse, nk_next, nk_n_chunks, nk_end_errno,
    nk_socket_errno, nk_send_errno.
  repeat split; apply lf_kbs_mb_fld;
    unfold NK_N_IF, NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_NEXT, NK_N_CHUNKS, NK_END_ERRNO,
      NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_N_SENT; lia.
Qed.
End Kbs.

Section Mbs.
Variables (kbs mbs : list byte).
Hypothesis KL : Z.of_nat (length kbs) = NK_SIZE.
Hypothesis ML : Z.of_nat (length mbs) = MD_SIZE.

Let s1 := slice kbs NK_SOCKET_ERRNO 4.
Let s2 := slice kbs NK_SEND_ERRNO 4.
Let b1 := lf_upd mbs (Z.to_nat MD_SOCKET_ERRNO) s1.
Let b2 := lf_upd b1 (Z.to_nat MD_SEND_ERRNO) s2.
Let b3 := lf_upd b2 (Z.to_nat MD_NEXT) lf_z4.

Lemma lf_mb_s1_len : length s1 = 4%nat.
Proof. unfold s1. rewrite lf_slice_length; [reflexivity | | |]; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia. Qed.
Lemma lf_mb_s2_len : length s2 = 4%nat.
Proof. unfold s2. rewrite lf_slice_length; [reflexivity | | |]; unfold NK_SEND_ERRNO, NK_SIZE in *; lia. Qed.

Lemma lf_mbs_mb_lens : length b1 = length mbs /\ length b2 = length mbs /\ length b3 = length mbs /\
  length (lf_mbs_mb kbs mbs) = length mbs.
Proof.
  pose proof lf_mb_s1_len as S1. pose proof lf_mb_s2_len as S2.
  assert (L1 : length b1 = length mbs)
    by (unfold b1; apply lf_upd_length; rewrite S1; unfold MD_SOCKET_ERRNO, MD_SIZE in *; lia).
  assert (L2 : length b2 = length mbs)
    by (unfold b2; rewrite lf_upd_length; [exact L1 | rewrite L1, S2; unfold MD_SEND_ERRNO, MD_SIZE in *; lia]).
  assert (L3 : length b3 = length mbs)
    by (unfold b3; rewrite lf_upd_length; [exact L2 | rewrite L2, lf_z4_len; unfold MD_NEXT, MD_SIZE in *; lia]).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  unfold lf_mbs_mb. fold s1 s2 b1 b2 b3. rewrite lf_upd_length; [exact L3|].
  rewrite L3, lf_z4_len. unfold MD_SIZE, MD_N_REQ in *. lia.
Qed.

Lemma lf_mbs_mb_len : Z.of_nat (length (lf_mbs_mb kbs mbs)) = MD_SIZE.
Proof. destruct lf_mbs_mb_lens as (_ & _ & _ & L). rewrite L. exact ML. Qed.

Lemma lf_mbs_mb_slice : forall off n, 12 <= off -> 0 <= n -> (off + n <= MD_N_REQ \/ MD_N_REQ + 4 <= off) ->
  slice (lf_mbs_mb kbs mbs) off n = slice mbs off n.
Proof.
  intros off n H0 H1 H2. destruct lf_mbs_mb_lens as (L1 & L2 & L3 & _).
  pose proof lf_mb_s1_len as S1. pose proof lf_mb_s2_len as S2.
  unfold lf_mbs_mb. fold s1 s2 b1 b2 b3.
  rewrite lf_slice_upd_other; [| lia | lia | rewrite L3, lf_z4_len; unfold MD_SIZE, MD_N_REQ in *; lia
                                 | rewrite lf_z4_len; unfold MD_N_REQ in *; lia].
  unfold b3. rewrite lf_slice_upd_other; [| lia | lia | fold b2; rewrite L2, lf_z4_len; unfold MD_NEXT, MD_SIZE in *; lia
                                            | rewrite lf_z4_len; unfold MD_NEXT; lia].
  unfold b2. rewrite lf_slice_upd_other; [| lia | lia | fold b1; rewrite L1, S2; unfold MD_SEND_ERRNO, MD_SIZE in *; lia
                                            | rewrite S2; unfold MD_SEND_ERRNO; lia].
  unfold b1. rewrite lf_slice_upd_other; [reflexivity | lia | lia | rewrite S1; unfold MD_SOCKET_ERRNO, MD_SIZE in *; lia
                                           | rewrite S1; unfold MD_SOCKET_ERRNO; lia].
Qed.

Lemma lf_mbs_mb_n_req : md_n_req (lf_mbs_mb kbs mbs) = 0.
Proof.
  destruct lf_mbs_mb_lens as (L1 & L2 & L3 & _).
  unfold md_n_req, fld_u32, lf_mbs_mb. fold s1 s2 b1 b2 b3.
  rewrite lf_rdn_upd_same4; [exact lf_z4_val | unfold MD_N_REQ; lia | reflexivity |].
  rewrite L3; unfold MD_SIZE, MD_N_REQ in *; lia.
Qed.

Lemma lf_mbs_mb_next : md_next (lf_mbs_mb kbs mbs) = 0.
Proof.
  destruct lf_mbs_mb_lens as (L1 & L2 & L3 & _).
  unfold md_next, fld_u32, lf_mbs_mb. fold s1 s2 b1 b2 b3.
  rewrite lf_rdn_upd_other; [| unfold MD_NEXT; lia | lia | rewrite L3, lf_z4_len; unfold MD_SIZE, MD_N_REQ in *; lia
                              | rewrite lf_z4_len; unfold MD_NEXT, MD_N_REQ; lia].
  unfold b3. rewrite lf_rdn_upd_same4; [exact lf_z4_val | unfold MD_NEXT; lia | reflexivity |].
  fold b2; rewrite L2; unfold MD_NEXT, MD_SIZE in *; lia.
Qed.

Lemma lf_mbs_mb_send : md_send_errno (lf_mbs_mb kbs mbs) = nk_send_errno kbs.
Proof.
  destruct lf_mbs_mb_lens as (L1 & L2 & L3 & _). pose proof lf_mb_s2_len as S2.
  unfold md_send_errno, fld_u32, lf_mbs_mb. fold s1 s2 b1 b2 b3.
  rewrite lf_rdn_upd_other; [| unfold MD_SEND_ERRNO; lia | lia
                              | rewrite L3, lf_z4_len; unfold MD_SIZE, MD_N_REQ in *; lia
                              | rewrite lf_z4_len; unfold MD_SEND_ERRNO, MD_N_REQ; lia].
  unfold b3. rewrite lf_rdn_upd_other; [| unfold MD_SEND_ERRNO; lia | lia
                                         | fold b2; rewrite L2, lf_z4_len; unfold MD_NEXT, MD_SIZE in *; lia
                                         | rewrite lf_z4_len; unfold MD_SEND_ERRNO, MD_NEXT; lia].
  unfold b2. rewrite lf_rdn_upd_same4; [| unfold MD_SEND_ERRNO; lia | exact S2 |
                                         fold b1; rewrite L1; unfold MD_SEND_ERRNO, MD_SIZE in *; lia].
  unfold s2, nk_send_errno, fld_u32, rdn. reflexivity.
Qed.

Lemma lf_mbs_mb_sock : md_socket_errno (lf_mbs_mb kbs mbs) = nk_socket_errno kbs.
Proof.
  destruct lf_mbs_mb_lens as (L1 & L2 & L3 & _). pose proof lf_mb_s1_len as S1. pose proof lf_mb_s2_len as S2.
  unfold md_socket_errno, fld_u32, lf_mbs_mb. fold s1 s2 b1 b2 b3.
  rewrite lf_rdn_upd_other; [| unfold MD_SOCKET_ERRNO; lia | lia
                              | rewrite L3, lf_z4_len; unfold MD_SIZE, MD_N_REQ in *; lia
                              | rewrite lf_z4_len; unfold MD_SOCKET_ERRNO, MD_N_REQ; lia].
  unfold b3. rewrite lf_rdn_upd_other; [| unfold MD_SOCKET_ERRNO; lia | lia
                                         | fold b2; rewrite L2, lf_z4_len; unfold MD_NEXT, MD_SIZE in *; lia
                                         | rewrite lf_z4_len; unfold MD_SOCKET_ERRNO, MD_NEXT; lia].
  unfold b2. rewrite lf_rdn_upd_other; [| unfold MD_SOCKET_ERRNO; lia | lia
                                         | fold b1; rewrite L1, S2; unfold MD_SEND_ERRNO, MD_SIZE in *; lia
                                         | rewrite S2; unfold MD_SOCKET_ERRNO, MD_SEND_ERRNO; lia].
  unfold b1. rewrite lf_rdn_upd_same4; [| unfold MD_SOCKET_ERRNO; lia | exact S1 |
                                         unfold MD_SOCKET_ERRNO, MD_SIZE in *; lia].
  unfold s1, nk_socket_errno, fld_u32, rdn. reflexivity.
Qed.

Lemma lf_mbs_mb_n_mark : md_n_mark (lf_mbs_mb kbs mbs) = md_n_mark mbs.
Proof.
  unfold md_n_mark, fld_u32, rdn. rewrite lf_mbs_mb_slice; [reflexivity | unfold MD_N_MARK; lia | lia |].
  unfold MD_N_MARK, MD_N_REQ; lia.
Qed.

Lemma lf_mbs_mb_mark_slice : forall j, 0 <= j < MARKS_MAX ->
  slice (lf_mbs_mb kbs mbs) (MD_MARK + MARK_LEN * j) MARK_LEN = slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN.
Proof.
  intros j Hj. apply lf_mbs_mb_slice; unfold MD_MARK, MARK_LEN, MD_N_REQ, MARKS_MAX in *; lia.
Qed.

Lemma lf_mbs_mb_marks : model_marks_wf mbs -> md_marks (lf_mbs_mb kbs mbs) = md_marks mbs.
Proof.
  intros (Hn & _). unfold md_marks. rewrite lf_mbs_mb_n_mark. apply map_ext_in. intros a Ha.
  apply in_seq in Ha. rewrite lf_mbs_mb_mark_slice; [reflexivity|]. lia.
Qed.

Lemma lf_mbs_mb_wf : model_wf mbs -> nlk_wf kbs -> model_wf (lf_mbs_mb kbs mbs).
Proof.
  intros (_ & _ & _ & _ & _ & (Hn & T)) HK.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hse & Hsd & _).
  unfold model_wf.
  rewrite lf_mbs_mb_n_req, lf_mbs_mb_next, lf_mbs_mb_sock, lf_mbs_mb_send.
  split; [unfold NL_SENT_MAX; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros j Hj; lia|].
  unfold model_marks_wf. rewrite lf_mbs_mb_n_mark. split; [exact Hn|].
  intros j Hj. rewrite lf_mbs_mb_mark_slice by (unfold MARKS_MAX in *; lia). exact (T j Hj).
Qed.

Lemma lf_mbs_mb_are : forall gbs, model_wf mbs -> marks_are gbs mbs -> marks_are gbs (lf_mbs_mb kbs mbs).
Proof.
  intros gbs (_ & _ & _ & _ & _ & MW) (E1 & E2). split.
  - rewrite lf_mbs_mb_n_mark. exact E1.
  - rewrite lf_mbs_mb_marks by exact MW. exact E2.
Qed.
End Mbs.

Lemma lf_mb_requests : forall kbs mbs, Z.of_nat (length kbs) = NK_SIZE -> Z.of_nat (length mbs) = MD_SIZE ->
  requests_are (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs).
Proof.
  intros kbs mbs KL ML. unfold requests_are.
  rewrite (lf_kbs_mb_n_sent kbs KL), (lf_mbs_mb_n_req kbs mbs KL ML).
  split; [reflexivity|]. intros i Hi. lia.
Qed.

(* ==========================================================================
   3. In memory
   ========================================================================== *)

Section mem.
Context {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).

(* a byte list under a store: off the stored range the memory reads as before *)
Lemma abytes_upd : forall (X : Z -> Prop) m m' a bs k xs,
  kagree SEGS X m m' -> (k + length xs <= length bs)%nat ->
  (forall i, (i < length bs)%nat -> X (a + Z.of_nat i) -> (k <= i < k + length xs)%nat) ->
  abytes SEGS m a bs -> abytes SEGS m' (a + Z.of_nat k) xs -> abytes SEGS m' a (lf_upd bs k xs).
Proof.
  intros X m m' a bs k xs HK Hk HX (H0 & H1 & H2) (_ & _ & H3).
  split; [exact H0|]. split; [rewrite lf_upd_length by exact Hk; exact H1|].
  intros i Hi. rewrite lf_upd_length in Hi by exact Hk. rewrite lf_upd_nth by exact Hk.
  destruct (Nat.leb_spec k i), (Nat.ltb_spec i (k + length xs)); cbn [andb].
  - rewrite <- (H3 (i - k)%nat) by lia. f_equal. lia.
  - rewrite (HK (a + Z.of_nat i)); [exact (H2 i Hi)|]. intros HXi. pose proof (HX i Hi HXi). lia.
  - rewrite (HK (a + Z.of_nat i)); [exact (H2 i Hi)|]. intros HXi. pose proof (HX i Hi HXi). lia.
  - rewrite (HK (a + Z.of_nat i)); [exact (H2 i Hi)|]. intros HXi. pose proof (HX i Hi HXi). lia.
Qed.

Lemma au8arr_upd : forall (X : Z -> Prop) m m' a bs k xs,
  kagree SEGS X m m' -> wcarry SEGS m m' a (Z.of_nat (length bs)) -> (k + length xs <= length bs)%nat ->
  (forall i, (i < length bs)%nat -> X (a + Z.of_nat i) -> (k <= i < k + length xs)%nat) ->
  au8arr SEGS m a bs -> abytes SEGS m' (a + Z.of_nat k) xs -> au8arr SEGS m' a (lf_upd bs k xs).
Proof.
  intros X m m' a bs k xs HK HW Hk HX (Hb & Hw) Hx. split.
  - exact (abytes_upd X m m' a bs k xs HK Hk HX Hb Hx).
  - rewrite lf_upd_length by exact Hk. exact (awrange_keep SEGS m m' a _ HW Hw).
Qed.

(* the bytes a 4-byte chunk of the runner holds, as abytes *)
Lemma abytes_of_word4 : forall m a (w : word) (bs : list byte), length bs = 4%nat ->
  w = Z_to_bv 64 (bytes_le_to_Z bs) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> mbyte SEGS m (a + i) = Some (byte_of_word w i)) ->
  abytes SEGS m a bs.
Proof.
  intros m a w bs Hl Hw H0 H1 H. split; [exact H0|]. split; [rewrite Hl; lia|].
  intros i Hi. rewrite (H (Z.of_nat i)) by lia. subst w.
  rewrite (YN3u.byte_of_word_le bs i) by lia. symmetry. apply nth_error_nth'. exact Hi.
Qed.

(* The five stores' ranges, which a run of model_begin may write besides bytes off the data *)
Definition lf_mb_rng (md a : Z) : Prop :=
  (md <= a < md + 12) \/ (md + MD_N_REQ <= a < md + MD_N_REQ + 4) \/
  (LA_G_NL + NK_N_SENT <= a < LA_G_NL + NK_N_SENT + 4).

(* a read-only byte lies below the image's top *)
Lemma lf_roP_bounds : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.
Proof.
  intros a [(s & Hs & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
    pose proof (pa_img_range a Hi) as R. unfold PcapImgEnd.pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
  - unfold PCAP_RLO, PCAP_RHI, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
Qed.

Lemma lf_roP_below_top : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> a < YImgTop.IMG_TOP.
Proof.
  intros a [(s & Hs & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
    pose proof (pa_img_range a Hi) as R. unfold PcapImgEnd.pcap_img_end in R. lia.
  - unfold PCAP_RLO, PCAP_RHI, YImgTop.IMG_TOP in *. lia.
Qed.

(* lf_data after model_begin. X is the run's exception set: inside the data's footprint it holds only the five
   stored ranges. *)
Lemma lf_data_mb : forall (X : Z -> Prop) m m' cx md mk kbs mbs gbs,
  pa_segs = tfibsegs ->
  kagree SEGS X m m' ->
  wcarry_on m m' (lf_data_fp_w md mk) ->
  (forall a, lf_data_fp md mk a -> X a -> lf_mb_rng md a) ->
  off_img md MD_SIZE -> off_img mk MK_SIZE -> apart md MD_SIZE mk MK_SIZE ->
  abytes SEGS m' (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4) ->
  abytes SEGS m' (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4) ->
  abytes SEGS m' (md + MD_NEXT) lf_z4 ->
  abytes SEGS m' (md + MD_N_REQ) lf_z4 ->
  abytes SEGS m' (LA_G_NL + NK_N_SENT) lf_z4 ->
  lf_data cx md mk kbs mbs gbs m ->
  lf_data cx md mk (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs) gbs m' /\
  nk_n_sent (lf_kbs_mb kbs) = 0 /\ md_n_req (lf_mbs_mb kbs mbs) = 0 /\
  nk_opened (lf_kbs_mb kbs) = nk_opened kbs /\ requests_are (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs).
Proof.
  intros X m m' cx md mk kbs mbs gbs HSEGS HK HW HX Hmdt Hmkt Hap A1 A2 A3 A4 A5
    (Hnl & Hwf & Hif & Ho & Hmi & Hoc & Hmd & Hmwf & Hmk & Hkwf & Hare & Hifp & Hgn & Hgw & Hodd & Htx & Hla).
  pose proof Hnl as (((Hnl0 & Hnl1 & Hnlb) & Hnlw) & KL). pose proof Hmd as (((Hmd0 & Hmd1 & Hmdb) & Hmdw) & ML).
  pose proof (lf_kbs_mb_fields kbs KL) as (Fn & Fo & Fod & Fc & Fmi & _).
  unfold lf_mb_rng in HX. unfold apart in Hap. unfold off_img in Hmdt, Hmkt.
  assert (CV : LA_G_NL = 6146752 /\ NK_SIZE = 271992 /\ LA_G_NAMES = 6486720 /\ G_NAMES_SIZE = 512 /\
               LA_LONG_ALIAS = 6487360 /\ MD_SIZE = 8856 /\ MK_SIZE = 516 /\ YImgTop.IMG_LO = 65536 /\
               YImgTop.IMG_TOP = 6635520 /\ MD_N_REQ = 8336 /\ NK_N_SENT = 271016)
    by (repeat split; reflexivity).
  assert (CT : LA_G_NL + NK_SIZE <= YImgTop.IMG_TOP /\ LA_G_NAMES + G_NAMES_SIZE <= YImgTop.IMG_TOP /\
               LA_LONG_ALIAS + 304 <= YImgTop.IMG_TOP)
    by (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS, YImgTop.IMG_TOP; lia).
  (* X inside each part of the data *)
  assert (XG : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> X a ->
                 LA_G_NL + NK_N_SENT <= a < LA_G_NL + NK_N_SENT + 4).
  { intros a Ha HXa. destruct (HX a ltac:(unfold lf_data_fp; left; exact Ha) HXa) as [H|[H|H]]; [| |exact H];
      unfold MD_N_REQ in *; lia. }
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a).
  { intros a Ha HXa. destruct (HX a ltac:(unfold lf_data_fp; right; left; exact Ha) HXa) as [H|[H|H]];
      unfold MD_N_REQ, NK_N_SENT, LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia. }
  assert (XL : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304 -> ~ X a).
  { intros a Ha HXa. destruct (HX a ltac:(unfold lf_data_fp; right; right; left; exact Ha) HXa) as [H|[H|H]];
      unfold MD_N_REQ, NK_N_SENT, LA_G_NL, LA_LONG_ALIAS in *; lia. }
  assert (XM : forall a, md <= a < md + MD_SIZE -> X a -> (md <= a < md + 12) \/ (md + MD_N_REQ <= a < md + MD_N_REQ + 4)).
  { intros a Ha HXa. destruct (HX a ltac:(unfold lf_data_fp; right; right; right; left; exact Ha) HXa) as [H|[H|H]];
      [left; exact H | right; exact H | unfold NK_N_SENT, LA_G_NL, NK_SIZE in *; lia]. }
  assert (XK : forall a, mk <= a < mk + MK_SIZE -> ~ X a).
  { intros a Ha HXa. destruct (HX a ltac:(unfold lf_data_fp; right; right; right; right; left; exact Ha) HXa)
      as [H|[H|H]]; unfold MD_N_REQ, MD_SIZE, MK_SIZE, NK_N_SENT, LA_G_NL, NK_SIZE in *; lia. }
  assert (XR : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a).
  { intros a Ha HXa. pose proof (lf_roP_bounds a Ha) as Hlo.
    destruct (HX a ltac:(unfold lf_data_fp; right; right; right; right; right; exact Ha) HXa) as [H|[H|H]];
      [unfold MD_N_REQ in *; lia | unfold MD_N_REQ in *; lia |].
    rewrite HSEGS in Ha. apply (LA_G_not_ro a); [|exact Ha]. apply inG_LA_G_NL.
    unfold NK_N_SENT in H. lia. }
  assert (XO : forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a).
  { intros a Ha. apply XR. right. unfold LA_ODD, PCAP_RLO, PCAP_RHI in *. lia. }
  assert (WS : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) -> wcarry SEGS m m' a n)
    by (intros a n Ha; exact (wcarry_on_sub m m' _ a n HW Ha)).
  (* the new g_nl *)
  assert (Hnl' : anlk_at SEGS m' LA_G_NL (lf_kbs_mb kbs)).
  { split; [|exact (lf_kbs_mb_len kbs KL)]. split.
    - pose proof A5 as (_ & _ & A5b). rewrite lf_z4_len in A5b.
      split; [unfold LA_G_NL; lia|]. split; [rewrite (lf_kbs_mb_len kbs KL); unfold LA_G_NL, NK_SIZE; lia|].
      intros i Hi. pose proof (lf_kbs_mb_len kbs KL) as KL'.
      assert (Hi' : Z.of_nat i < NK_SIZE) by lia.
      unfold lf_kbs_mb. rewrite lf_upd_nth by (rewrite lf_z4_len; unfold NK_N_SENT, NK_SIZE in *; lia).
      rewrite lf_z4_len.
      destruct (Nat.leb_spec (Z.to_nat NK_N_SENT) i), (Nat.ltb_spec i (Z.to_nat NK_N_SENT + 4)); cbn [andb].
      1: { rewrite <- (A5b (i - Z.to_nat NK_N_SENT)%nat) by lia. f_equal. unfold NK_N_SENT in *. lia. }
      all: rewrite (HK (LA_G_NL + Z.of_nat i)); [exact (Hnlb i ltac:(lia))|];
        intros HXa; pose proof (XG (LA_G_NL + Z.of_nat i) ltac:(lia) HXa); unfold NK_N_SENT in *; lia.
    - rewrite (lf_kbs_mb_len kbs KL).
      apply (awrange_keep SEGS m m' LA_G_NL NK_SIZE (WS LA_G_NL NK_SIZE ltac:(intros i Hi; unfold lf_data_fp_w; left; lia))).
      rewrite <- KL. exact Hnlw. }
  (* the new model *)
  assert (Hmd' : amodel_at SEGS m' md (lf_mbs_mb kbs mbs)).
  { pose proof (lf_mbs_mb_lens kbs mbs KL ML) as (L1 & L2 & L3 & L4).
    assert (S1 : length (slice kbs NK_SOCKET_ERRNO 4) = 4%nat)
      by (rewrite lf_slice_length; [reflexivity | | |]; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia).
    assert (S2 : length (slice kbs NK_SEND_ERRNO 4) = 4%nat)
      by (rewrite lf_slice_length; [reflexivity | | |]; unfold NK_SEND_ERRNO, NK_SIZE in *; lia).
    split; [|exact (lf_mbs_mb_len kbs mbs KL ML)]. split.
    - pose proof A1 as (_ & _ & A1b). pose proof A2 as (_ & _ & A2b).
      pose proof A3 as (_ & _ & A3b). pose proof A4 as (_ & _ & A4b).
      rewrite S1 in A1b. rewrite S2 in A2b. change (length lf_z4) with 4%nat in A3b, A4b.
      split; [lia|]. split; [rewrite L4; lia|].
      intros i Hi. rewrite L4 in Hi.
      unfold lf_mbs_mb. rewrite lf_upd_nth by (rewrite ?L3, ?lf_z4_len; unfold MD_N_REQ, MD_SIZE in *; lia).
      rewrite lf_z4_len.
      destruct (Nat.leb_spec (Z.to_nat MD_N_REQ) i), (Nat.ltb_spec i (Z.to_nat MD_N_REQ + 4)); cbn [andb].
      1: { rewrite <- (A4b (i - Z.to_nat MD_N_REQ)%nat) by lia. f_equal. unfold MD_N_REQ in *. lia. }
      all: rewrite lf_upd_nth by (rewrite ?L2, ?lf_z4_len; unfold MD_NEXT, MD_SIZE in *; lia); rewrite lf_z4_len;
        destruct (Nat.leb_spec (Z.to_nat MD_NEXT) i), (Nat.ltb_spec i (Z.to_nat MD_NEXT + 4)); cbn [andb];
        try (rewrite <- (A3b (i - Z.to_nat MD_NEXT)%nat) by lia; f_equal; unfold MD_NEXT in *; lia);
        rewrite lf_upd_nth by (rewrite ?L1, ?S2; unfold MD_SEND_ERRNO, MD_SIZE in *; lia); rewrite S2;
        destruct (Nat.leb_spec (Z.to_nat MD_SEND_ERRNO) i), (Nat.ltb_spec i (Z.to_nat MD_SEND_ERRNO + 4)); cbn [andb];
        try (rewrite <- (A2b (i - Z.to_nat MD_SEND_ERRNO)%nat) by lia; f_equal; unfold MD_SEND_ERRNO in *; lia);
        rewrite lf_upd_nth by (rewrite ?S1; unfold MD_SOCKET_ERRNO, MD_SIZE in *; lia); rewrite S1;
        destruct (Nat.leb_spec (Z.to_nat MD_SOCKET_ERRNO) i), (Nat.ltb_spec i (Z.to_nat MD_SOCKET_ERRNO + 4)); cbn [andb];
        try (rewrite <- (A1b (i - Z.to_nat MD_SOCKET_ERRNO)%nat) by lia; f_equal; unfold MD_SOCKET_ERRNO in *; lia);
        (rewrite (HK (md + Z.of_nat i)); [exact (Hmdb i ltac:(unfold MD_SIZE in *; lia))|];
         intros HXa; destruct (XM (md + Z.of_nat i) ltac:(unfold MD_SIZE in *; lia) HXa);
         unfold MD_SOCKET_ERRNO, MD_SEND_ERRNO, MD_NEXT, MD_N_REQ in *; lia).
    - rewrite L4, ML.
      apply (awrange_keep SEGS m m' md MD_SIZE
        (WS md MD_SIZE ltac:(intros i Hi; unfold lf_data_fp_w; right; right; right; left; lia))).
      rewrite <- ML. exact Hmdw. }
  (* the parts no store touches *)
  assert (Hodd' : lf_odd_at m') by exact (lf_odd_at_keep X m m' HK XR Hodd).
  assert (Htx' : lf_texts_at m') by exact (lf_texts_at_keep X m m' HK XR Htx).
  assert (XGi : forall a, LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE -> ~ X a).
  { intros a Ha HXa. pose proof (XG a ltac:(unfold NK_IF_NAME, NK_SIZE in *; lia) HXa).
    unfold NK_IF_NAME, NK_N_SENT in *. lia. }
  assert (Hifp' : lf_ifp m' 64).
  { intros e He. destruct (Hifp e He) as (q & Hq & H1 & H2). exists q.
    split; [|split; [exact H1|]].
    - apply (au64_keep SEGS X m m' _ q HK); [|exact Hq]. intros k Hk. apply XGi. unfold NK_IF_NAME, NK_SIZE. lia.
    - intros He60. apply (au64_keep SEGS X m m' _ q HK); [|exact (H2 He60)]. intros k Hk. apply XO. lia. }
  assert (Hif' : aiftab_at SEGS m' LA_G_NL (lf_kbs_mb kbs) lf_tab).
  { destruct Hif as (Hn & H80 & Ht). split; [rewrite Fn; exact Hn|]. split; [exact H80|].
    intros i nm ix Hi. destruct (Ht i nm ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
    destruct (lf_tab_entry i nm ix Hi) as (H64 & Hlt & Hge).
    assert (Hp' : au64_at SEGS m' (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
    { apply (au64_keep SEGS X m m' _ p HK); [|exact Hp]. intros k Hk. apply XGi. unfold NK_IF_NAME, NK_SIZE. lia. }
    split; [exact Hix|]. exists p. split; [exact Hp'|]. split; [exact Hp0|].
    split; [|apply (au32_keep SEGS X m m' _ ix HK); [|exact Hx]; intros k Hk; apply XGi;
             unfold NK_IF_INDEX, NK_IF_NAME, NK_SIZE; lia].
    pose proof Hs as ((Hpa & Hpb & _) & _). rewrite length_app in Hpb. cbn [length] in Hpb.
    destruct (Nat.lt_ge_cases i 60) as [Hi60 | Hi60].
    - destruct (Hifp (Z.of_nat i) ltac:(lia)) as (q & Hq & Hq1 & _).
      pose proof (val_mem8_mod SEGS m _ p q Hp Hq) as Epq. rewrite (Hq1 ltac:(lia)) in Epq.
      pose proof (Hlt Hi60) as Hlen. assert (Hd : 0 <= Z.of_nat i / 15 <= 3) by lia.
      rewrite (Z.mod_small p) in Epq by lia. rewrite Z.mod_small in Epq by (unfold LA_G_NAMES; lia).
      apply (acstr_keep SEGS X m m' p nm HK); [|exact Hs]. intros j Hj. apply XN. unfold G_NAMES_SIZE. lia.
    - pose proof (Hge Hi60) as Hnm.
      destruct (Hodd' (i - 59)%nat ltac:(lia)) as (q' & Hq' & _ & Hs' & _).
      destruct (Hifp' (Z.of_nat i) ltac:(lia)) as (q & Hq & _ & Hq2).
      pose proof (val_mem8_mod SEGS m' _ p q Hp' Hq) as Epq.
      assert (Eq : q mod 2 ^ 64 = q' mod 2 ^ 64).
      { apply (val_mem8_mod SEGS m' (LA_ODD + 8 * Z.of_nat (i - 59))); [|exact Hq'].
        replace (Z.of_nat (i - 59)) with (Z.of_nat i - 59) by lia. exact (Hq2 ltac:(lia)). }
      pose proof Hs' as ((Hqa & Hqb & _) & _). rewrite length_app in Hqb. cbn [length] in Hqb.
      rewrite (Z.mod_small p) in Epq by lia. rewrite (Z.mod_small q') in Eq by lia.
      assert (Ep : p = q') by (rewrite Epq; exact Eq).
      rewrite Ep, Hnm. exact Hs'. }
  assert (Hmk' : amarks_at SEGS m' mk gbs).
  { apply (amarks_keep SEGS X m m' _ gbs HK); [|intros i Hi; apply XK; lia | exact Hmk].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; right. lia. }
  assert (Hgw' : lf_gnames_w m').
  { apply (lf_gnames_w_keep X m m' HK); [|exact XN | exact Hgw].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; left. unfold G_NAMES_SIZE in *. lia. }
  assert (Hla' : lf_la_at m').
  { apply (lf_la_at_keep X m m' HK); [|exact XL | exact Hla].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; left. lia. }
  split.
  - exact (conj Hnl' (conj (lf_kbs_mb_wf kbs KL Hwf) (conj Hif' (conj (eq_trans Fo Ho) (conj (eq_trans Fmi Hmi)
      (conj (eq_trans Fod (eq_trans Hoc (eq_sym Fc))) (conj Hmd' (conj (lf_mbs_mb_wf kbs mbs KL ML Hmwf Hwf)
      (conj Hmk' (conj Hkwf (conj (lf_mbs_mb_are kbs mbs KL ML gbs Hmwf Hare) (conj Hifp'
      (conj (lf_gnames_at_keep X m m' 64 HK ltac:(lia) XN Hgn) (conj Hgw' (conj Hodd' (conj Htx' Hla')))))))))))))))).
  - split; [exact (lf_kbs_mb_n_sent kbs KL)|]. split; [exact (lf_mbs_mb_n_req kbs mbs KL ML)|].
    split; [exact Fod | exact (lf_mb_requests kbs mbs KL ML)].
Qed.
End mem.
