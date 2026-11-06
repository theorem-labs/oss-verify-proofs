(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 330 of its 385 lines of code are new or changed and 1250 lines of the source are left out. *)
(* reac_link_alias_write on image A, the SEND piece (lib/A/Prog/reac_link_alias_writeSend.v): its byte algebra,
   with no symbolic engine and no journal. The request as the code leaves it in the frame (+0x1f4..+0x2e4) is
   link_spec.v's `req_write`; the result of the send arm is `write_lib`'s talk arm; and the Post's fields at the
   EXIT cut (`aw_pf` of reac_link_alias_writeDefs.v) come from nl_talk's Post. The uniqueness and transport lemmas
   are adapted from reac_link_alias_read's ArPost.v (now lib/A/Prog/reac_link_alias_readPost.v), the
   request lemma from the plain walk's `req_bytes` (lib/Prog/reac_link_alias_write.v).

   Proves no function (kind: segment lemma of reac_link_alias_write's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide reac_link_alias_writeDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Bytes of a value, and lists of bytes in memory
   ========================================================================== *)

Lemma aws_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma aws_le_byte_shiftr : forall v (n k : nat), (k < n)%nat ->
  Z_to_bv 8 (le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v n k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, le_byte.
  change (2 ^ Z.of_N 8) with (2 ^ 8). change 256 with (2 ^ 8).
  rewrite Z.mod_mod by lia.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* two byte lists with the same values are equal (plain walk's bl_ext) *)
Lemma aws_bl_ext : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* the word 0x50010 the code stores at req + 4: type RTM_NEWLINK, flags NLM_F_REQUEST | NLM_F_ACK *)
Lemma aws_hdr_split : Z_to_le_bytes 4 327696 = Z_to_le_bytes 2 RTM_NEWLINK ++ Z_to_le_bytes 2 (F_REQUEST + F_ACK).
Proof. apply aws_bl_ext. vm_compute. reflexivity. Qed.

Lemma aws_land_508 : forall x, 0 <= x < 512 -> Z.land x 508 = 4 * (x / 4).
Proof.
  intros x Hx.
  assert (H : forallb (fun k => Z.eqb (Z.land (Z.of_nat k) 508) (4 * (Z.of_nat k / 4))) (seq 0 512) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat x)).
  rewrite in_seq, Z2Nat.id in H by lia. apply Z.eqb_eq, H. lia.
Qed.

Section s.
Variable segs : list Segment.

Lemma aws_abytes_cat : forall m a b l1 l2,
  abytes segs m a l1 -> b = a + Z.of_nat (length l1) -> abytes segs m b l2 -> abytes segs m a (l1 ++ l2).
Proof.
  intros m a b l1 l2 (H0 & H1 & H2) -> (H3 & H4 & H5). split; [exact H0|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length l1)) as [Hl | Hl].
  - rewrite nth_error_app1 by exact Hl. exact (H2 i Hl).
  - rewrite nth_error_app2 by exact Hl. specialize (H5 (i - length l1)%nat ltac:(lia)).
    replace (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) with (a + Z.of_nat i) in H5 by lia. exact H5.
Qed.

Lemma aws_abytes_le : forall m a (n : nat) v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem segs m a n v -> abytes segs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v H0 H1 Hv. split; [exact H0|]. split; [rewrite length_Z_to_le_bytes; exact H1|].
  intros i Hi. rewrite length_Z_to_le_bytes in Hi. rewrite (Hv i Hi), aws_nth_le_bytes by exact Hi.
  f_equal. apply aws_le_byte_shiftr. exact Hi.
Qed.

Lemma aws_abytes_zeros : forall m a n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> mbyte segs m (a + i) = Some (zb 0)) -> abytes segs m a (zeros n).
Proof.
  intros m a n H0 H1 Hn Hz. unfold zeros. split; [exact H0|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi. apply Hz. lia.
Qed.

Lemma aws_req_write_length : forall idx (sa : list byte),
  Z.of_nat (length (req_write idx sa)) = 32 + nl_align (RTA_HDR + Z.of_nat (length sa)).
Proof.
  intros idx sa. unfold req_write, zeros. cbv zeta.
  rewrite !length_app, !length_Z_to_le_bytes, !repeat_length.
  unfold nl_align, RTA_HDR. lia.
Qed.

(* THE REQUEST, as the code leaves it at req = F + 32 (+0x2a0..+0x2e4 the header words, checked_memset's zeros,
   checked_memcpy's alias): the bytes link_spec.v's req_write names (the plain walk's req_bytes, on image A). *)
Lemma aws_req_bytes : forall (m : word -> option byte) req idx (sa : list byte),
  0 <= req -> req + 292 <= 2 ^ 64 -> Z.of_nat (length sa) < 256 ->
  val_mem segs m req 4 (32 + nl_align (RTA_HDR + Z.of_nat (length sa))) ->
  val_mem segs m (req + 4) 4 327696 ->
  val_mem segs m (req + 8) 4 1 ->
  (forall i, 12 <= i < 20 -> mbyte segs m (req + i) = Some (zb 0)) ->
  val_mem segs m (req + 20) 4 idx ->
  (forall i, 24 <= i < 32 -> mbyte segs m (req + i) = Some (zb 0)) ->
  val_mem segs m (req + 32) 2 (Z.of_nat (length sa) + 4) ->
  val_mem segs m (req + 34) 2 20 ->
  (forall i, (i < length sa)%nat -> mbyte segs m (req + 36 + Z.of_nat i) = nth_error sa i) ->
  (forall i, 36 + Z.of_nat (length sa) <= i < 32 + nl_align (RTA_HDR + Z.of_nat (length sa)) ->
     mbyte segs m (req + i) = Some (zb 0)) ->
  abytes segs m req (req_write idx sa).
Proof.
  intros m req idx sa H0 H1 HL V0 V4 V8 Z12 V20 Z24 V32 V34 VA ZT.
  assert (NA : nl_align (RTA_HDR + Z.of_nat (length sa)) <= 260 /\
               RTA_HDR + Z.of_nat (length sa) <= nl_align (RTA_HDR + Z.of_nat (length sa)))
    by (unfold nl_align, RTA_HDR; lia).
  unfold req_write. cbv zeta.
  apply (aws_abytes_cat m req (req + 4)); [apply aws_abytes_le; [lia | lia | exact V0] | rewrite length_Z_to_le_bytes; lia |].
  rewrite (app_assoc (Z_to_le_bytes 2 RTM_NEWLINK)), <- aws_hdr_split.
  apply (aws_abytes_cat m (req + 4) (req + 8)); [apply aws_abytes_le; [lia | lia | exact V4] | rewrite length_Z_to_le_bytes; lia |].
  apply (aws_abytes_cat m (req + 8) (req + 12)); [apply aws_abytes_le; [lia | lia | exact V8] | rewrite length_Z_to_le_bytes; lia |].
  apply (aws_abytes_cat m (req + 12) (req + 16));
    [apply aws_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 12 + i) with (req + (12 + i)) by ring; apply Z12; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (aws_abytes_cat m (req + 16) (req + 20));
    [apply aws_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 16 + i) with (req + (16 + i)) by ring; apply Z12; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (aws_abytes_cat m (req + 20) (req + 24)); [apply aws_abytes_le; [lia | lia | exact V20] | rewrite length_Z_to_le_bytes; lia |].
  apply (aws_abytes_cat m (req + 24) (req + 32));
    [apply aws_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 24 + i) with (req + (24 + i)) by ring; apply Z24; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (aws_abytes_cat m (req + 32) (req + 34));
    [apply aws_abytes_le; [lia | lia |]; replace (RTA_HDR + Z.of_nat (length sa)) with (Z.of_nat (length sa) + 4)
       by (unfold RTA_HDR; ring); exact V32
    | rewrite length_Z_to_le_bytes; lia |].
  apply (aws_abytes_cat m (req + 34) (req + 36)); [apply aws_abytes_le; [lia | lia | exact V34] | rewrite length_Z_to_le_bytes; lia |].
  apply (aws_abytes_cat m (req + 36) (req + 36 + Z.of_nat (length sa))).
  - split; [lia|]. split; [lia|]. exact VA.
  - reflexivity.
  - apply aws_abytes_zeros; [lia | unfold RTA_HDR in *; lia | unfold RTA_HDR in *; lia |].
    intros i Hi. replace (req + 36 + Z.of_nat (length sa) + i) with (req + (36 + Z.of_nat (length sa) + i)) by ring.
    apply ZT. unfold RTA_HDR in *. lia.
Qed.

(* ==========================================================================
   2. Uniqueness and transport of the A views (ArPost.v sections 1-2)
   ========================================================================== *)

Lemma aws_lb_inj : forall (n : nat) (p1 p2 : Z),
  (forall k, (k < n)%nat ->
     Z_to_bv 8 (Z.shiftr (p1 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256) =
     Z_to_bv 8 (Z.shiftr (p2 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256)) ->
  p1 mod 2 ^ (8 * Z.of_nat n) = p2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n p1 p2 H. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat n)) as [Hl|Hl].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hr.
    set (q := i / 8) in *. set (r := i mod 8) in *. clearbody q r.
    assert (Hq : 0 <= q) by lia.
    assert (Hk : (Z.to_nat q < n)%nat) by lia.
    specialize (H (Z.to_nat q) Hk).
    apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
    change (bv_modulus 8) with 256 in H. rewrite !Z.mod_mod in H by lia.
    rewrite Z2Nat.id in H by exact Hq.
    apply (f_equal (fun z => Z.testbit z r)) in H. cbv beta in H.
    change 256 with (2 ^ 8) in H. rewrite !Z.mod_pow2_bits_low in H by lia.
    rewrite !Z.shiftr_spec in H by lia.
    replace (r + 8 * q) with i in H by lia. exact H.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma aws_vm_unique : forall m a (n : nat) v1 v2, val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2. apply aws_lb_inj. intros k Hk.
  pose proof (eq_trans (eq_sym (H1 k Hk)) (H2 k Hk)) as E.
  exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E).
Qed.

Lemma aws_abytes_unique : forall m a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma aws_acstr_short : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 ->
  (length s1 < length s2)%nat -> False.
Proof.
  intros m a s1 s2 [(_ & _ & B1) _] [(_ & _ & B2) N2] L.
  assert (E1 : mbyte segs m (a + Z.of_nat (length s1)) = Some (zb 0)).
  { rewrite (B1 (length s1)) by (rewrite length_app; cbn [length]; lia).
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (E2 : mbyte segs m (a + Z.of_nat (length s1)) = nth_error s2 (length s1)).
  { rewrite (B2 (length s1)) by (rewrite length_app; cbn [length]; lia).
    apply nth_error_app1. exact L. }
  apply N2. apply (nth_error_In s2 (length s1)). rewrite <- E2. exact E1.
Qed.

Lemma aws_acstr_unique : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  destruct (Nat.lt_trichotomy (length s1) (length s2)) as [L|[L|L]].
  - exfalso. exact (aws_acstr_short m a s1 s2 H1 H2 L).
  - destruct H1 as [B1 _]. destruct H2 as [B2 _].
    apply (app_inv_tail [zb 0]). apply (aws_abytes_unique m a); [exact B1 | exact B2 |].
    rewrite !length_app, L. reflexivity.
  - exfalso. exact (aws_acstr_short m a s2 s1 H2 H1 L).
Qed.

Lemma aws_anlk_unique : forall m g b1 b2, anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (aws_abytes_unique m g); [exact B1 | exact B2 | lia].
Qed.

Lemma aws_au64_unique : forall m a p1 p2, au64_at segs m a p1 -> au64_at segs m a p2 ->
  p1 mod 2 ^ 64 = p2 mod 2 ^ 64.
Proof.
  intros m a p1 p2 H1 H2. pose proof (aws_vm_unique m a 8 p1 p2 H1 H2) as E.
  change (8 * Z.of_nat 8) with 64 in E. exact E.
Qed.

Lemma aws_au32_small_unique : forall m a x1 x2, au32_at segs m a x1 -> au32_at segs m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. pose proof (aws_vm_unique m a 4 x1 x2 H1 H2) as E.
  change (8 * Z.of_nat 4) with 32 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma aws_acstr_range : forall m p s, acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s [(Ha & Hl & _) _]. rewrite length_app in Hl. cbn [length] in Hl. lia.
Qed.

Lemma aws_aiftab_unique : forall m bs tab1 tab2,
  aiftab_at segs m LA_G_NL bs tab1 -> aiftab_at segs m LA_G_NL bs tab2 -> tab1 = tab2.
Proof.
  intros m bs tab1 tab2 (L1 & _ & E1) (L2 & _ & E2).
  assert (L : length tab1 = length tab2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error tab1 i) as [[n1 x1]|] eqn:H1; destruct (nth_error tab2 i) as [[n2 x2]|] eqn:H2.
  - destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (aws_au64_unique _ _ _ _ P1 P2) as Ep.
    pose proof (aws_acstr_range _ _ _ C1). pose proof (aws_acstr_range _ _ _ C2).
    rewrite !Z.mod_small in Ep by lia. subst p2.
    rewrite (aws_acstr_unique _ _ _ _ C1 C2).
    rewrite (aws_au32_small_unique _ _ _ _ I1 I2 R1 R2). reflexivity.
  - exfalso. apply nth_error_None in H2. assert (i < length tab1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in H1. assert (i < length tab2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

Lemma aws_astr_arg_unique : forall m a o1 o2, astr_arg segs m a o1 -> astr_arg segs m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|] H1 H2; cbn [astr_arg] in H1, H2.
  - f_equal. exact (aws_acstr_unique m a s1 s2 (proj2 H1) (proj2 H2)).
  - destruct H1 as [Hn _]. contradiction.
  - destruct H2 as [Hn _]. contradiction.
  - reflexivity.
Qed.

Lemma aws_abytes_move : forall (m m' : word -> option byte) a bs,
  abytes segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) Hk. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma aws_acstr_move : forall m m' p s, acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) -> acstr_at segs m' p s.
Proof.
  intros m m' p s [B N] Hk. split; [|exact N]. apply (aws_abytes_move m m' p _ B).
  intros x Hx. apply Hk. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma aws_au8arr_move : forall m m' a bs, au8arr segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> writable_at segs m' x) -> au8arr segs m' a bs.
Proof.
  intros m m' a bs [B R] Hk Hw. split; [exact (aws_abytes_move m m' a bs B Hk)|].
  intros i Hi. apply Hw. lia.
Qed.

Lemma aws_anlk_move : forall m m' bs, anlk_at segs m LA_G_NL bs ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> writable_at segs m' x) -> anlk_at segs m' LA_G_NL bs.
Proof.
  intros m m' bs [U L] Hk Hw. split; [|exact L].
  apply (aws_au8arr_move m m' LA_G_NL bs U); intros x Hx; [apply Hk | apply Hw]; lia.
Qed.

Lemma aws_aiftab_keep : forall m m' bs bs' tab,
  aiftab_at segs m LA_G_NL bs tab -> nk_n_if bs' = nk_n_if bs ->
  (forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_IF_NAME + 8 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL + NK_IF_INDEX <= x < LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' LA_G_NL bs' tab.
Proof.
  intros m m' bs bs' tab (L & L80 & E) Hn DN DI DS.
  split; [rewrite Hn; exact L|]. split; [exact L80|]. intros i n2 ix Hi.
  destruct (E i n2 ix Hi) as (R & p & P & Pz & C & I). split; [exact R|].
  assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  exists p. split; [|split; [exact Pz|split]].
  - unfold au64_at, val_mem in *. intros k Hk.
    rewrite (DN (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i + Z.of_nat k)) by lia. exact (P k Hk).
  - pose proof (aws_acstr_range m p n2 C) as Rp.
    apply (aws_acstr_move m m' p n2 C). exact (DS i n2 ix p Hi P ltac:(lia)).
  - unfold au32_at, val_mem in *. intros k Hk.
    rewrite (DI (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i + Z.of_nat k)) by lia. exact (I k Hk).
Qed.

(* a word read is the read it was when its eight bytes did not change *)
Lemma aws_rdword_eq : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H.
  assert (E0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  unfold rdword. rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* the read-only image facts are the facts they were when every read-only byte did not change *)
Lemma aws_arodata_eq : forall rlo rhi B (rd rd' : reader),
  arodata_okP segs rlo rhi B rd -> (forall a, in_roP segs rlo rhi a -> rd' a = rd a) ->
  arodata_okP segs rlo rhi B rd'.
Proof. intros rlo rhi B rd rd' H Hk a Hro Ho He. rewrite (Hk a Hro). exact (H a Hro Ho He). Qed.

(* the request's shadow, as the code sets it at +0x1f8..+0x28c (s2 + 4 .. s2 + 0x27 := 0, s2 + 0x28 := 4): every
   byte of [F + 32, F + 324) is addressable *)
Lemma aws_req_ra : forall (rd : reader) F lo n, F mod 8 = 0 -> 0 <= F ->
  (forall j, 4 <= j < 40 -> rd (SHADOW_OFF + F / 8 + j) = Some 0) -> rd (SHADOW_OFF + F / 8 + 40) = Some 4 ->
  F + 32 <= lo -> lo + n <= F + 324 -> range_addressable rd SHADOW_OFF lo n.
Proof.
  intros rd F lo n HF8 HF0 HZ H4 Hlo Hhi x Hx. unfold shadow_of_addr.
  assert (Ex : x / 8 = F / 8 + (x - F) / 8) by lia.
  rewrite Ex. replace (SHADOW_OFF + (F / 8 + (x - F) / 8)) with (SHADOW_OFF + F / 8 + (x - F) / 8) by lia.
  destruct (Z_lt_le_dec x (F + 320)) as [Hl | Hl].
  - exists 0. split; [apply HZ; lia | left; reflexivity].
  - assert (E40 : (x - F) / 8 = 40) by lia. rewrite E40. exists 4. split; [exact H4|].
    right. unfold saddr_ok. split; [|lia].
    pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF. lia.
Qed.
End s.

(* ==========================================================================
   3. The send arm of write_lib, and the Post's fields at the EXIT cut
   ========================================================================== *)

Lemma aws_talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; reflexivity.
Qed.

Lemma aws_write_lib_talk : forall tab sn sa reqs K,
  sn <> [] -> Z.of_nat (length sa) < ALIAS_MAX -> index_of tab sn <> 0 ->
  write_lib tab (Some sn) (Some sa) reqs K =
    Wres (talk_rc_lib K) (if talk_owes K then owe reqs (req_write (index_of tab sn) sa) else reqs) (talk_after K).
Proof.
  intros tab sn sa reqs K Hs Ha Hi. unfold write_lib, write_core.
  destruct sn as [|b sn']; [exfalso; exact (Hs eq_refl)|].
  cbn [length Nat.eqb]. rewrite (proj2 (Z.leb_gt ALIAS_MAX (Z.of_nat (length sa))) Ha). cbv zeta.
  rewrite (proj2 (Z.eqb_neq (index_of tab (b :: sn')) 0) Hi). reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).

(* THE POST'S FIELDS at the EXIT cut on the send arm: rc is nl_talk's code, and the kernel's bytes at the cut are
   the ones nl_talk's Post gives (with the request req_write) and the interface table the read set kept. *)
Lemma aws_pf_talk : forall (cx : awcx) (W' : world SEGS) m kbs tab sn sa,
  anlk_at SEGS (aw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab ->
  acstr_at SEGS (aw_m0 cx) (aw_name cx) sn -> aw_name cx <> 0 -> sn <> [] ->
  acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa -> aw_alias cx <> 0 -> Z.of_nat (length sa) < ALIAS_MAX ->
  index_of tab sn <> 0 ->
  (exists kbs', anlk_at SEGS (mrestrict (w_H W') m) LA_G_NL kbs' /\ nlk_wf kbs'
     /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
     /\ nk_n_if kbs' = nk_n_if kbs
     /\ aiftab_at SEGS (mrestrict (w_H W') m) LA_G_NL kbs' tab
     /\ nk_socket_errno kbs' = 0
     /\ nk_send_errno kbs' = k_send (talk_after (nk_kstate kbs))
     /\ nk_next kbs' = Z.of_nat (k_next (talk_after (nk_kstate kbs)))
     /\ nk_sent kbs' = (if talk_owes (nk_kstate kbs)
                        then owe (nk_sent kbs) (req_write (index_of tab sn) sa) else nk_sent kbs)
     /\ nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs'))
     /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
     /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
     /\ (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs)
     /\ (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1)) ->
  aw_pf cx (talk_rc_lib (nk_kstate kbs)) W' m.
Proof.
  intros cx W' m kbs tab sn sa NK IT SN Hn0 Sne SA Ha0 HL Inz NL.
  intros kbs2 tab2 nm2 al2 NK2 IT2 SN2 SA2.
  assert (kbs2 = kbs) by exact (aws_anlk_unique _ _ _ _ _ NK2 NK). subst kbs2.
  assert (tab2 = tab) by exact (aws_aiftab_unique _ _ _ _ _ IT2 IT). subst tab2.
  assert (nm2 = Some sn) by (apply (aws_astr_arg_unique _ _ _ _ _ SN2); split; [exact Hn0 | exact SN]). subst nm2.
  assert (al2 = Some sa) by (apply (aws_astr_arg_unique _ _ _ _ _ SA2); split; [exact Ha0 | exact SA]). subst al2.
  cbv zeta. rewrite (aws_write_lib_talk tab sn sa (nk_sent kbs) (nk_kstate kbs) Sne HL Inz).
  cbn [w_rc w_reqs w_state].
  split; [reflexivity|].
  destruct NL as (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
  exists kbs'. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
  split; [exact N5|]. split; [exact N6|]. split; [exact N9|].
  split; [rewrite aws_talk_after_sock; exact N7|]. split; [exact N8|]. split; [exact N10|].
  split; [rewrite N11, N10; reflexivity|]. split; [exact N12|]. split; [exact N13|]. split; [exact N14|].
  split; [destruct (Z.eq_dec (nk_socket_errno kbs) 0) as [E|E]; [rewrite (N16 E) | rewrite (N15 E)]; lia|].
  intros [H|[H|[H|[H|H]]]].
  - discriminate H.
  - discriminate H.
  - injection H as H. exfalso. exact (Sne H).
  - exfalso. specialize (H sa eq_refl). lia.
  - exfalso. exact (Inz (H sn eq_refl)).
Qed.
End p.

About aws_req_bytes. About aws_pf_talk.
