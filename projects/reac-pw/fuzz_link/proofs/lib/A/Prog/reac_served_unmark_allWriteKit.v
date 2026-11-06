(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 261 of its 313 lines of code are new or changed and 1253 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all = 0x7d08) on image A: the
   kit of the WRITE piece (lib/A/Prog/reac_served_unmark_allWrite.v, `um_write`), with no symbolic engine and no
   journal, in a file of its own so that the other pieces of the walk can use it:
   - image computations over tfibsegs and the start-up static table (a walk at pa_segs reaches them through
     `pa_segs = tfibsegs`): .str.7 at LA_S_EMPTY = 0x214e0 and the seven bytes after its NUL lie in a non-writable
     segment; the NUL itself is not an owned static (the seven bytes after it are: its redzone, Tfib_owned_static's
     row (0x214e1, 0x1f)), and the seven bytes are bytes of the image's file, so every memory shows them (strlen's
     slack); every address of [0xa1000, 0x654000) (errno, g_nl) is writable at every memory (AB1h.v);
   - C strings, byte lists, words, g_nl and its interface table in the A views: uniqueness and transport;
   - the C string of slot i of a marks block (marks_wf), and its place among mk_names;
   - sub-ranges of range_addressable / shadow_hull_vis / amem_range;
   - link_spec's fake-kernel state across write_core (the plain walk's nk_kstate_eq / write_state_ce).

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AB1h AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YP08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Image computations
   ========================================================================== *)

(* .str.7 and the seven bytes after its NUL lie in one non-writable segment of image A *)
Lemma uw_empty_seg_b :
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? LA_S_EMPTY) &&
    (LA_S_EMPTY + 8 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) AB1v.tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma uw_empty_ro : forall a, LA_S_EMPTY <= a < LA_S_EMPTY + 8 ->
  in_roP AB1v.tfibsegs PCAP_RLO PCAP_RHI a /\ in_img AB1v.tfibsegs a.
Proof.
  intros a Ha. destruct (proj1 (existsb_exists _ _) uw_empty_seg_b) as (s & Hin & H).
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  split.
  - left. exists s. split; [exact Hin|]. split; [exact H1 | lia].
  - exists s. split; [exact Hin | lia].
Qed.

(* .str.7's byte (its NUL) meets no runtime static of image A's certificate tables (the seven bytes after it are
   its redzone, an owned static: Tfib_owned_static's row (0x214e1, 0x1f)) *)
Lemma uw_empty_static_b :
  forallb (fun r => (fst r + snd r <=? LA_S_EMPTY) || (LA_S_EMPTY + 1 <=? fst r)) AF0m.Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma uw_empty_not_static : ~ Exists (in_zr LA_S_EMPTY) AF0m.Tfib_owned_static.
Proof.
  intros HE. apply Exists_exists in HE as (r & Hr & Hz).
  pose proof (proj1 (forallb_forall _ _) uw_empty_static_b r Hr) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb. unfold in_zr in Hz.
  destruct Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* the seven bytes after .str.7's NUL (strlen's slack) are bytes of the image's file, so every memory shows them *)
Lemma uw_slack_rom_b : YP08.zallb (YP08.img_byte_ok AB1v.tfibsegs) (LA_S_EMPTY + 1) 7 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma uw_slack_readable : forall segs (m : word -> option byte) a, segs = AB1v.tfibsegs ->
  LA_S_EMPTY + 1 <= a < LA_S_EMPTY + 8 -> exists b, mbyte segs m a = Some b.
Proof.
  intros segs m a -> Ha. pose proof (YP08.zallb_sound _ 7 _ a uw_slack_rom_b ltac:(lia)) as H.
  unfold YP08.img_byte_ok, img_byte in H. unfold mbyte.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
  destruct (seg_rom AB1v.tfibsegs (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | discriminate H].
Qed.

(* an address of [0xa1000, 0x654000) is writable at every memory of image A (errno, g_nl) *)
Lemma uw_rw_window : forall (m : word -> option byte) a, 0xa1000 <= a < 0x654000 ->
  writable_at AB1v.tfibsegs m a.
Proof.
  intros m a Ha. unfold writable_at. rewrite <- AB1h.tsegs_tfasegs. apply AB1h.tfib_rw_window.
  rewrite unsigned_lit_small by lia. lia.
Qed.

(* ==========================================================================
   2. Bytes, C strings and words of the A views
   ========================================================================== *)

Lemma uw_byte_zero : forall b : byte, bv_unsigned b = 0 -> b = zb 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma uw_nth_firstn : forall {A} (l : list A) n i,
  nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i]; cbn; try reflexivity;
    try (rewrite IH; reflexivity);
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma uw_nth_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l. induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma uw_slice_nth : forall (c : list byte) off len i, 0 <= off -> 0 <= len ->
  nth_error (slice c off len) i = if (i <? Z.to_nat len)%nat then nth_error c (Z.to_nat off + i) else None.
Proof. intros c off len i H0 H1. unfold slice. rewrite uw_nth_firstn, uw_nth_skipn. reflexivity. Qed.

Lemma uw_slice_length : forall (c : list byte) off len, 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> length (slice c off len) = Z.to_nat len.
Proof. intros c off len H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

(* a byte list with a NUL holds its C string, then the NUL *)
Lemma uw_cstr_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ [zb 0] ++ rest /\ ~ In (zb 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn [nul_at length] in H; lia|].
  unfold cstr in *. cbn [nul_at firstn] in *. unfold bz in *.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  - exists l. cbn [firstn app]. rewrite (uw_byte_zero b E). split; [reflexivity | intros []].
  - cbn [length] in H. destruct (IH ltac:(lia)) as (rest & Hl & Hn). exists rest.
    cbn [firstn app]. split; [f_equal; exact Hl|].
    intros [Hb|Hin]; [apply E; rewrite Hb; reflexivity | exact (Hn Hin)].
Qed.

Lemma uw_cstr_len : forall l, (length (cstr l) <= nul_at l)%nat.
Proof. intros l. unfold cstr. rewrite length_firstn. lia. Qed.

Section s.
Variable segs : list Segment.

Lemma uw_mbyte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b1|] eqn:E1;
    destruct (mbyte segs (mrestrict H m) a) as [b2|] eqn:E2; cbn [option_map] in E; try discriminate;
    [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma uw_abytes_unique : forall m a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma uw_acstr_short : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 ->
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

Lemma uw_acstr_unique : forall m a s1 s2, acstr_at segs m a s1 -> acstr_at segs m a s2 -> s1 = s2.
Proof.
  intros m a s1 s2 H1 H2.
  destruct (Nat.lt_trichotomy (length s1) (length s2)) as [L|[L|L]].
  - exfalso. exact (uw_acstr_short m a s1 s2 H1 H2 L).
  - destruct H1 as [B1 _]. destruct H2 as [B2 _].
    apply (app_inv_tail [zb 0]). apply (uw_abytes_unique m a); [exact B1 | exact B2 |].
    rewrite !length_app, L. reflexivity.
  - exfalso. exact (uw_acstr_short m a s2 s1 H2 H1 L).
Qed.

Lemma uw_acstr_range : forall m p s, acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof. intros m p s [(Ha & Hl & _) _]. rewrite length_app in Hl. cbn [length] in Hl. lia. Qed.

Lemma uw_abytes_move : forall (m m' : word -> option byte) a bs,
  abytes segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) Hk. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma uw_acstr_move : forall m m' p s, acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) -> acstr_at segs m' p s.
Proof.
  intros m m' p s [Bs N] Hk. split; [|exact N]. apply (uw_abytes_move m m' p _ Bs).
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hk. lia.
Qed.

Lemma uw_vm_move : forall (m m' : word -> option byte) a (n : nat) v, val_mem segs m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) -> val_mem segs m' a n v.
Proof. intros m m' a n v H Hk k Hk'. rewrite Hk by lia. exact (H k Hk'). Qed.

Lemma uw_lb_inj : forall (n : nat) (p1 p2 : Z),
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

Lemma uw_vm_unique : forall m a (n : nat) v1 v2, val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2. apply uw_lb_inj. intros k Hk.
  pose proof (eq_trans (eq_sym (H1 k Hk)) (H2 k Hk)) as E.
  exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E).
Qed.

Lemma uw_au64_unique : forall m a p1 p2, au64_at segs m a p1 -> au64_at segs m a p2 ->
  p1 mod 2 ^ 64 = p2 mod 2 ^ 64.
Proof.
  intros m a p1 p2 H1 H2. pose proof (uw_vm_unique m a 8 p1 p2 H1 H2) as E.
  change (8 * Z.of_nat 8) with 64 in E. exact E.
Qed.

Lemma uw_au32_small_unique : forall m a x1 x2, au32_at segs m a x1 -> au32_at segs m a x2 ->
  0 <= x1 < 2 ^ 31 -> 0 <= x2 < 2 ^ 31 -> x1 = x2.
Proof.
  intros m a x1 x2 H1 H2 R1 R2. pose proof (uw_vm_unique m a 4 x1 x2 H1 H2) as E.
  change (8 * Z.of_nat 4) with 32 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma uw_anlk_unique : forall m g b1 b2, anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[B1 _] L1] [[B2 _] L2]. apply (uw_abytes_unique m g); [exact B1 | exact B2 | lia].
Qed.

Lemma uw_aiftab_unique : forall m bs tab1 tab2,
  aiftab_at segs m LA_G_NL bs tab1 -> aiftab_at segs m LA_G_NL bs tab2 -> tab1 = tab2.
Proof.
  intros m bs tab1 tab2 (L1 & _ & E1) (L2 & _ & E2).
  assert (L : length tab1 = length tab2) by lia.
  apply nth_error_ext. intros i.
  destruct (nth_error tab1 i) as [[n1 x1]|] eqn:H1; destruct (nth_error tab2 i) as [[n2 x2]|] eqn:H2.
  - destruct (E1 i n1 x1 H1) as (R1 & p1 & P1 & _ & C1 & I1).
    destruct (E2 i n2 x2 H2) as (R2 & p2 & P2 & _ & C2 & I2).
    pose proof (uw_au64_unique _ _ _ _ P1 P2) as Ep.
    pose proof (uw_acstr_range _ _ _ C1). pose proof (uw_acstr_range _ _ _ C2).
    rewrite !Z.mod_small in Ep by lia. subst p2.
    rewrite (uw_acstr_unique _ _ _ _ C1 C2).
    rewrite (uw_au32_small_unique _ _ _ _ I1 I2 R1 R2). reflexivity.
  - exfalso. apply nth_error_None in H2. assert (i < length tab1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in H1. assert (i < length tab2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

Lemma uw_astr_arg_unique : forall m a o1 o2, astr_arg segs m a o1 -> astr_arg segs m a o2 -> o1 = o2.
Proof.
  intros m a [s1|] [s2|] H1 H2; cbn [astr_arg] in H1, H2.
  - f_equal. exact (uw_acstr_unique m a s1 s2 (proj2 H1) (proj2 H2)).
  - destruct H1 as [Hn _]. contradiction.
  - destruct H2 as [Hn _]. contradiction.
  - reflexivity.
Qed.

(* the bytes of a slice of a byte list in memory *)
Lemma uw_abytes_slice : forall m a (c : list byte) off len, abytes segs m a c -> 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> abytes segs m (a + off) (slice c off len).
Proof.
  intros m a c off len (Ha & Hl & H) H0 H1 H2. pose proof (uw_slice_length c off len H0 H1 H2) as LS.
  split; [lia|]. split; [rewrite LS; lia|]. intros i Hi. rewrite LS in Hi. rewrite uw_slice_nth by lia.
  replace (i <? Z.to_nat len)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite <- H by lia. f_equal. lia.
Qed.

Lemma uw_abytes_prefix : forall m a l1 l2, abytes segs m a (l1 ++ l2) -> abytes segs m a l1.
Proof.
  intros m a l1 l2 (Ha & Hl & H). rewrite length_app in Hl. split; [exact Ha|]. split; [lia|].
  intros i Hi. rewrite (H i ltac:(rewrite length_app; lia)). apply nth_error_app1. exact Hi.
Qed.

(* the C string of slot i of a marks block (marks_wf: its NUL lies inside the slot) *)
Lemma uw_slot_cstr : forall m p gbs i, abytes segs m p gbs -> Z.of_nat (length gbs) = MK_SIZE ->
  0 <= i < MARKS_MAX ->
  (nul_at (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN) < Z.to_nat MARK_LEN)%nat ->
  acstr_at segs m (p + MK_NAME + MARK_LEN * i) (cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)) /\
  (length (cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)) < 16)%nat.
Proof.
  intros m p gbs i Hb Hl Hi Hn. unfold MK_SIZE, MK_NAME, MARK_LEN, MARKS_MAX in *.
  set (sl := slice gbs (4 + 16 * i) 16) in *.
  assert (LS : length sl = 16%nat) by (unfold sl; rewrite uw_slice_length by lia; reflexivity).
  pose proof (uw_abytes_slice m p gbs (4 + 16 * i) 16 Hb ltac:(lia) ltac:(lia) ltac:(lia)) as Bs. fold sl in Bs.
  destruct (uw_cstr_split sl ltac:(rewrite LS; exact Hn)) as (rest & El & Nn).
  pose proof (uw_cstr_len sl) as Lc.
  split; [|lia].
  split; [|exact Nn].
  rewrite El, app_assoc in Bs. apply uw_abytes_prefix in Bs.
  replace (p + 4 + 16 * i) with (p + (4 + 16 * i)) by lia. exact Bs.
Qed.

(* sub-ranges of the shadow facts *)
Lemma uw_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
  intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + x' / 8) / 8).
  { apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  assert (A2 : (SHADOW_OFF + (x' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8).
  { apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  lia.
Qed.

Lemma uw_ra_sub : forall (rd : reader) Bs x n x' n', range_addressable rd Bs x n -> x <= x' -> x' + n' <= x + n ->
  range_addressable rd Bs x' n'.
Proof. intros rd Bs x n x' n' H H1 H2 y Hy. apply H. lia. Qed.

Lemma uw_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> p' + n' <= p + n -> amem_range p' n'.
Proof. intros p n p' n' H H1 H2. unfold amem_range in *. lia. Qed.

End s.

(* ==========================================================================
   3. link_spec: the names of the marks block, and the fake kernel across write_core
   ========================================================================== *)

Lemma uw_mk_names_nth : forall gbs c, (c < Z.to_nat (mk_n gbs))%nat ->
  nth c (mk_names gbs) [] = cstr (slice gbs (MK_NAME + MARK_LEN * Z.of_nat c) MARK_LEN).
Proof.
  intros gbs c Hc. unfold mk_names.
  set (f := fun i : nat => cstr (slice gbs (MK_NAME + MARK_LEN * Z.of_nat i) MARK_LEN)).
  change (cstr (slice gbs (MK_NAME + MARK_LEN * Z.of_nat c) MARK_LEN)) with (f c).
  rewrite (nth_indep (map f (seq 0 (Z.to_nat (mk_n gbs)))) [] (f 0%nat))
    by (rewrite length_map, length_seq; exact Hc).
  rewrite map_nth, seq_nth by exact Hc. reflexivity.
Qed.

Lemma uw_nk_kstate_eq : forall kbs K, nk_chunks kbs = k_chunks K -> nk_next kbs = Z.of_nat (k_next K) ->
  nk_end_errno kbs = k_end K -> nk_socket_errno kbs = k_sock K -> nk_send_errno kbs = k_send K ->
  nk_kstate kbs = K.
Proof.
  intros kbs [c n e s d] H1 H2 H3 H4 H5. cbn [k_chunks k_next k_end k_sock k_send] in *. unfold nk_kstate.
  rewrite H1, H2, H3, H4, H5, Nat2Z.id. reflexivity.
Qed.

Lemma uw_talk_after_ce : forall K, k_chunks (talk_after K) = k_chunks K /\ k_end (talk_after K) = k_end K.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [split; reflexivity|].
  destruct (negb (k_send K =? 0)); [split; reflexivity|].
  destruct (chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K)) as [v j].
  destruct v; split; reflexivity.
Qed.

Lemma uw_write_state_ce : forall tab nm al reqs K,
  k_chunks (w_state (write_core tab nm al reqs K)) = k_chunks K /\
  k_end (w_state (write_core tab nm al reqs K)) = k_end K.
Proof.
  intros. unfold write_core. destruct nm as [s|]; [|split; reflexivity].
  destruct al as [a|]; [|split; reflexivity]. cbv zeta.
  destruct (Nat.eqb (length s) 0); [split; reflexivity|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [split; reflexivity|].
  destruct (index_of tab s =? 0); [split; reflexivity|]. apply uw_talk_after_ce.
Qed.
