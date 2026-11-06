(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 419 of its 453 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeExit.v, with its module names changed; 167 of its 194 lines of code are new or changed and 426 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeSendA.v, with its numbers changed; 111 of its 201 lines of code are new or changed and 104 lines of the source are left out. *)
(* model_read on image A: the byte algebra of its read (+0x184..+0x1e4), with no symbolic engine and no journal
   (adapted from model_writeSendA.v, whose request layout is the same up to byte 32):
   - the request the code leaves at r = F + 0x20 (checked_memset's zeros, the header stores, the index at r + 20) is
     link_spec.v's `req_read` (mr_req_read_bytes);
   - the request's shadow bytes 4..7 := 0 (+0x18c..+0x198) make every byte of [F + 32, F + 64) addressable (mr_req_ra);
   - small facts the walk's Pre and Post steps share.
   Proves no function (kind: segment lemma of model_read's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma mr_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma mr_le_byte_shiftr : forall v (n k : nat), (k < n)%nat ->
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

Lemma mr_bl_ext : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* the word 0x10012 the code stores at r + 4: type RTM_GETLINK, flags NLM_F_REQUEST *)
Lemma mr_hdr_split : Z_to_le_bytes 4 65554 = Z_to_le_bytes 2 RTM_GETLINK ++ Z_to_le_bytes 2 F_REQUEST.
Proof. apply mr_bl_ext. vm_compute. reflexivity. Qed.

Lemma mr_talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; reflexivity.
Qed.

(* two ranges with no byte in common are apart *)
Lemma mr_apart_of_disj : forall p n q m, 0 < n -> 0 < m ->
  (forall a, p <= a < p + n -> q <= a < q + m -> False) -> apart p n q m.
Proof.
  intros p n q m Hn Hm H. unfold apart.
  destruct (Z.le_gt_cases (p + n) q) as [H1 | H1]; [left; exact H1|].
  destruct (Z.le_gt_cases (q + m) p) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (H (Z.max p q)); lia.
Qed.

Lemma mr_hull_sub : forall (rd : reader) p n q k,
  shadow_hull_vis rd p n -> p <= q -> 0 < k -> q + k <= p + n -> 0 <= p -> shadow_hull_vis rd q k.
Proof.
  intros rd p n q k H H1 H2 H3 H4 s Hs. apply H. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (SHADOW_OFF + p / 8) (SHADOW_OFF + q / 8) 8 ltac:(lia)
    ltac:(pose proof (Z.div_le_mono p q 8 ltac:(lia) H1); lia)).
  pose proof (Z.div_le_mono (SHADOW_OFF + (q + k - 1) / 8) (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)
    ltac:(pose proof (Z.div_le_mono (q + k - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)); lia)).
  lia.
Qed.

Section s.
Variable segs : list Segment.

Lemma mr_abytes_cat : forall m a b l1 l2,
  abytes segs m a l1 -> b = a + Z.of_nat (length l1) -> abytes segs m b l2 -> abytes segs m a (l1 ++ l2).
Proof.
  intros m a b l1 l2 (H0 & H1 & H2) -> (H3 & H4 & H5). split; [exact H0|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length l1)) as [Hl | Hl].
  - rewrite nth_error_app1 by exact Hl. exact (H2 i Hl).
  - rewrite nth_error_app2 by exact Hl. specialize (H5 (i - length l1)%nat ltac:(lia)).
    replace (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) with (a + Z.of_nat i) in H5 by lia. exact H5.
Qed.

Lemma mr_abytes_le : forall m a (n : nat) v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem segs m a n v -> abytes segs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v H0 H1 Hv. split; [exact H0|]. split; [rewrite length_Z_to_le_bytes; exact H1|].
  intros i Hi. rewrite length_Z_to_le_bytes in Hi. rewrite (Hv i Hi), mr_nth_le_bytes by exact Hi.
  f_equal. apply mr_le_byte_shiftr. exact Hi.
Qed.

Lemma mr_abytes_zeros : forall m a n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> mbyte segs m (a + i) = Some (zb 0)) -> abytes segs m a (zeros n).
Proof.
  intros m a n H0 H1 Hn Hz. unfold zeros. split; [exact H0|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi. apply Hz. lia.
Qed.

(* THE REQUEST, as the code leaves it at r = F + 32: the bytes link_spec.v's req_read names *)
Lemma mr_req_read_bytes : forall (m : word -> option byte) req idx,
  0 <= req -> req + 32 <= 2 ^ 64 ->
  val_mem segs m req 4 32 -> val_mem segs m (req + 4) 4 65554 -> val_mem segs m (req + 8) 4 1 ->
  (forall i, 12 <= i < 20 -> mbyte segs m (req + i) = Some (zb 0)) ->
  val_mem segs m (req + 20) 4 idx ->
  (forall i, 24 <= i < 32 -> mbyte segs m (req + i) = Some (zb 0)) ->
  abytes segs m req (req_read idx).
Proof.
  intros m req idx H0 H1 V0 V4 V8 Z12 V20 Z24.
  unfold req_read, req_head.
  apply (mr_abytes_cat m req (req + 4)); [apply mr_abytes_le; [lia | lia | exact V0] | rewrite length_Z_to_le_bytes; lia |].
  rewrite (app_assoc (Z_to_le_bytes 2 RTM_GETLINK)), <- mr_hdr_split.
  apply (mr_abytes_cat m (req + 4) (req + 8)); [apply mr_abytes_le; [lia | lia | exact V4] | rewrite length_Z_to_le_bytes; lia |].
  apply (mr_abytes_cat m (req + 8) (req + 12)); [apply mr_abytes_le; [lia | lia | exact V8] | rewrite length_Z_to_le_bytes; lia |].
  apply (mr_abytes_cat m (req + 12) (req + 16));
    [apply mr_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 12 + i) with (req + (12 + i)) by ring; apply Z12; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (mr_abytes_cat m (req + 16) (req + 20));
    [apply mr_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 16 + i) with (req + (16 + i)) by ring; apply Z12; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (mr_abytes_cat m (req + 20) (req + 24)); [apply mr_abytes_le; [lia | lia | exact V20] | rewrite length_Z_to_le_bytes; lia |].
  apply mr_abytes_zeros; [lia | lia | lia |].
  intros i Hi. replace (req + 24 + i) with (req + (24 + i)) by ring. apply Z24. lia.
Qed.

(* the request's shadow after the four stores (+0x18c..+0x198: shadow bytes 4..7 of the frame := 0) *)
Lemma mr_req_ra : forall (rd : reader) F lo n, F mod 8 = 0 -> 0 <= F ->
  (forall j, 4 <= j < 8 -> rd (SHADOW_OFF + F / 8 + j) = Some 0) ->
  F + 32 <= lo -> lo + n <= F + 64 -> range_addressable rd SHADOW_OFF lo n.
Proof.
  intros rd F lo n HF8 HF0 HZ Hlo Hhi x Hx. unfold shadow_of_addr.
  assert (Ex : x / 8 = F / 8 + (x - F) / 8) by lia.
  rewrite Ex. replace (SHADOW_OFF + (F / 8 + (x - F) / 8)) with (SHADOW_OFF + F / 8 + (x - F) / 8) by lia.
  exists 0. split; [apply HZ; lia | left; reflexivity].
Qed.
(* a byte list in memory moves to a memory that shows the same bytes and keeps them writable *)
Lemma mr_au8arr_move : forall (m m' : word -> option byte) a l,
  au8arr segs m a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, a <= x < a + Z.of_nat (length l) -> writable_at segs m' x) ->
  au8arr segs m' a l.
Proof.
  intros m m' a l ((H0 & H1 & H2) & _) HK HW. split; [split; [exact H0|]; split; [exact H1|]|].
  - intros i Hi. rewrite (HK (a + Z.of_nat i) ltac:(lia)). exact (H2 i Hi).
  - intros i Hi. apply HW. lia.
Qed.

Lemma mr_amodel_move : forall (m m' : word -> option byte) p mbs,
  amodel_at segs m p mbs ->
  (forall x, p <= x < p + MD_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, p <= x < p + MD_SIZE -> writable_at segs m' x) ->
  amodel_at segs m' p mbs.
Proof.
  intros m m' p mbs (HA & HL) HK HW. split; [|exact HL].
  apply (mr_au8arr_move m m' p mbs HA); rewrite HL; assumption.
Qed.

Lemma mr_abuf_move : forall (m m' : word -> option byte) p n,
  abuf segs m p n ->
  (forall x, p <= x < p + n -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, p <= x < p + n -> writable_at segs m' x) ->
  abuf segs m' p n.
Proof.
  intros m m' p n (junk & HL & HA) HK HW. exists junk. split; [exact HL|].
  apply (mr_au8arr_move m m' p junk HA); rewrite HL; assumption.
Qed.

(* a buffer whose first byte is now 0 and whose other bytes did not change: an empty C string, and still a buffer *)
Lemma mr_bufz : forall (m m' : word -> option byte) p n,
  1 <= n -> abuf segs m p n ->
  mbyte segs m' p = Some (zb 0) ->
  (forall i, 1 <= i < n -> mbyte segs m' (p + i) = mbyte segs m (p + i)) ->
  (forall x, p <= x < p + n -> writable_at segs m' x) ->
  acstr_at segs m' p [] /\ abuf segs m' p n.
Proof.
  intros m m' p n Hn (junk & Hl & ((J0 & J1 & Jb) & Jw)) MB0 HV WRX.
  destruct junk as [|j0 jt]; [cbn [length] in Hl; lia|].
  cbn [length] in Hl, J1.
  split.
  - split; [|intros []]. split; [exact J0|]. split; [cbn [length app]; lia|].
    intros i Hi. cbn [length app] in Hi. destruct i as [|i]; [|lia]. rewrite Z.add_0_r. exact MB0.
  - exists (zb 0 :: jt). split; [cbn [length]; lia|]. split.
    + split; [exact J0|]. split; [cbn [length]; lia|].
      intros i Hi. destruct i as [|i].
      * rewrite Z.add_0_r. exact MB0.
      * cbn [nth_error]. rewrite (HV (Z.of_nat (Datatypes.S i)) ltac:(cbn [length] in Hi; lia)).
        exact (Jb (Datatypes.S i) Hi).
    + intros i Hi. cbn [length] in Hi. apply WRX. lia.
Qed.

(* an empty C string stays one where its byte did not change *)
Lemma mr_cstr_nil_move : forall (m m' : word -> option byte) p,
  acstr_at segs m p [] -> mbyte segs m' p = mbyte segs m p -> acstr_at segs m' p [].
Proof.
  intros m m' p ((H0 & H1 & H2) & N) HK. split; [|exact N]. split; [exact H0|]. split; [exact H1|].
  intros i Hi. cbn [length app] in Hi. destruct i as [|i]; [|lia]. rewrite Z.add_0_r, HK.
  pose proof (H2 0%nat ltac:(cbn; lia)) as Q. rewrite Z.add_0_r in Q. exact Q.
Qed.
(* a byte list whose first byte is 0 starts an empty C string *)
Lemma mr_cstr_nil_of_abytes : forall (m : word -> option byte) p l,
  abytes segs m p l -> nth_error l 0 = Some (zb 0) -> acstr_at segs m p [].
Proof.
  intros m p l (H0 & H1 & H2) Hn. destruct l as [|b l]; [discriminate Hn|].
  split; [|intros []]. split; [exact H0|]. split; [cbn [length app] in *; lia|].
  intros i Hi. cbn [length app] in Hi. destruct i as [|i]; [|lia].
  rewrite (H2 0%nat ltac:(cbn; lia)). exact Hn.
Qed.
End s.
