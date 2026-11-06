(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 419 of its 453 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeExit.v, with its module names changed; 167 of its 194 lines of code are new or changed and 426 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A, the SEND piece: its byte algebra, with no symbolic engine and no
   journal (adapted from lib/A/Prog/reac_link_alias_writeSendA.v, whose
   request has the same layout):
   - the request as the code leaves it in the side frame (+0x16c..+0x1d4: checked_memset's zeros, the header stores,
     checked_memcpy's alias) is link_spec.v's `req_write` (mw_req_bytes);
   - the request's shadow after meta_fill_00 (+0x17c: shadow bytes 4..67 of the frame := 0) makes every byte of
     [F + 32, F + 544) addressable (mw_req_ra);
   - the length word's ALU expression (+0x180..+0x188) is 32 + nl_align (4 + |alias|);
   - the EXIT cut's result clause on the talk arm, from talk's Post (mw_pf_talk).

   Proves no function (kind: segment lemma). *)
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
index_of_c talk_c model_write_c model_writeDefs model_writeArmsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Bytes of a value, and lists of bytes in memory
   ========================================================================== *)

Lemma mw_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma mw_le_byte_shiftr : forall v (n k : nat), (k < n)%nat ->
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

Lemma mw_bl_ext : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* the word 0x50010 the code stores at req + 4: type RTM_NEWLINK, flags NLM_F_REQUEST | NLM_F_ACK *)
Lemma mw_hdr_split : Z_to_le_bytes 4 327696 = Z_to_le_bytes 2 RTM_NEWLINK ++ Z_to_le_bytes 2 (F_REQUEST + F_ACK).
Proof. apply mw_bl_ext. vm_compute. reflexivity. Qed.

Lemma mw_land_508 : forall x, 0 <= x < 512 -> Z.land x 508 = 4 * (x / 4).
Proof.
  intros x Hx.
  assert (H : forallb (fun k => Z.eqb (Z.land (Z.of_nat k) 508) (4 * (Z.of_nat k / 4))) (seq 0 512) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat x)).
  rewrite in_seq, Z2Nat.id in H by lia. apply Z.eqb_eq, H. lia.
Qed.

Lemma mw_len_val : forall v, 0 <= v < 256 -> Z.land (v + 7) 508 + 32 = 32 + nl_align (RTA_HDR + v).
Proof. intros v Hv. rewrite mw_land_508 by lia. unfold nl_align, RTA_HDR. lia. Qed.

Lemma mw_talk_after_sock : forall K, k_sock (talk_after K) = 0.
Proof.
  intros K. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [reflexivity|].
  destruct (negb (k_send K =? 0)); [reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; reflexivity.
Qed.

Section s.
Variable segs : list Segment.

Lemma mw_abytes_cat : forall m a b l1 l2,
  abytes segs m a l1 -> b = a + Z.of_nat (length l1) -> abytes segs m b l2 -> abytes segs m a (l1 ++ l2).
Proof.
  intros m a b l1 l2 (H0 & H1 & H2) -> (H3 & H4 & H5). split; [exact H0|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length l1)) as [Hl | Hl].
  - rewrite nth_error_app1 by exact Hl. exact (H2 i Hl).
  - rewrite nth_error_app2 by exact Hl. specialize (H5 (i - length l1)%nat ltac:(lia)).
    replace (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) with (a + Z.of_nat i) in H5 by lia. exact H5.
Qed.

Lemma mw_abytes_le : forall m a (n : nat) v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem segs m a n v -> abytes segs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v H0 H1 Hv. split; [exact H0|]. split; [rewrite length_Z_to_le_bytes; exact H1|].
  intros i Hi. rewrite length_Z_to_le_bytes in Hi. rewrite (Hv i Hi), mw_nth_le_bytes by exact Hi.
  f_equal. apply mw_le_byte_shiftr. exact Hi.
Qed.

Lemma mw_abytes_zeros : forall m a n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> mbyte segs m (a + i) = Some (zb 0)) -> abytes segs m a (zeros n).
Proof.
  intros m a n H0 H1 Hn Hz. unfold zeros. split; [exact H0|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi. apply Hz. lia.
Qed.

Lemma mw_req_write_length : forall idx (sa : list byte),
  Z.of_nat (length (req_write idx sa)) = 32 + nl_align (RTA_HDR + Z.of_nat (length sa)).
Proof.
  intros idx sa. unfold req_write, zeros. cbv zeta.
  rewrite !length_app, !length_Z_to_le_bytes, !repeat_length.
  unfold nl_align, RTA_HDR. lia.
Qed.

(* THE REQUEST, as the code leaves it at req = F + 32: the bytes link_spec.v's req_write names *)
Lemma mw_req_bytes : forall (m : word -> option byte) req idx (sa : list byte),
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
  apply (mw_abytes_cat m req (req + 4)); [apply mw_abytes_le; [lia | lia | exact V0] | rewrite length_Z_to_le_bytes; lia |].
  rewrite (app_assoc (Z_to_le_bytes 2 RTM_NEWLINK)), <- mw_hdr_split.
  apply (mw_abytes_cat m (req + 4) (req + 8)); [apply mw_abytes_le; [lia | lia | exact V4] | rewrite length_Z_to_le_bytes; lia |].
  apply (mw_abytes_cat m (req + 8) (req + 12)); [apply mw_abytes_le; [lia | lia | exact V8] | rewrite length_Z_to_le_bytes; lia |].
  apply (mw_abytes_cat m (req + 12) (req + 16));
    [apply mw_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 12 + i) with (req + (12 + i)) by ring; apply Z12; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (mw_abytes_cat m (req + 16) (req + 20));
    [apply mw_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 16 + i) with (req + (16 + i)) by ring; apply Z12; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (mw_abytes_cat m (req + 20) (req + 24)); [apply mw_abytes_le; [lia | lia | exact V20] | rewrite length_Z_to_le_bytes; lia |].
  apply (mw_abytes_cat m (req + 24) (req + 32));
    [apply mw_abytes_zeros; [lia | lia | lia | intros i Hi; replace (req + 24 + i) with (req + (24 + i)) by ring; apply Z24; lia]
    | unfold zeros; rewrite repeat_length; lia |].
  apply (mw_abytes_cat m (req + 32) (req + 34));
    [apply mw_abytes_le; [lia | lia |]; replace (RTA_HDR + Z.of_nat (length sa)) with (Z.of_nat (length sa) + 4)
       by (unfold RTA_HDR; ring); exact V32
    | rewrite length_Z_to_le_bytes; lia |].
  apply (mw_abytes_cat m (req + 34) (req + 36)); [apply mw_abytes_le; [lia | lia | exact V34] | rewrite length_Z_to_le_bytes; lia |].
  apply (mw_abytes_cat m (req + 36) (req + 36 + Z.of_nat (length sa))).
  - split; [lia|]. split; [lia|]. exact VA.
  - reflexivity.
  - apply mw_abytes_zeros; [lia | unfold RTA_HDR in *; lia | unfold RTA_HDR in *; lia |].
    intros i Hi. replace (req + 36 + Z.of_nat (length sa) + i) with (req + (36 + Z.of_nat (length sa) + i)) by ring.
    apply ZT. unfold RTA_HDR in *. lia.
Qed.

(* the request's shadow after meta_fill_00(F's shadow + 4, 64): every byte of [F + 32, F + 544) is addressable *)
Lemma mw_req_ra : forall (rd : reader) F lo n, F mod 8 = 0 -> 0 <= F ->
  (forall j, 4 <= j < 68 -> rd (SHADOW_OFF + F / 8 + j) = Some 0) ->
  F + 32 <= lo -> lo + n <= F + 544 -> range_addressable rd SHADOW_OFF lo n.
Proof.
  intros rd F lo n HF8 HF0 HZ Hlo Hhi x Hx. unfold shadow_of_addr.
  assert (Ex : x / 8 = F / 8 + (x - F) / 8) by lia.
  rewrite Ex. replace (SHADOW_OFF + (F / 8 + (x - F) / 8)) with (SHADOW_OFF + F / 8 + (x - F) / 8) by lia.
  exists 0. split; [apply HZ; lia | left; reflexivity].
Qed.
End s.

(* ==========================================================================
   2. The talk arm of write_model, and the Post's fields at the EXIT cut
   ========================================================================== *)

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).

Lemma mw_pf_talk : forall (cx : mwcx) (W' : world SEGS) (m' : word -> option byte) mbs kbs tab sn sa,
  amodel_at SEGS (mw_m0 cx) (mw_m cx) mbs ->
  anlk_at SEGS (mw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab ->
  acstr_at SEGS (mw_m0 cx) (mw_name cx) sn -> mw_name cx <> 0 -> sn <> [] ->
  acstr_at SEGS (mw_m0 cx) (mw_alias cx) sa -> mw_alias cx <> 0 -> Z.of_nat (length sa) < ALIAS_MAX ->
  index_of tab sn <> 0 ->
  (exists mbs', amodel_at SEGS (mrestrict (w_H W') m') (mw_m cx) mbs' /\ model_wf mbs'
     /\ md_next mbs' = Z.of_nat (k_next (talk_after (md_kstate mbs kbs)))
     /\ md_socket_errno mbs' = 0
     /\ md_send_errno mbs' = k_send (talk_after (md_kstate mbs kbs))
     /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs
     /\ md_reqs mbs' = (if talk_owes (md_kstate mbs kbs)
                        then owe (md_reqs mbs) (req_write (index_of tab sn) sa) else md_reqs mbs)
     /\ md_n_req mbs' = Z.of_nat (length (md_reqs mbs'))) ->
  mw_pf cx (w64 (talk_rc_model (md_kstate mbs kbs))) W' m'.
Proof.
  intros cx W' m' mbs kbs tab sn sa HM NK IT SN Hn0 Sne SA Ha0 HL Inz NL.
  intros mbs2 kbs2 tab2 nm2 al2 HM2 NK2 IT2 SN2 SA2.
  assert (mbs2 = mbs) by exact (mw_amodel_unique SEGS _ _ _ _ HM2 HM). subst mbs2.
  assert (kbs2 = kbs) by exact (mw_anlk_unique SEGS _ _ _ _ NK2 NK). subst kbs2.
  assert (tab2 = tab) by exact (mw_aiftab_unique SEGS _ _ _ _ _ IT2 IT). subst tab2.
  assert (nm2 = Some sn) by (apply (mw_astr_arg_unique SEGS _ _ _ _ SN2); split; [exact Hn0 | exact SN]). subst nm2.
  assert (al2 = Some sa) by (apply (mw_astr_arg_unique SEGS _ _ _ _ SA2); split; [exact Ha0 | exact SA]). subst al2.
  cbv zeta. rewrite (mw_wm_talk tab sn sa (md_reqs mbs) (md_kstate mbs kbs) Sne HL Inz).
  cbn [w_rc w_reqs w_state].
  split; [reflexivity|].
  destruct NL as (mbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  exists mbs'. split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
  split; [rewrite mw_talk_after_sock; exact N4|]. split; [exact N5|].
  split; [exact N8|]. split; [rewrite N9, N8; reflexivity|].
  split; [exact N6 | exact N7].
Qed.
End p.
