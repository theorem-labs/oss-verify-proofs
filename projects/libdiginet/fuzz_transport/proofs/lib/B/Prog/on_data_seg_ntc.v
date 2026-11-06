(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths, module names and numbers changed; 1047 of its 1133 lines of code are new or changed and 679 lines of the source are left out. *)
(* on_data_seg_ntc: the notice piece of on_data's image-B G-form walk, od_ntc : forall fx rc B MT, od_ntc_stmt
   (lib/B/Prog/on_data_seg_cut.v), code +0x2ec .. +0x3dc from AF_on_data (0x88d34 .. 0x88e24 of the listing
   lib/B/Prog/DgnTransportBList.v, fuzz_transport.asan-ubsan), ended at the cut od_nc_at at the `jalr a2` (+0x3e0).
   Image B's twin of lib/A/Prog/on_data_seg_ntc.v: the same two runs and the same cut at image B's offsets and names,
   but for what image B's code changes: after the checked load of S_state the stores at p + 8, p + 4 and p + 16 come
   in another order; a0 = fp + 32 for the check of f + 32 is computed after the memset; the 2-byte check of f + 28
   reads its shadow byte through s8, which holds the shadow address of f + 28 from the cut on (od_regs_ntc; image A
   loads it from the frame word at s1 + 16), so the symbolic state pins s8 and has no frame-word region; the loads of
   s + 96 and s + 104 go through a0 = s + 96 and a1 = s + 104.
   - The symbolic state at the cut (odn_ss, odn_entry): s3 = s and s11 = the shadow base as literals; s5 = fp + 20,
     s6 = fp + 28, s2 = the shadow address of f + 20 and s8 = the shadow address of f + 28 over the atom 20 (fp) and
     the atom 32 (SHADOW_OFF + fp / 8); regions: the notice's shadow bytes 4 .. 12 and its bytes [p, p + 24),
     [p + 48, p + 72) (p = F + 32, writable: bytes of the frame the journal owns), g_s's notify, notify_ctx and state
     (TWorldG.v tw_read_val at the world ondata_w3 (ondata_w2 B1 b r now) b) and their shadow bytes
     (trans_ondata_cells), f's fields at f + 20 .. f + 48 and their shadow bytes (trans_dframe_at at the call's entry,
     carried to the cut by the frame clause of od_cur's acall_kept_g: ondata_wr is a set of bytes of G, odn_wr_G).
   - Run 1 (TransportGRunB.v paj_run_x) to `jal __asan_memset` (+0x34c), taken through TransportGCg.v gx_intrin_at
     (destination [p + 24, p + 48): bytes of the own frame, shadow bytes 7 .. 9 just set to 0); the seven regions are
     kept across it (YC1h.v jafter_call_keep_hi); run 2 (paj_run_to_x) to the cut.
   - The cut's state od_nc_cur: od_cur carried by TransportGFrame.v dk_kept_nfz_gw over odn_Z (the notice's shadow
     bytes and 72 bytes, the memset's stack window), the 72 bytes as odn_nb with the fields od_nc_cur lists, and the
     registers od_regs_nc. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_frame_is_keepalive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Bytes, chunks and shadow geometry                                *)
(* ------------------------------------------------------------------ *)

(* A byte of the view read as 0 is a stored 0. *)
Lemma odn_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* val_mem reads its value only modulo 2 ^ (8 n). *)
Lemma odn_vm_mod : forall (m : word -> option byte) a (n : nat) v v',
  v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m a n v'.
Proof. intros m a n v v' E H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite E. reflexivity. Qed.

(* The low w bytes of a 64-bit literal are those of the number. *)
Lemma odn_lit_mod : forall v (n : nat), (n <= 8)%nat ->
  bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros v n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  assert (Hd : (2 ^ (8 * Z.of_nat n) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_nat n)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia).
Qed.

(* A sign extension keeps the low w bits. *)
Lemma odn_swrap_mod : forall (w : N) z, (0 < w)%N ->
  bv_swrap w z mod 2 ^ Z.of_N w = z mod 2 ^ Z.of_N w.
Proof.
  intros w z Hw. unfold bv_swrap, bv_wrap. change (bv_modulus w) with (2 ^ Z.of_N w).
  unfold bv_half_modulus. change (bv_modulus w) with (2 ^ Z.of_N w).
  assert (Hp : 0 < 2 ^ Z.of_N w) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. lia.
Qed.

(* The bytes put n v leaves, read back as a value. *)
Lemma odn_garr8_put : forall (m : word -> option byte) a (n : nat) v,
  garr8 tfibsegs m a (map DSpec.bz (TW.put n v)) -> val_mem tfibsegs m a n v.
Proof.
  intros m a n v H k Hk.
  assert (Hk' : (k < length (map DSpec.bz (TW.put n v)))%nat) by (rewrite length_map, TWL.length_put; exact Hk).
  destruct (H k Hk') as [Hv Hr].
  assert (E : nth k (map DSpec.bz (TW.put n v)) 0 = YO0f.le_byte v n k).
  { rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by exact Hk'.
    rewrite map_nth. unfold DSpec.bz. apply tw_le_byte_put. exact Hk. }
  rewrite E in Hv, Hr. pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
  rewrite H0. rewrite (tw_le_byte1 _ Hr). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The struct diginet_frame f                                       *)
(* ------------------------------------------------------------------ *)

(* The four fields of f the code reads (h.send_counter at 20, h.retry at 28, body at 32, body_len at 40), as the
   parse left them (DgnTransportCg.v frame_f_bytes at fr_code b = 0). *)
Lemma odn_ff : forall (m : word -> option byte) fp buf b fj,
  DSpec.fr_code b = 0 -> length fj = 64%nat ->
  garr8 tfibsegs m fp (frame_f_bytes buf b fj) ->
  val_mem tfibsegs m (fp + 20) 4 (DSpec.fr_send b) /\ val_mem tfibsegs m (fp + 28) 2 (DSpec.fr_retry b) /\
  val_mem tfibsegs m (fp + 32) 8 (buf + 30) /\ val_mem tfibsegs m (fp + 40) 8 (DSpec.fr_body_len b).
Proof.
  intros m fp buf b fj Hc Hfj H.
  destruct (DSpec.fr_code_ok b Hc) as (Hlb & _).
  unfold frame_f_bytes, frame_f_cells in H. rewrite Hc in H. cbn [Z.eqb] in H.
  unfold PParse.parse_cells in H. cbn [LC.cells_bytes LC.cbytes] in H.
  unfold Mem.le2, Mem.le4, Mem.le8, word_to_le_bytes in H.
  rewrite !map_app in H.
  assert (L6a : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
  assert (L6b : length (DSpec.fr_src b) = 6%nat) by (unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia).
  assert (L2 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (rewrite length_firstn, length_skipn; lia).
  apply garr8_app in H as [_ H]. rewrite length_map, L6a in H.
  apply garr8_app in H as [_ H]. rewrite length_map, L6b in H.
  apply garr8_app in H as [_ H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [_ H]. rewrite length_map, L2 in H.
  apply garr8_app in H as [_ H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [_ H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [Hs H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [_ H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [Hr H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [_ H]. cbn [length map] in H.
  apply garr8_app in H as [_ H]. cbn [length map] in H.
  apply garr8_app in H as [Hb H]. rewrite length_map, Mem.length_Z_to_le_bytes in H.
  apply garr8_app in H as [Hl _].
  change (Z_to_le_bytes 4) with (TW.put 4) in Hs. change (Z_to_le_bytes 2) with (TW.put 2) in Hr.
  change (Z_to_le_bytes 8) with (TW.put 8) in Hb, Hl.
  apply odn_garr8_put in Hs, Hr, Hb, Hl.
  replace (fp + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2) with (fp + 20) in Hs
    by (cbn [Z.of_nat]; lia).
  replace (fp + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 4 +
    Z.of_nat 4) with (fp + 28) in Hr by (cbn [Z.of_nat]; lia).
  replace (fp + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 4 +
    Z.of_nat 4 + Z.of_nat 2 + Z.of_nat 1 + Z.of_nat 1) with (fp + 32) in Hb by (cbn [Z.of_nat]; lia).
  replace (fp + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 2 + Z.of_nat 4 +
    Z.of_nat 4 + Z.of_nat 2 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 8) with (fp + 40) in Hl by (cbn [Z.of_nat]; lia).
  split; [|split; [|split]].
  - apply (odn_vm_mod _ _ 4 _ _ (odn_lit_mod _ 4 ltac:(lia))). exact Hs.
  - apply (odn_vm_mod _ _ 2 _ _ (odn_lit_mod _ 2 ltac:(lia))). exact Hr.
  - apply (odn_vm_mod _ _ 8 _ _ (odn_lit_mod _ 8 ltac:(lia))). exact Hb.
  - apply (odn_vm_mod _ _ 8 _ _ (odn_lit_mod _ 8 ltac:(lia))). exact Hl.
Qed.

(* The frame's fields lie in their ranges. *)
Lemma odn_at8_range : forall l i, 0 <= DSpec.at8 l i < 256.
Proof.
  intros l i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i l (DSpec.b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.
Lemma odn_fr_ranges : forall b, DSpec.fr_code b = 0 ->
  0 <= DSpec.fr_send b < 2 ^ 32 /\ 0 <= DSpec.fr_retry b < 2 ^ 16 /\ 0 <= DSpec.fr_body_len b < 2 ^ 16 /\
  (30 <= length b)%nat.
Proof.
  intros b Hc. destruct (DSpec.fr_code_ok b Hc) as (Hlb & _ & Hnb).
  unfold DSpec.fr_send, DSpec.fr_retry, DSpec.fr_body_len, DSpec.be32, DSpec.be16 in *.
  unfold DSpec.fr_numbytes, DSpec.be16 in Hnb |- *.
  pose proof (odn_at8_range b 18). pose proof (odn_at8_range b 19). pose proof (odn_at8_range b 20).
  pose proof (odn_at8_range b 21). pose proof (odn_at8_range b 26). pose proof (odn_at8_range b 27).
  pose proof (odn_at8_range b 14). pose proof (odn_at8_range b 15).
  cbn [Nat.succ] in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The notice's 72 bytes                                            *)
(* ------------------------------------------------------------------ *)

(* The bytes the code leaves at p = F + 32: kind 3, state, 8 zero bytes, fp, the memset's 24 zero bytes, body,
   body_len, counter, retry, 2 zero bytes. *)
Definition odn_nb (st fp bp bl sd rt : Z) : list byte :=
  TW.put 4 3 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fp ++ TW.put 8 0 ++ TW.put 8 0 ++ TW.put 8 0 ++
  TW.put 8 bp ++ TW.put 8 bl ++ TW.put 4 sd ++ TW.put 2 rt ++ TW.put 2 0.

(* Eight bytes read as 0 are a stored 0. *)
Lemma odn_vm_zero8 : forall (H : word -> bool) (m : word -> option byte) a,
  (forall i, 0 <= i < 8 -> aview tfibsegs H m (a + i) = Some 0) -> val_mem tfibsegs (mrestrict H m) a 8 0.
Proof.
  intros H m a Hz k Hk. pose proof (Hz (Z.of_nat k) ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb.
  assert (L0 : YO0f.le_byte 0 8 k = 0)
    by (unfold YO0f.le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia; reflexivity).
  rewrite L0. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma odn_nb_garr8 : forall (H : word -> bool) (m : word -> option byte) F st fp bp bl sd rt,
  val_mem tfibsegs (mrestrict H m) (F + 32) 4 3 -> val_mem tfibsegs (mrestrict H m) (F + 36) 4 st ->
  val_mem tfibsegs (mrestrict H m) (F + 40) 8 0 -> val_mem tfibsegs (mrestrict H m) (F + 48) 8 fp ->
  (forall a, F + 56 <= a < F + 80 -> aview tfibsegs H m a = Some 0) ->
  val_mem tfibsegs (mrestrict H m) (F + 80) 8 bp -> val_mem tfibsegs (mrestrict H m) (F + 88) 8 bl ->
  val_mem tfibsegs (mrestrict H m) (F + 96) 4 sd -> val_mem tfibsegs (mrestrict H m) (F + 100) 2 rt ->
  val_mem tfibsegs (mrestrict H m) (F + 102) 2 0 ->
  garr8 tfibsegs (mrestrict H m) (F + 32) (map DSpec.bz (odn_nb st fp bp bl sd rt)).
Proof.
  intros H m F st fp bp bl sd rt V0 V4 V8 V16 Z24 V48 V56 V64 V68 V70.
  assert (VZ : forall c, 0 <= c < 3 -> val_mem tfibsegs (mrestrict H m) (F + 56 + 8 * c) 8 0)
    by (intros c Hc; apply odn_vm_zero8; intros i Hi; apply Z24; lia).
  unfold odn_nb. rewrite !map_app.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 4 3 V0) |].
  rewrite length_map, TWL.length_put. replace (F + 32 + Z.of_nat 4) with (F + 36) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 4 st V4) |].
  rewrite length_map, TWL.length_put. replace (F + 36 + Z.of_nat 4) with (F + 40) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 0 V8) |].
  rewrite length_map, TWL.length_put. replace (F + 40 + Z.of_nat 8) with (F + 48) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 fp V16) |].
  rewrite length_map, TWL.length_put. replace (F + 48 + Z.of_nat 8) with (F + 56 + 8 * 0) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 0 (VZ 0 ltac:(lia))) |].
  rewrite length_map, TWL.length_put. replace (F + 56 + 8 * 0 + Z.of_nat 8) with (F + 56 + 8 * 1) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 0 (VZ 1 ltac:(lia))) |].
  rewrite length_map, TWL.length_put. replace (F + 56 + 8 * 1 + Z.of_nat 8) with (F + 56 + 8 * 2) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 0 (VZ 2 ltac:(lia))) |].
  rewrite length_map, TWL.length_put. replace (F + 56 + 8 * 2 + Z.of_nat 8) with (F + 80) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 bp V48) |].
  rewrite length_map, TWL.length_put. replace (F + 80 + Z.of_nat 8) with (F + 88) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 8 bl V56) |].
  rewrite length_map, TWL.length_put. replace (F + 88 + Z.of_nat 8) with (F + 96) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 4 sd V64) |].
  rewrite length_map, TWL.length_put. replace (F + 96 + Z.of_nat 4) with (F + 100) by lia.
  apply garr8_app. split; [exact (TGNA.garr8_of_put _ _ _ 2 rt V68) |].
  rewrite length_map, TWL.length_put. replace (F + 100 + Z.of_nat 2) with (F + 102) by lia.
  exact (TGNA.garr8_of_put _ _ _ 2 0 V70).
Qed.

(* Reading a field of a byte list built of put pieces (lib/Prog/T/WalkNotify.v's u_at_app_l / u_at_app_r). *)
Lemma odn_ua_l : forall (l1 l2 : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l1) ->
  TW.u_at (l1 ++ l2) k n = TW.u_at l1 k n.
Proof.
  intros l1 l2 k n Hk Hn. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app. replace (Z.to_nat k - length l1)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app. rewrite length_skipn. replace (n - (length l1 - Z.to_nat k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma odn_ua_r : forall (l1 l2 : list byte) k n, Z.of_nat (length l1) <= k ->
  TW.u_at (l1 ++ l2) k n = TW.u_at l2 (k - Z.of_nat (length l1)) n.
Proof.
  intros l1 l2 k n Hk. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  f_equal. f_equal. lia.
Qed.
Lemma odn_ua_put : forall n v k, k = 0 -> TW.u_at (TW.put n v) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros n v k ->. apply TWL.u_at_put. Qed.
Ltac odn_fld :=
  repeat (rewrite odn_ua_r by (rewrite ?TWL.length_put; cbn; lia); rewrite ?TWL.length_put);
  rewrite ?odn_ua_l by (rewrite ?TWL.length_put; cbn; lia);
  first [ rewrite odn_ua_put by (cbn; lia) | idtac ].

Lemma odn_nb_fields : forall st fp bp bl sd rt,
  0 <= st < 2 ^ 32 -> 0 <= bp < 2 ^ 64 -> 0 <= bl < 2 ^ 64 -> 0 <= sd < 2 ^ 32 -> 0 <= rt < 2 ^ 16 ->
  length (odn_nb st fp bp bl sd rt) = 72%nat /\
  TW.s32_at (odn_nb st fp bp bl sd rt) 0 = TS0.DIGINET_N_DATA /\
  TW.s32_at (odn_nb st fp bp bl sd rt) 4 = bv_swrap 32 st /\
  TW.s32_at (odn_nb st fp bp bl sd rt) 8 = 0 /\ TW.s32_at (odn_nb st fp bp bl sd rt) 12 = 0 /\
  TW.u_at (odn_nb st fp bp bl sd rt) 24 8 = 0 /\ TW.u_at (odn_nb st fp bp bl sd rt) 32 8 = 0 /\
  TW.s32_at (odn_nb st fp bp bl sd rt) 40 = 0 /\ TW.u_at (odn_nb st fp bp bl sd rt) 48 8 = bp /\
  TW.u_at (odn_nb st fp bp bl sd rt) 56 8 = bl /\ TW.u_at (odn_nb st fp bp bl sd rt) 64 4 = sd /\
  TW.u_at (odn_nb st fp bp bl sd rt) 68 2 = rt.
Proof.
  intros st fp bp bl sd rt Hst Hbp Hbl Hsd Hrt. unfold odn_nb, TW.s32_at.
  split; [rewrite ?length_app, ?TWL.length_put; reflexivity |].
  split; [odn_fld; reflexivity |].
  split; [odn_fld; rewrite Z.mod_small by lia; reflexivity |].
  split; [odn_fld; reflexivity |].
  split; [odn_fld; reflexivity |].
  split; [odn_fld; reflexivity |].
  split; [odn_fld; reflexivity |].
  split; [odn_fld; reflexivity |].
  split; [odn_fld; apply Z.mod_small; lia |].
  split; [odn_fld; apply Z.mod_small; lia |].
  split; [odn_fld; apply Z.mod_small; lia |].
  odn_fld; apply Z.mod_small; lia.
Qed.

(* The world's g_s fields the code reads, at their numeral offsets. *)
Lemma odn_notify_eq : forall Bx, TW.S_notify Bx = TW.u_at Bx (TW.OFF_g_s + 96) 8.
Proof. intros Bx. reflexivity. Qed.
Lemma odn_state_eq : forall Bx, TW.S_state Bx = bv_swrap 32 (TW.u_at Bx (TW.OFF_g_s + 112) 4).
Proof. intros Bx. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 4. The symbolic state at the notice path (+0x2ec)                   *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the cut; 32 the shadow address of f's granule 0, SHADOW_OFF + fp / 8; 33, 34
   g_s.notify and g_s.notify_ctx; 35 the four bytes of g_s.state; 36 .. 39 f's send counter, retry, body pointer
   and body length. Registers: s3 = s and s11 = the shadow base as literals, s5 = fp + 20, s6 = fp + 28, s2 = the
   shadow address of f + 20 and s8 = the shadow address of f + 28 over the atoms 20 (fp) and 32. Regions: the
   notice's shadow bytes 4 .. 12 (base s9), the notice's bytes [p, p + 24) and [p + 48, p + 72) (base s10;
   [p + 24, p + 48) is the memset's), g_s's bytes s + 96 .. s + 116 (notify, notify_ctx, state) and their three
   shadow bytes, f's bytes f + 20 .. f + 48 (base s4) and their four shadow bytes (base 32). The alias fact names
   atom 32 as the shadow address of atom 20, for the checks of f + 32 and f + 40. *)
(* The shadow byte of g_s.notify (s + 96); s + 104 and s + 112 have the next two. *)
Definition ODN_GSH : Z := 2148220628.
Lemma ODN_GSH_eq : ODN_GSH = SHADOW_OFF + (ONDATA_S + 96) / 8.
Proof. reflexivity. Qed.
Definition ODN_R_sh : YP09.region := YP09.mkRegion (Some 25%nat) 4 13 4 13 [].
Definition ODN_R_p1 : YP09.region := YP09.mkRegion (Some 26%nat) 32 56 32 56 [].
Definition ODN_R_p2 : YP09.region := YP09.mkRegion (Some 26%nat) 80 104 80 104 [].
Definition ODN_R_gs : YP09.region :=
  YP09.mkRegion None (ONDATA_S + 96) (ONDATA_S + 116) 0 0
    [YP09.mkChunk (ONDATA_S + 96) (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk (ONDATA_S + 104) (YP09.CVal 8 (SOff 34 0));
     YP09.mkChunk (ONDATA_S + 112) (YP09.CVal 4 (SOff 35 0))].
Definition ODN_R_gsh : YP09.region :=
  YP09.mkRegion None ODN_GSH (ODN_GSH + 3) 0 0
    [YP09.mkChunk ODN_GSH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (ODN_GSH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (ODN_GSH + 2) (YP09.CVal 1 (SLit 0))].
Definition ODN_R_f : YP09.region :=
  YP09.mkRegion (Some 20%nat) 20 48 0 0
    [YP09.mkChunk 20 (YP09.CVal 4 (SOff 36 0)); YP09.mkChunk 28 (YP09.CVal 2 (SOff 37 0));
     YP09.mkChunk 32 (YP09.CVal 8 (SOff 38 0)); YP09.mkChunk 40 (YP09.CVal 8 (SOff 39 0))].
Definition ODN_R_fsh : YP09.region :=
  YP09.mkRegion (Some 32%nat) 2 6 0 0
    [YP09.mkChunk 2 (YP09.CVal 1 (SLit 0)); YP09.mkChunk 3 (YP09.CVal 1 (SLit 0));
     YP09.mkChunk 4 (YP09.CVal 1 (SLit 0)); YP09.mkChunk 5 (YP09.CVal 1 (SLit 0))].
Definition ODN_RS : smem := [ODN_R_sh; ODN_R_p1; ODN_R_p2; ODN_R_gs; ODN_R_gsh; ODN_R_f; ODN_R_fsh].
Definition ODN_F : facts :=
  mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 3); (25%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3);
           (26%nat, mkAF 4096 (2 ^ 47) 6)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SLit SHADOW_OFF), SOff 32 0)].
Definition ODN_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SLit ONDATA_S)) (Z_to_bv 5 27)
    (SLit SHADOW_OFF)) (Z_to_bv 5 21) (SOff 20 20)) (Z_to_bv 5 22) (SOff 20 28)) (Z_to_bv 5 18) (SOff 32 2))
    (Z_to_bv 5 24) (SOff 32 3).
Definition odn_ss : sstate := mkSS OD_NTC ODN_REGS ODN_RS None ODN_F.
Definition ODN_Bx : sv := SLit 0.
Definition ODN_B0 : Z * Z := (0, 0).
(* The valuation of the atoms 32 .. 39. *)
Definition odn_vals (sa n96 n104 st sd rt bp bl : Z) : list word :=
  [Z_to_bv 64 sa; Z_to_bv 64 n96; Z_to_bv 64 n104; Z_to_bv 64 st; Z_to_bv 64 sd; Z_to_bv 64 rt; Z_to_bv 64 bp;
   Z_to_bv 64 bl].

(* A region with no base, kept by a step that keeps its bytes' views and presence. *)
Lemma odn_rk_none : forall E H (m m2 : word -> option byte) lo hi wlo whi cs,
  (forall a, lo <= a < hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion None lo hi wlo whi cs).
Proof.
  intros E H m m2 lo hi wlo whi cs Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - apply (mbyte_of_aview tfibsegs). apply Hav. lia.
  - apply writable_kept. apply Hp.
Qed.

(* A one-byte chunk of the literal 0 reads 0: TransportGNoticeB.v chunks_zero_aview on a region's chunks. *)
Lemma odn_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  exact (chunks_zero_aview E H m (base_val E bopt) cs off Hcs Hin).
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma odn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac odn_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Section odn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition odn_E (regs : bvmap 5 word) (vs : list word) : env := Eimg (PI := PI_transportb) (Ereg regs vs).

(* A register pinned to a symbolic value it holds. *)
Lemma odn_pin : forall E ss ms (r : bv 5) e,
  st_ok_pi segs VAL E ss ms -> sv_denot E e = YK11.getr (ms_regs ms) r -> bv_eqb r 0 = false ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  apply (st_ok_regs segs E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
    (sr_set (ss_regs ss) r e) HS).
  intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
  - rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg segs E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
    rewrite <- Hq. exact Hr.
  - rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

Lemma odn_alias : forall E fp, bv_unsigned (ew E 20) = fp -> 0 <= fp < 2 ^ 47 ->
  bv_unsigned (ew E 32) = SHADOW_OFF + fp / 8 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SLit SHADOW_OFF)) = sv_denot E (SOff 32 0).
Proof.
  intros E fp H20 Hfp H32.
  rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SLit SHADOW_OFF)))).
  change (sv_denot E (SOff 32 0)) with (Z_to_bv 64 (bv_unsigned (ew E 32) + 0)). rewrite H32, Z.add_0_r. f_equal.
  change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SLit SHADOW_OFF)) = SHADOW_OFF + fp / 8).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, H20, Z.add_0_r.
  change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_pos fp 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound fp 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  change (U E (SLit SHADOW_OFF)) with (zcanon SHADOW_OFF).
  unfold SHADOW_OFF in *. rewrite (zcanon_id fp) by (unfold M64; lia). rewrite (zcanon_id (fp / 8)) by (unfold M64; lia).
  rewrite (zcanon_id 2147450880) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

End odn.

Section odn3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The symbolic state at +0x2ec with every register an atom, from the cut's memory. *)
Lemma odn_entry0 : forall ly S (W : world segs) (regs : bvmap 5 word) mem md F fp n96 n104 st sd rt bp bl,
  trans_ondata_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 25 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 26 = w64 F -> YK11.getr regs 20 = w64 fp ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= F) ->
  4096 <= fp -> fp mod 8 = 0 -> in_app fp 64 ->
  (fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp) ->
  (fp + 64 <= F \/ F + 256 <= fp) ->
  (forall a, F + 32 <= a < F + 56 -> apresent (w_H W) mem a) ->
  (forall a, F + 80 <= a < F + 104 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  0 <= n96 < 2 ^ 64 -> 0 <= n104 < 2 ^ 64 -> 0 <= st < 2 ^ 32 ->
  val_mem segs (mrestrict (w_H W) mem) (ONDATA_S + 96) 8 n96 ->
  val_mem segs (mrestrict (w_H W) mem) (ONDATA_S + 104) 8 n104 ->
  val_mem segs (mrestrict (w_H W) mem) (ONDATA_S + 112) 4 st ->
  0 <= sd < 2 ^ 32 -> 0 <= rt < 2 ^ 16 -> 0 <= bp < 2 ^ 64 -> 0 <= bl < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mem) (fp + 20) 4 sd -> val_mem segs (mrestrict (w_H W) mem) (fp + 28) 2 rt ->
  val_mem segs (mrestrict (w_H W) mem) (fp + 32) 8 bp -> val_mem segs (mrestrict (w_H W) mem) (fp + 40) 8 bl ->
  (forall i, 2 <= i < 6 -> aview segs (w_H W) mem (SHADOW_OFF + fp / 8 + i) = Some 0) ->
  st_ok_pi segs VAL (odn_E regs (odn_vals (SHADOW_OFF + fp / 8) n96 n104 st sd rt bp bl))
    (mkSS OD_NTC sr_atoms ODN_RS None ODN_F)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OD_NTC)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md F fp n96 n104 st sd rt bp bl HSC HAR R25 R26 R20 HF0 HF64 HFc HFapp HFG
    Hf0 Hf8 Hfapp HfG HfF HpF1 HpF2 HpSh Hn96 Hn104 Hst V96 V104 V112 Hsd Hrt Hbp Hbl Vsd Vrt Vbp Vbl Hfsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  pose proof (Z.div_mod fp 8 ltac:(lia)) as Dfp. rewrite Hf8, Z.add_0_r in Dfp.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  set (g := F / 64) in *. set (f8 := fp / 8) in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hfapp.
  set (sa := SHADOW_OFF + f8).
  set (E := odn_E regs (odn_vals sa n96 n104 st sd rt bp bl)).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, odn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
    by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U26 : bv_unsigned (ew E 26) = F)
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = fp)
    by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (odn_vals sa n96 n104 st sd rt bp bl) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, odn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
  cbn [Nat.add nth odn_vals] in E32, E33, E34, E35, E36, E37, E38, E39.
  assert (U32 : bv_unsigned (ew E 32) = sa)
    by (rewrite E32; apply unsigned_lit_small; unfold sa, SHADOW_OFF; lia).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, (j < 3)%nat -> val_mem segs (mrestrict (w_H W) mem) (ODN_GSH + Z.of_nat j) 1 0).
  { intros j Hj. apply odn_vm0.
    replace (ODN_GSH + Z.of_nat j) with (FCells.shadow_addr (ONDATA_S + 96 + 8 * Z.of_nat j)).
    - apply (decode_zshadow_rd B ly S W mem md ONDATA_S (ONDATA_S + TW.SZ_g_s) _ HAR); [| | | exact HSC].
      + unfold ONDATA_S, TB_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, ODN_GSH, ONDATA_S, TB_g_s.
      replace (6157888 + 96 + 8 * Z.of_nat j) with ((769748 + Z.of_nat j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ODN_RS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ODN_R_sh ODN_R_p1 ODN_R_p2 ODN_R_gs
        ODN_R_gsh ODN_R_f ODN_R_fsh base_val]; rewrite ?U25, ?U26, ?U20, ?U32.
    + (* the notice's shadow bytes 4 .. 12 *)
      split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply HpSh. lia.
    + (* [p, p + 24) *)
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply HpF1. lia.
    + (* [p + 48, p + 72) *)
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply HpF2. lia.
    + (* g_s's notify, notify_ctx, state *)
      split; [unfold ONDATA_S, TB_g_s; lia|]. split; [unfold ONDATA_S, TB_g_s; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (ONDATA_S + 96) 8 (SOff 33 0) n96); [apply DEN; [exact E33 | exact Hn96] | exact Hn96 | lia |].
        rewrite Z.add_0_l. exact V96.
      * apply (chunk_ok_val segs E _ 0 (ONDATA_S + 104) 8 (SOff 34 0) n104); [apply DEN; [exact E34 | exact Hn104] | exact Hn104 | lia |].
        rewrite Z.add_0_l. exact V104.
      * apply (chunk_ok_val segs E _ 0 (ONDATA_S + 112) 4 (SOff 35 0) st); [apply DEN; [exact E35 | lia] | exact Hst | lia |].
        rewrite Z.add_0_l. exact V112.
    + (* their shadow bytes *)
      split; [unfold ODN_GSH, SHADOW_OFF, ONDATA_S, TB_g_s; lia|]. split; [unfold ODN_GSH, SHADOW_OFF, ONDATA_S, TB_g_s; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 ODN_GSH 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0%nat ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (ODN_GSH + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 1%nat ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (ODN_GSH + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 2%nat ltac:(lia)).
    + (* f + 20 .. f + 48 *)
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ fp 20 4 (SOff 36 0) sd); [apply DEN; [exact E36 | lia] | exact Hsd | lia | exact Vsd].
      * apply (chunk_ok_val segs E _ fp 28 2 (SOff 37 0) rt); [apply DEN; [exact E37 | lia] | exact Hrt | lia | exact Vrt].
      * apply (chunk_ok_val segs E _ fp 32 8 (SOff 38 0) bp); [apply DEN; [exact E38 | exact Hbp] | exact Hbp | lia | exact Vbp].
      * apply (chunk_ok_val segs E _ fp 40 8 (SOff 39 0) bl); [apply DEN; [exact E39 | exact Hbl] | exact Hbl | lia | exact Vbl].
    + (* their four shadow bytes *)
      split; [unfold sa, SHADOW_OFF; lia|]. split; [unfold sa, SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
        (apply (chunk_ok_val segs E _ sa _ 1 (SLit 0) 0); [reflexivity | lia | lia |]); apply odn_vm0;
        unfold sa; apply Hfsh; lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, ODN_RS, ODN_R_sh, ODN_R_p1, ODN_R_p2, ODN_R_gs, ODN_R_gsh, ODN_R_f, ODN_R_fsh.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U25, U26, U20, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold sa, ODN_GSH, SHADOW_OFF, ONDATA_S, TB_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold ODN_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25, U26, U20.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * g) with ((268431360 + g) * 8) by ring.
      apply Z.mod_mul. lia. }
    split; [|split; [exact I |]].
    + unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + split; [|exact I]. apply (odn_alias E fp U20 ltac:(lia)). rewrite U32. reflexivity.
Qed.

(* The symbolic state odn_ss at +0x2ec: odn_entry0 with s3, s11, s5, s6, s2 and s8 pinned. *)
Lemma odn_entry : forall ly S (W : world segs) (regs : bvmap 5 word) mem md F fp n96 n104 st sd rt bp bl,
  trans_ondata_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 25 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 26 = w64 F -> YK11.getr regs 20 = w64 fp ->
  YK11.getr regs 19 = w64 ONDATA_S -> YK11.getr regs 27 = w64 SHADOW_OFF ->
  YK11.getr regs 21 = w64 (fp + 20) -> YK11.getr regs 22 = w64 (fp + 28) ->
  YK11.getr regs 18 = w64 (SHADOW_OFF + (fp + 20) / 8) -> YK11.getr regs 24 = w64 (SHADOW_OFF + (fp + 28) / 8) ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= 2 ^ 47 -> in_app F 256 ->
  (F + 256 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= F) ->
  4096 <= fp -> fp mod 8 = 0 -> in_app fp 64 ->
  (fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp) ->
  (fp + 64 <= F \/ F + 256 <= fp) ->
  (forall a, F + 32 <= a < F + 56 -> apresent (w_H W) mem a) ->
  (forall a, F + 80 <= a < F + 104 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  0 <= n96 < 2 ^ 64 -> 0 <= n104 < 2 ^ 64 -> 0 <= st < 2 ^ 32 ->
  val_mem segs (mrestrict (w_H W) mem) (ONDATA_S + 96) 8 n96 ->
  val_mem segs (mrestrict (w_H W) mem) (ONDATA_S + 104) 8 n104 ->
  val_mem segs (mrestrict (w_H W) mem) (ONDATA_S + 112) 4 st ->
  0 <= sd < 2 ^ 32 -> 0 <= rt < 2 ^ 16 -> 0 <= bp < 2 ^ 64 -> 0 <= bl < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mem) (fp + 20) 4 sd -> val_mem segs (mrestrict (w_H W) mem) (fp + 28) 2 rt ->
  val_mem segs (mrestrict (w_H W) mem) (fp + 32) 8 bp -> val_mem segs (mrestrict (w_H W) mem) (fp + 40) 8 bl ->
  (forall i, 2 <= i < 6 -> aview segs (w_H W) mem (SHADOW_OFF + fp / 8 + i) = Some 0) ->
  st_ok_pi segs VAL (odn_E regs (odn_vals (SHADOW_OFF + fp / 8) n96 n104 st sd rt bp bl)) odn_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OD_NTC)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md F fp n96 n104 st sd rt bp bl HSC HAR R25 R26 R20 R19 R27 R21 R22 R18 R24 HF0 HF64 HFc
    HFapp HFG Hf0 Hf8 Hfapp HfG HfF HpF1 HpF2 HpSh Hn96 Hn104 Hst V96 V104 V112 Hsd Hrt Hbp Hbl Vsd Vrt Vbp Vbl Hfsh.
  rewrite restrict_mkst_fx.
  pose proof (odn_entry0 ly S W regs mem md F fp n96 n104 st sd rt bp bl HSC HAR R25 R26 R20 HF0 HF64 HFc HFapp
    HFG Hf0 Hf8 Hfapp HfG HfF HpF1 HpF2 HpSh Hn96 Hn104 Hst V96 V104 V112 Hsd Hrt Hbp Hbl Vsd Vrt Vbp Vbl Hfsh) as H0.
  set (E := odn_E regs (odn_vals (SHADOW_OFF + fp / 8) n96 n104 st sd rt bp bl)) in H0 |- *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, odn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U20 : bv_unsigned (ew E 20) = fp)
    by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + fp / 8).
  { unfold E, odn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regs (odn_vals (SHADOW_OFF + fp / 8) n96 n104 st sd rt bp bl) 0) as X.
    cbn [Nat.add nth odn_vals] in X. rewrite X. apply unsigned_lit_small.
    pose proof (Z.div_pos fp 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound fp 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
    unfold SHADOW_OFF. lia. }
  assert (E20 : (fp + 20) / 8 = fp / 8 + 2).
  { pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hf8, Z.add_0_r in D.
    symmetry. apply Z.div_unique with (r := 4); lia. }
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 19) ONDATA_S H0 R19 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 27) SHADOW_OFF H1 R27 eq_refl) as H2.
  pose proof (odn_pin _ _ _ (Z_to_bv 5 21) (SOff 20 20) H2
    ltac:(cbn [sv_denot ms_regs YK11.mkst]; rewrite U20; exact (eq_sym R21)) eq_refl) as H3.
  pose proof (odn_pin _ _ _ (Z_to_bv 5 22) (SOff 20 28) H3
    ltac:(cbn [sv_denot ms_regs YK11.mkst]; rewrite U20; exact (eq_sym R22)) eq_refl) as H4.
  pose proof (odn_pin _ _ _ (Z_to_bv 5 18) (SOff 32 2) H4
    ltac:(cbn [sv_denot ms_regs YK11.mkst]; rewrite U32; refine (eq_trans _ (eq_sym R18)); unfold w64;
          rewrite E20; f_equal; lia) eq_refl) as H5.
  assert (E28 : (fp + 28) / 8 = fp / 8 + 3).
  { pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite Hf8, Z.add_0_r in D.
    symmetry. apply Z.div_unique with (r := 4); lia. }
  pose proof (odn_pin _ _ _ (Z_to_bv 5 24) (SOff 32 3) H5
    ltac:(cbn [sv_denot ms_regs YK11.mkst]; rewrite U32; refine (eq_trans _ (eq_sym R24)); unfold w64;
          rewrite E28; f_equal; lia) eq_refl) as H6.
  exact H6.
Qed.

End odn3.

(* ------------------------------------------------------------------ *)
(* 5. The written range ondata_wr: bytes of G                          *)
(* ------------------------------------------------------------------ *)

Lemma odn_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
  intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* g_s's and io_send's fields by their rows of TMAP_B; notice's stores by TransportGNoticeB.v notice_wr_G. *)
Lemma odn_wr_G : forall Bw b a, ondata_wr Bw b a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw b a H. unfold ondata_wr, iosend_wr, twb_fld in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
    try (apply (odn_inG_row _ _ _ a TMAP_B_g_s);
         unfold TW.A_S_stats_tx_frames, TW.A_S_stats_tx_acks, TW.A_S_stats_rx_data, TW.A_S_stats_rx_desk_retries,
           TW.A_S_backoff_until_us, TW.A_S_stats_rx_duplicates, TW.A_S_desk_counter, TW.A_S_desk_counter_valid,
           TW.OFF_g_s, TW.SZ_g_s in *; lia).
  - destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(s & Hs & H)|[H|H]]]]]]]]]]]]]]]]]].
    + apply (odn_inG_row _ _ _ a TMAP_B_g_fail_next). lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_GOT). unfold TW.A_GOT_e2, TW.OFF_GOT, TW.SZ_GOT in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_GOT). unfold TW.A_GOT_e3, TW.OFF_GOT, TW.SZ_GOT in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_GOT). unfold TW.A_GOT_acks, TW.OFF_GOT, TW.SZ_GOT in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_g_last_counter). unfold TW.SZ_g_last_counter in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_host_counter, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_next_ka, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_last_display, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_display_sent, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_fly_on, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_fly_cmd, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_fly_counter, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_fly_retries, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_fly_sent, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M). unfold TW.A_M_fly_len, TW.OFF_M, TW.SZ_M in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_M).
      unfold TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME, SENDCTL_F in *. lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_g_cmd). unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TC.CMDS_MAX in *.
      lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_g_q). lia.
    + apply (odn_inG_row _ _ _ a TMAP_B_g_nq). lia.
  - exact (notice_wr_G Bw _ a H).
Qed.

(* A value read through the view at one memory is read at another that shows the same bytes. *)
Lemma odn_vm_tr : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H' m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview tfibsegs H H' m m' (a + Z.of_nat k)).
  - exact (Hv k Hkn).
  - apply Hk. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The piece                                                        *)
(* ------------------------------------------------------------------ *)
(* A frame in application memory lies apart from its own shadow bytes. *)
Lemma odn_shf {rc : YM05.RunCeil} : forall F, in_app F 256 -> SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8.
Proof.
  intros F HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
  destruct HFapp as (H0 & [HL | (HH1 & HH2)]); [right | left]; unfold SHADOW_OFF; lia.
Qed.

(* The bytes the piece may change between the cut and the call of notice: the notice's shadow bytes 4 .. 12, the
   notice's 72 bytes, and the stack window of __asan_memset below sp1. *)
Definition odn_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13) \/ (F + 32 <= x < F + 104) \/ (sp1 - ESTACK <= x < sp1).

(* Where the bytes the walk reads lie with respect to the bytes it may change. *)
Lemma odn_out {rc : YM05.RunCeil} : forall F fp sp1,
  4096 <= F -> F mod 64 = 0 -> in_app F 256 -> F + 256 <= alloc_ceiling ->
  (F + 256 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= F) ->
  4096 <= fp -> fp + 64 <= alloc_ceiling -> in_app fp 64 -> (fp + 64 <= F \/ F + 256 <= fp) ->
  alloc_ceiling <= sp1 - ESTACK ->
  (forall a, ONDATA_S + 96 <= a < ONDATA_S + 116 -> 0 <= a < 2 ^ 64 /\ ~ odn_Z F sp1 a) /\
  (forall a, ODN_GSH <= a < ODN_GSH + 3 -> 0 <= a < 2 ^ 64 /\ ~ odn_Z F sp1 a) /\
  (forall a, fp + 20 <= a < fp + 48 -> 0 <= a < 2 ^ 64 /\ ~ odn_Z F sp1 a) /\
  (forall a, SHADOW_OFF + fp / 8 + 2 <= a < SHADOW_OFF + fp / 8 + 6 -> 0 <= a < 2 ^ 64 /\ ~ odn_Z F sp1 a) /\
  (forall a, sp1 <= a < 2 ^ 47 -> 0 <= a < 2 ^ 64 /\ ~ odn_Z F sp1 a) /\
  (forall a, F + 248 <= a < F + 256 -> 0 <= a < 2 ^ 64 /\ ~ odn_Z F sp1 a) /\
  (forall a, SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 13 ->
     0 <= a < 2 ^ 64 /\ ~ (F + 56 <= a < F + 56 + 24) /\ ~ (sp1 - ESTACK <= a < sp1)) /\
  (forall a, (F + 32 <= a < F + 56 \/ F + 80 <= a < F + 104) ->
     0 <= a < 2 ^ 64 /\ ~ (F + 56 <= a < F + 56 + 24) /\ ~ (sp1 - ESTACK <= a < sp1)) /\
  (forall a, 0 <= a < kLowMemEnd -> ~ (F + 32 <= a < F + 104) -> ~ odn_Z F sp1 a).
Proof.
  intros F fp sp1 HF0 HF64 HFapp HFc HFG Hf0 Hfc Hfapp HfF Hsp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold kLowMemEnd in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hfapp.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
  pose proof (Z.div_mod fp 8 ltac:(lia)) as Df. pose proof (Z.mod_pos_bound fp 8 ltac:(lia)) as Mf.
  set (q := F / 8) in *. set (qf := fp / 8) in *.
  unfold odn_Z, ODN_GSH, ONDATA_S, TB_g_s, TW.SZ_g_s, SHADOW_OFF, ESTACK in *.
  split; [intros a Ha; lia|]. split; [intros a Ha; lia|]. split; [intros a Ha; lia|].
  split; [intros a Ha; lia|]. split; [intros a Ha; lia|]. split; [intros a Ha; lia|].
  split; [intros a Ha; lia|]. split; [intros a Ha; lia|]. intros a Ha Hf; lia.
Qed.

(* The bytes the walk may change are in the call's stack window, the own frame (its bytes, its shadow) or G. *)
Lemma odn_Z_in : forall F FL sp1 spr a, spr - ONDATA_STK <= sp1 - ESTACK -> sp1 <= spr ->
  odn_Z F sp1 a -> (spr - ONDATA_STK <= a < spr) \/ dkg_nf ONDATA_CID F FL a \/ inG TG.G_HARNESS_B a.
Proof.
  intros F FL sp1 spr a H1 H2 [Hz | [Hz | Hz]].
  - right; left; right; left. change (fs_frame_bytes ONDATA_CID / 8) with 32. lia.
  - right; left; left. change (fs_frame_bytes ONDATA_CID) with 256. lia.
  - left; lia.
Qed.

(* A byte outside the bytes the walk may change is outside the memset's destination and stack window. *)
Ltac odn_eff HeffM Hr Hn :=
  apply HeffM; [exact Hr | let Hd := fresh "Hd" in intros Hd; apply Hn; right; left; clear - Hd; lia
               | let Hd := fresh "Hd" in intros Hd; apply Hn; right; right; clear - Hd; lia].

(* The low bytes of the registers the code stored: an atom, its 32-bit and 16-bit sign extensions. *)
Lemma odn_off_val : forall E n v (w : N), ew E n = Z_to_bv 64 v -> (w <= 8)%N ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w).
Proof.
  intros E n v w Hn Hw. cbn [sv_denot]. rewrite Hn, Z.add_0_r.
  rewrite (Z_to_bv_unsigned 64 (bv_unsigned (Z_to_bv 64 v))), Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia).
Qed.
Lemma odn_lw_val : forall E n v, ew E n = Z_to_bv 64 v ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ (8 * Z.of_N 4) = v mod 2 ^ (8 * Z.of_N 4).
Proof.
  intros E n v Hn. cbn [sv_denot]. rewrite YK11.b_lw_val. unfold YK11.v_lw.
  pose proof (odn_lit_mod (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (ew E n) + 0)))) 4 ltac:(lia)) as L.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ Z.of_N 32) in L. change (2 ^ (8 * Z.of_N 4)) with (2 ^ Z.of_N 32).
  rewrite L, odn_swrap_mod by lia. change (2 ^ Z.of_N 32) with (2 ^ (8 * Z.of_N 4)).
  exact (odn_off_val E n v 4 Hn ltac:(lia)).
Qed.
Lemma odn_lh_val : forall E n v, ew E n = Z_to_bv 64 v ->
  bv_unsigned (sv_denot E (SExt true 16 (SOff n 0))) mod 2 ^ (8 * Z.of_N 2) = v mod 2 ^ (8 * Z.of_N 2).
Proof.
  intros E n v Hn. cbn [sv_denot]. rewrite YK11.b_lh_val. unfold YK11.v_lh.
  pose proof (odn_lit_mod (bv_swrap 16 (bv_unsigned (Z_to_bv 64 (bv_unsigned (ew E n) + 0)))) 2 ltac:(lia)) as L.
  change (2 ^ (8 * Z.of_nat 2)) with (2 ^ Z.of_N 16) in L. change (2 ^ (8 * Z.of_N 2)) with (2 ^ Z.of_N 16).
  rewrite L, odn_swrap_mod by lia. change (2 ^ Z.of_N 16) with (2 ^ (8 * Z.of_N 2)).
  exact (odn_off_val E n v 2 Hn ltac:(lia)).
Qed.

(* The value of the chunk at offset off of a region, read from the region's region_ok RS, as val_mem. *)
Ltac odn_cv RS off w e H :=
  pose proof (odn_chunk_val _ _ _ _ _ _ _ _ _ off w e RS ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(lia)) as H.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac odn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "odn_reg: no match for" T; fail
  end.

(* The write rights of a run from a state with the regions of odn_ss (U25 / U26: the bases' values; EF2: the frame's
   address F = frame_addr ly2 ONDATA_CID pos): the notice's shadow bytes and its bytes [p, p + 24), [p + 48, p + 72)
   are bytes of the frame the journal owns; the other five regions have no writable byte. *)
Ltac odn_awr U25 U26 EF2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONDATA_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes ONDATA_CID / 8) with 32; lia |];
  eapply awr_ok_x_cons_own with (cid := ONDATA_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U26 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes ONDATA_CID) with 256; lia |];
  eapply awr_ok_x_cons_own with (cid := ONDATA_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U26 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes ONDATA_CID) with 256; lia |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.


Section odnm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma odn_main : @od_ntc_stmt fx rc B MT.
Proof.
unfold od_ntc_stmt. intros NC. unfold od_ntc_at.
intros LAWS0 CALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B1 r f ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HODC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof CALL as (CSM & CSC & CKA & CMS & CNT).
pose proof HFIX as (HPRE & HTFG & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HPRE as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf0 &
  Hm & HTF & Hrom & Hap & Hfly & Hcmd & Hsrc & Hcnt & Hev).
pose proof HCUR as ((HC0 & Hs24 & HSC & Htw2 & Hgf1 & Hdup) & Hka).
pose proof HC0 as (HJ1 & He & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R25 & R26) & R18 & R19 & R20 & R21 & R27) & R22 & R24).
pose proof HDF as (Hcode & Hbuf0 & Hbg8 & Hbsrc & Hboff & HbnG & Hfp0 & Hfp8 & Hfj & Hfg8 & Hffake & Hfrd & Hfoff).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold OD_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HOS : ONDATA_STK = 8832) by reflexivity.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold ONDATA_FRAME.
  pose proof (Z.div_mod (spZ regs - 160) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 160) / 32) in *. set (rr := (spZ regs - 160) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EF2 : frame_addr ly2 ONDATA_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite EF2 in HFb, HFsh.
change (fs_frame_bytes ONDATA_CID) with 256 in HFb. change (fs_frame_bytes ONDATA_CID / 8) with 32 in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
set (FL := flag_addr lyc ONDATA_CID pos) in *.
assert (HgsG : forall x, ONDATA_S <= x < ONDATA_S + TW.SZ_g_s -> inG TG.G_HARNESS_B x)
  by (intros x Hx; apply (odn_inG_row _ _ _ x TMAP_B_g_s); unfold ONDATA_S in Hx; lia).
assert (HFG : F + 256 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) ONDATA_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONDATA_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 256 /\ ONDATA_S <= x < ONDATA_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F ONDATA_S) as [h3|h3]; [exists ONDATA_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos x HAR2 Hin);
    [rewrite EF2; change (fs_frame_bytes ONDATA_CID) with 256; lia|].
  exact (trans_g_img x (HgsG x Hx2)). }
(* f: the caller's frame that holds it, its separation from the own frame and from g_s *)
destruct Hffake as (cf & pf & Hinf & Hf1 & Hf2). unfold FRAME_F_SIZE in Hf2.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cf pf HARc Hinf) as (Hfa0 & Hfac & Hfaapp).
assert (Hfapp : in_app fp 64) by (apply (in_app_sub _ _ _ _ Hfaapp); lia).
assert (HfF : fp + 64 <= F \/ F + 256 <= fp).
{ pose proof (dkg_own_sep segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos Sc cf pf HAR2 Hfrs Hinf) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF2 in Hd.
  assert (Efa : frame_addr ly2 cf pf = frame_addr lyc cf pf) by (unfold frame_addr; rewrite HlyF; reflexivity).
  rewrite Efa in Hd. change (fs_frame_bytes ONDATA_CID) with 256 in Hd. lia. }
assert (HfG : fp + 64 <= ONDATA_S \/ ONDATA_S + TW.SZ_g_s <= fp).
{ destruct (Z_le_gt_dec (fp + 64) ONDATA_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONDATA_S + TW.SZ_g_s) fp) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, fp <= x < fp + 64 /\ ONDATA_S <= x < ONDATA_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec fp ONDATA_S) as [h3|h3]; [exists ONDATA_S | exists fp]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc Sc W memc mdc cf pf x HARc Hinf); [lia|].
  exact (trans_g_img x (HgsG x Hx2)). }
(* f's bytes and their shadow at the cut's memory are those at the call's entry *)
assert (KF : forall a, (fp <= a < fp + 64 \/ SHADOW_OFF + fp / 8 <= a < SHADOW_OFF + fp / 8 + 8) ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a Ha. pose proof HK as (_ & _ & _ & K4 & _).
  pose proof (dkg_frame_al64 segs B lyc Sc W memc mdc cf pf HARc Hinf) as (A64 & As64 & As).
  apply (K4 cf pf a Hinf).
  - destruct Ha as [Ha | Ha]; [left; unfold in_zr, frame_rng; cbn [fst snd]; lia |].
    right. unfold in_zr, shadow_addr. cbn [fst snd].
    pose proof (Z.div_mod (frame_addr lyc cf pf) 64 ltac:(lia)) as D. rewrite A64, Z.add_0_r in D.
    pose proof (Z.div_mod (fs_frame_bytes cf) 64 ltac:(lia)) as Ds. rewrite As64, Z.add_0_r in Ds.
    assert (E1 : frame_addr lyc cf pf / 8 = 8 * (frame_addr lyc cf pf / 64))
      by (rewrite D at 1; replace (64 * (frame_addr lyc cf pf / 64)) with ((8 * (frame_addr lyc cf pf / 64)) * 8) by ring;
          apply Z.div_mul; lia).
    assert (E2 : fs_frame_bytes cf / 8 = 8 * (fs_frame_bytes cf / 64))
      by (rewrite Ds at 1; replace (64 * (fs_frame_bytes cf / 64)) with ((8 * (fs_frame_bytes cf / 64)) * 8) by ring;
          apply Z.div_mul; lia).
    pose proof (Z.div_mod fp 8 ltac:(lia)) as Df. rewrite Hfp8, Z.add_0_r in Df.
    lia.
  - intros Hw. pose proof (odn_wr_G Bw b a Hw) as Hg. pose proof (inG_low segs B transportb_segs_low _ a HGX Hg) as Hl.
    unfold kLowMemEnd in Hl. destruct Ha as [Ha | Ha]; [| unfold SHADOW_OFF in Ha; lia].
    exact (frm_img segs B LAWS lyc Sc W memc mdc cf pf a HARc Hinf ltac:(lia) (trans_g_img a Hg)). }
destruct (odn_ff (mrestrict (w_H W) memc) fp buf b fj Hcode Hfj Hfg8) as (Vsd0 & Vrt0 & Vbp0 & Vbl0).
assert (VF : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 64 ->
  val_mem segs (mrestrict (w_H W) memc) (fp + o) n v -> val_mem segs (mrestrict (w_H W2) mem2) (fp + o) n v)
  by (intros o n v Ho Hn Hv; apply (odn_vm_tr (w_H W) (w_H W2) memc mem2 (fp + o) n v); [|exact Hv];
      intros i Hi; apply KF; left; lia).
pose proof (VF 20 4%nat _ ltac:(lia) ltac:(cbn; lia) Vsd0) as Vsd.
pose proof (VF 28 2%nat _ ltac:(lia) ltac:(cbn; lia) Vrt0) as Vrt.
pose proof (VF 32 8%nat _ ltac:(lia) ltac:(cbn; lia) Vbp0) as Vbp.
pose proof (VF 40 8%nat _ ltac:(lia) ltac:(cbn; lia) Vbl0) as Vbl.
assert (ZF : forall i, 0 <= i < 8 -> aview segs (w_H W2) mem2 (SHADOW_OFF + fp / 8 + i) = Some 0).
{ intros i Hi. rewrite KF by (right; lia).
  pose proof Hfrd as (_ & Hra8 & _).
  destruct (Hra8 (fp + 8 * i + 7) ltac:(unfold FRAME_F_SIZE; lia)) as (s & Hs & Hok).
  pose proof (Z.div_mod fp 8 ltac:(lia)) as Df. rewrite Hfp8, Z.add_0_r in Df.
  assert (Ex : shadow_of_addr SHADOW_OFF (fp + 8 * i + 7) = SHADOW_OFF + fp / 8 + i).
  { unfold shadow_of_addr. replace (fp + 8 * i + 7) with ((fp / 8 + i) * 8 + 7) by lia.
    rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  rewrite Ex in Hs. rewrite Hs. f_equal.
  destruct Hok as [Hok | (Hok1 & Hok2)]; [exact Hok|].
  replace (fp + 8 * i + 7) with (7 + (fp / 8 + i) * 8) in Hok1 by lia. rewrite Z.mod_add in Hok1 by lia.
  change (7 mod 8) with 7 in Hok1. lia. }
destruct (odn_fr_ranges b Hcode) as (Hsd & Hrt & Hbl & Hlb).
assert (Hbp : 0 <= buf + 30 < 2 ^ 64).
{ destruct (trans_src_ok_rd B LAWS lyc Sc W memc mdc buf (Z.of_nat (length b)) HARc Hbsrc ltac:(lia))
    as (_ & _ & _ & _ & _ & Hb63). lia. }
(* g_s's notify, notify_ctx and state at the world ondata_w3 (ondata_w2 B1 b r now) b *)
set (w3 := ondata_w3 (ondata_w2 B1 b r now) b) in *.
pose proof (tw_read_val segs _ TMAP_B w3 TW.OFF_g_s TB_g_s TW.SZ_g_s 96 8 TMAP_B_ok Htw2 TMAP_B_g_s
  ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as V96.
pose proof (tw_read_val segs _ TMAP_B w3 TW.OFF_g_s TB_g_s TW.SZ_g_s 104 8 TMAP_B_ok Htw2 TMAP_B_g_s
  ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as V104.
pose proof (tw_read_val segs _ TMAP_B w3 TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw2 TMAP_B_g_s
  ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as V112.
pose proof (TWL.u_at_range w3 (TW.OFF_g_s + 96) 8) as R96.
pose proof (TWL.u_at_range w3 (TW.OFF_g_s + 104) 8) as R104.
pose proof (TWL.u_at_range w3 (TW.OFF_g_s + 112) 4) as R112.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R96, R104. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R112.
set (n96 := TW.u_at w3 (TW.OFF_g_s + 96) 8) in *. set (n104 := TW.u_at w3 (TW.OFF_g_s + 104) 8) in *.
set (st := TW.u_at w3 (TW.OFF_g_s + 112) 4) in *.
(* +0x2ec: the symbolic state at the cut *)
pose proof (odn_entry B ly2 S2 W2 regs2 mem2 md2 F fp n96 n104 st (DSpec.fr_send b) (DSpec.fr_retry b) (buf + 30)
  (DSpec.fr_body_len b) HODC HAR2 R25 R26 R20 R19 R27 R21 R22 R18 R24 HF0 HF64 ltac:(lia) HFapp HFG ltac:(lia) Hfp8
  Hfapp HfG HfF
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i ltac:(lia))))
  R96 R104 R112 V96 V104 V112 Hsd Hrt Hbp ltac:(lia) Vsd Vrt Vbp Vbl
  ltac:(intros i Hi; exact (ZF i ltac:(lia)))) as HS.
set (E0 := odn_E regs2 (odn_vals (SHADOW_OFF + fp / 8) n96 n104 st (DSpec.fr_send b) (DSpec.fr_retry b) (buf + 30)
  (DSpec.fr_body_len b))) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, odn_E; apply Eimg_env).
assert (EE : forall n (rg : bv 5), Z.of_nat n = bv_unsigned rg -> ew E0 n = YK11.getr regs2 rg)
  by (intros n rg Hn; unfold E0, odn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (U25 : bv_unsigned (ew E0 25) = SHADOW_OFF + F / 8)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U26 : bv_unsigned (ew E0 26) = F)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E0 20) = fp)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (E0x : forall j, (j < 8)%nat -> ew E0 (32 + j) =
  nth j (odn_vals (SHADOW_OFF + fp / 8) n96 n104 st (DSpec.fr_send b) (DSpec.fr_retry b) (buf + 30)
    (DSpec.fr_body_len b)) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, odn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (E0x 0%nat ltac:(lia)) as E032. pose proof (E0x 1%nat ltac:(lia)) as E033.
pose proof (E0x 3%nat ltac:(lia)) as E035. pose proof (E0x 4%nat ltac:(lia)) as E036.
pose proof (E0x 5%nat ltac:(lia)) as E037. pose proof (E0x 6%nat ltac:(lia)) as E038.
pose proof (E0x 7%nat ltac:(lia)) as E039.
cbn [Nat.add nth odn_vals] in E032, E033, E035, E036, E037, E038, E039. clear E0x.
assert (U32 : bv_unsigned (ew E0 32) = SHADOW_OFF + fp / 8).
{ rewrite E032. apply unsigned_lit_small.
  pose proof (Z.div_pos fp 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound fp 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF. lia. }
assert (HACE : alloc_ceiling <= sp1 - ESTACK) by lia.
destruct (odn_out F fp sp1 HF0 HF64 HFapp HFc HFG ltac:(lia) ltac:(lia) Hfapp HfF HACE)
  as (OGS & OGSH & OF & OFSH & OHI & OFL & OSHM & OPM & OLOW).
assert (SHOK : sh_ok segs ODN_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
(* +0x2ec .. +0x34c: s7 = p, shadow bytes 4 .. 12 := 0, the stores at p .. p + 24, the checked load of S_state, the
   memset's arguments, `jal __asan_memset` *)
paj_run_tok RUN HS HJ1 SHOK ODN_B0.
{ odn_awr U25 U26 EF2. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8) by exact (odn_shf F HFapp).
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ odn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (odn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros bb wlo whi x Hiw Hx. cbv beta.
  odn_win Hiw Hx ltac:(rewrite ?U25, ?U26 in Hx; unfold odn_Z;
    first [lia | left; lia | right; left; lia | right; right; lia]). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (ZS1 : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U25.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (odn_chunk0 E0 (w_H W2) (ms_mem ms) (Some 25%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear HF HFr HG RG0.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 ONDATA_CID pos HAR1 Hin) as (_ & _ & HFb1 & HFsh1).
rewrite EF2, ESH in HFsh1. change (fs_frame_bytes ONDATA_CID / 8) with 32 in HFsh1.
pmkst HS.
odn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 56)) Q10 ltac:(cbn [sv_denot]; rewrite U26; reflexivity).
odn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
odn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 24) Q12 ltac:(reflexivity).
odn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
odn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 31480)) Q1 ltac:(apply codeptr_val; exact HEI).
odn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
odn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* +0x34c: __asan_memset (p + 24, 0, 24), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet (transportb_sigma TB___asan_memset)
    (CMS fx) TG.G_HARNESS_B W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONDATA_CID, pos) :: own) ly2 S2
    md1 (k + e) (F + 56) 0 24 (sp1 - sp0) (Z_to_bv 64 (BASE + 31480)) HGX G_HARNESS_B_rw HJ1 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    destruct Hsp1 as (_ & M1). rewrite M1, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONDATA_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes ONDATA_CID) with 256. lia.
    + lia.
  - apply (amem_range_sub_app F 256); [exact HFapp | lia | lia | lia | lia].
  - apply (TGNA.frame_ra_zero _ F (F + 56) 24 7 10); [lia | exact DFm8 | lia | lia |].
    intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TGNA.frame_hull_vis _ F 256 (F + 56) 24); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros Wm c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ odn_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right. left. lia.
  - intros Hd. apply Hn. right. right. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a) by (intros a Ha; exact (HgrM a (GA1 a Ha))).
assert (ZMM : forall a, F + 56 <= a < F + 80 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 56) + (a - (F + 56))) by lia. rewrite (HsetM (a - (F + 56)) ltac:(lia)). reflexivity. }
(* after the memset: the seven regions are kept (none meets [p + 24, p + 48) or the memset's stack window) *)
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat]
  HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 25%nat (SHADOW_OFF + F / 8)); [exact U25 | | exact HgrM].
    intros a Ha. destruct (OSHM a ltac:(clear - Ha; lia)) as (Hr & N1 & N2).
    apply HeffM; [exact Hr | exact N1 | intros Hd; apply N2; clear - Hd; lia].
  - apply (region_kept_aview _ _ _ _ 26%nat F); [exact U26 | | exact HgrM].
    intros a Ha. destruct (OPM a ltac:(clear - Ha; lia)) as (Hr & N1 & N2).
    apply HeffM; [exact Hr | exact N1 | intros Hd; apply N2; clear - Hd; lia].
  - apply (region_kept_aview _ _ _ _ 26%nat F); [exact U26 | | exact HgrM].
    intros a Ha. destruct (OPM a ltac:(clear - Ha; lia)) as (Hr & N1 & N2).
    apply HeffM; [exact Hr | exact N1 | intros Hd; apply N2; clear - Hd; lia].
  - apply odn_rk_none; [| exact HgrM]. intros a Ha.
    destruct (OGS a ltac:(unfold ONDATA_S, TB_g_s; clear - Ha; lia)) as (Hr & Hn). odn_eff HeffM Hr Hn.
  - apply odn_rk_none; [| exact HgrM]. intros a Ha.
    destruct (OGSH a ltac:(unfold ODN_GSH; clear - Ha; lia)) as (Hr & Hn). odn_eff HeffM Hr Hn.
  - apply (region_kept_aview _ _ _ _ 20%nat fp); [exact U20 | | exact HgrM].
    intros a Ha. destruct (OF a ltac:(clear - Ha; lia)) as (Hr & Hn). odn_eff HeffM Hr Hn.
  - apply (region_kept_aview _ _ _ _ 32%nat (SHADOW_OFF + fp / 8)); [exact U32 | | exact HgrM].
    intros a Ha. destruct (OFSH a ltac:(clear - Ha; lia)) as (Hr & Hn). odn_eff HeffM Hr Hn. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U25b : bv_unsigned (ew E1 25) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U25).
assert (U26b : bv_unsigned (ew E1 26) = F) by (rewrite E1lo by lia; exact U26).
assert (SHOK1 : sh_ok segs ODN_Bx (@nil shent) E1 (mrestrict (w_H W2) memM)) by constructor.
clear dependent ms.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUNTO.
(* +0x350 .. +0x3dc: the checked loads of f + 32, f + 40, f + 20, f + 28 (its shadow byte through s8) and their stores
   into the notice, the checked loads of s + 96 and s + 104, a1 = p, up to `jalr a2` *)
paj_run_to_tok RUNTO HS HJ2 SHOK1 ODN_B0 OD_NC.
{ odn_awr U25b U26b EF2. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ odn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (odn_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros bb wlo whi x Hiw Hx. cbv beta.
  odn_win Hiw Hx ltac:(rewrite ?U25b, ?U26b in Hx; unfold odn_Z;
    first [lia | left; lia | right; left; lia | right; right; lia]). }
assert (ZMN : forall a, F + 56 <= a < F + 80 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (F + 32 <= x < F + 56) \/ (F + 80 <= x < F + 104) \/
    (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 13)) HFr); [| clear - Ha HFc HF0 C1; lia |].
  - intros bb wlo whi x Hiw Hx. cbv beta.
    odn_win Hiw Hx ltac:(rewrite ?U25b, ?U26b in Hx; first [lia | left; lia | right; left; lia | right; right; lia]).
  - cbv beta. intros [Hx | [Hx | Hx]]; [clear - Ha Hx; lia | clear - Ha Hx; lia | clear - Ha Hx HSHF; destruct HSHF; lia]. }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ odn_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
clear HF HFr HG.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
cbn [ms_mem restrict] in RS0, RS1, RS2.
(* the notice's shadow bytes 4 .. 12 and its 72 bytes at p *)
assert (ZSN : forall i, 4 <= i < 13 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U25b.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (odn_chunk0 E1 (w_H W2) (ms_mem ms) (Some 25%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
assert (E1v : forall n v, (n < 1024)%nat -> ew E0 n = Z_to_bv 64 v -> ew E1 n = Z_to_bv 64 v)
  by (intros n v Hn H; rewrite E1lo by exact Hn; exact H).
assert (E120 : ew E1 20 = Z_to_bv 64 fp)
  by (rewrite E1lo by lia; rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
odn_cv RS1 32 4%N (SLit 3) VP0.
odn_cv RS1 36 4%N (SExt true 32 (SOff 35 0)) VP4.
odn_cv RS1 40 8%N (SLit 0) VP8.
odn_cv RS1 48 8%N (SOff 20 0) VP16.
odn_cv RS2 80 8%N (SOff 38 0) VP48.
odn_cv RS2 88 8%N (SOff 39 0) VP56.
odn_cv RS2 96 4%N (SExt true 32 (SOff 36 0)) VP64.
odn_cv RS2 100 2%N (SExt true 16 (SOff 37 0)) VP68.
odn_cv RS2 102 2%N (SLit 0) VP70.
cbn [base_val] in VP0, VP4, VP8, VP16, VP48, VP56, VP64, VP68, VP70.
rewrite U26b in VP0, VP4, VP8, VP16, VP48, VP56, VP64, VP68, VP70.
change (N.to_nat 8) with 8%nat in VP8, VP16, VP48, VP56.
change (N.to_nat 4) with 4%nat in VP0, VP4, VP64. change (N.to_nat 2) with 2%nat in VP68, VP70.
change (bv_unsigned (sv_denot E1 (SLit 3)) mod 2 ^ (8 * Z.of_N 4)) with 3 in VP0.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in VP8.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 2)) with 0 in VP70.
rewrite (odn_lw_val E1 35 st (E1v 35%nat st ltac:(lia) E035)) in VP4.
rewrite (odn_off_val E1 20 fp 8 E120 ltac:(lia)) in VP16.
rewrite (odn_off_val E1 38 (buf + 30) 8 (E1v 38%nat _ ltac:(lia) E038) ltac:(lia)) in VP48.
rewrite (odn_off_val E1 39 (DSpec.fr_body_len b) 8 (E1v 39%nat _ ltac:(lia) E039) ltac:(lia)) in VP56.
rewrite (odn_lw_val E1 36 (DSpec.fr_send b) (E1v 36%nat _ ltac:(lia) E036)) in VP64.
rewrite (odn_lh_val E1 37 (DSpec.fr_retry b) (E1v 37%nat _ ltac:(lia) E037)) in VP68.
apply (odn_vm_mod _ _ 4 _ st (Zmod_mod st (2 ^ (8 * Z.of_nat 4)))) in VP4.
apply (odn_vm_mod _ _ 8 _ fp (Zmod_mod fp (2 ^ (8 * Z.of_nat 8)))) in VP16.
apply (odn_vm_mod _ _ 8 _ (buf + 30) (Zmod_mod (buf + 30) (2 ^ (8 * Z.of_nat 8)))) in VP48.
apply (odn_vm_mod _ _ 8 _ (DSpec.fr_body_len b) (Zmod_mod (DSpec.fr_body_len b) (2 ^ (8 * Z.of_nat 8)))) in VP56.
apply (odn_vm_mod _ _ 4 _ (DSpec.fr_send b) (Zmod_mod (DSpec.fr_send b) (2 ^ (8 * Z.of_nat 4)))) in VP64.
apply (odn_vm_mod _ _ 2 _ (DSpec.fr_retry b) (Zmod_mod (DSpec.fr_retry b) (2 ^ (8 * Z.of_nat 2)))) in VP68.
pose proof (odn_nb_garr8 (w_H W2) (ms_mem ms) F st fp (buf + 30) (DSpec.fr_body_len b) (DSpec.fr_send b)
  (DSpec.fr_retry b) VP0 VP4 VP8 VP16 ZMN VP48 VP56 VP64 VP68 VP70) as HNB.
destruct (odn_nb_fields st fp (buf + 30) (DSpec.fr_body_len b) (DSpec.fr_send b) (DSpec.fr_retry b) R112 Hbp
  ltac:(lia) Hsd Hrt) as (NB0 & NB1 & NB2 & NB3 & NB4 & NB5 & NB6 & NB7 & NB8 & NB9 & NB10 & NB11).
(* what the call kept, from its entry to the call of notice *)
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
pose proof (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
  (ms_mem ms) (spZ regs - ONDATA_STK) (spZ regs) ONDATA_CID pos F FL (ondata_wr Bw b) (odn_Z F sp1) HGX HARc HAR2
  Hfrs Hbl2 HlyF EF eq_refl FFL ltac:(lia) ltac:(lia)
  (fun a Ha => odn_Z_in F FL sp1 (spZ regs) a ltac:(lia) ltac:(lia) Ha) HK KAN GAN) as KCN.
(* the registers at `jalr a2` *)
odn_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) T2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) T3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) T4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) T25
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 26) (YK11.getr regs2 (Z_to_bv 5 26)) T26
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
odn_reg HS (Z_to_bv 5 11) (w64 (F + 32)) T11 ltac:(cbn [sv_denot]; rewrite U26b; reflexivity).
odn_reg HS (Z_to_bv 5 12) (w64 (TW.S_notify w3)) T12
  ltac:(cbn [sv_denot]; rewrite (E1v 33%nat n96 ltac:(lia) E033), unsigned_lit_small, Z.add_0_r by exact R96;
        rewrite odn_notify_eq; reflexivity).
(* the bytes od_cur reads: the saved words, the frame word at s1 + 24, the frame's last word *)
assert (HSo : forall o, In o OD_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold OD_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (KHI : forall a, sp1 <= a < 2 ^ 47 -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; destruct (OHI a Ha) as (Hr & Hn); exact (KAN a Hr Hn)).
pmkst HS.
change (Z_to_bv 64 (BASE + 31624)) with (Z_to_bv 64 (BASE + OD_NC)).
apply (NC LAWS0 CALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B1 r f ly2 S2 W2 (ms_mem ms) md3 e (ms_regs ms) HFIX).
- split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  + split; [exact HJ2|]. split; [exact He|]. split; [exact Hfrs|]. split; [exact Hperm|]. split; [exact HlyF|].
    split; [exact Hmo|]. split; [exact KCN|]. split.
    * rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
      pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KHI. lia.
    * change (flag_addr lyc ONDATA_CID pos) with FL. unfold OD_FBYTES. rewrite <- HFLw. apply rdword_ext. intros i Hi.
      destruct (OFL (F + 256 - 8 + i) ltac:(lia)) as (Hr & Hn). exact (KAN _ Hr Hn).
  + rewrite <- Hs24. apply rdword_ext. intros i Hi. apply KHI. lia.
  + exact HSC.
  + apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact Htw2|].
    intros x Hx. destruct Hx as (o & bb & n & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS_B x) by exact (odn_inG_row o bb n x Hin3 ltac:(lia)).
    pose proof (inG_low segs B transportb_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
    apply KAN; [lia|]. apply OLOW; [unfold kLowMemEnd; lia|].
    intros Hf. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONDATA_CID pos x HAR2 Hin);
      [rewrite EF2; change (fs_frame_bytes ONDATA_CID) with 256; lia | exact (trans_g_img x HxG)].
  + exact Hgf1.
  + exact Hdup.
  + exact Hka.
  + exact ZSN.
  + exists (odn_nb st fp (buf + 30) (DSpec.fr_body_len b) (DSpec.fr_send b) (DSpec.fr_retry b)).
    split; [exact HNB|]. split; [exact NB0|]. split; [exact NB1|].
    split; [rewrite odn_state_eq; exact NB2|].
    split; [exact NB3|]. split; [exact NB4|]. split; [exact NB5|]. split; [exact NB6|]. split; [exact NB7|].
    split; [exact NB8|]. split; [exact NB9|]. split; [exact NB10|]. exact NB11.
- split; [|split].
  + split; [exact (eq_trans T2 R2)|]. split; [exact (eq_trans T3 R3)|]. split; [exact (eq_trans T4 R4)|].
    split; [exact (eq_trans T8 R8)|]. split; [exact (eq_trans T9 R9)|]. split; [exact (eq_trans T25 R25)|].
    exact (eq_trans T26 R26).
  + exact T11.
  + exact T12.
Qed.

End odnm.

Theorem od_ntc : forall fx rc B MT, @od_ntc_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odn_main fx rc B MT). Qed.

Print Assumptions od_ntc.
