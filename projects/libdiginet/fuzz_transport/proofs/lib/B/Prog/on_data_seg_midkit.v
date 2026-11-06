(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1210 of its 1392 lines of code are new or changed and 957 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_ack_seg_head.v, with its module paths and module names changed; 398 of its 513 lines of code are new or changed and 1277 lines of the source are left out. *)
(* on_data_seg_midkit: what the three middle pieces of the image-B walk of on_data (lib/B/Prog/on_data_seg_cut.v
   od_acks_stmt, od_dup_stmt, od_set_stmt; offsets +0x174 .. +0x2e4 of lib/B/Prog/DgnTransportBList.v) share. Image
   B's twin of lib/A/Prog/on_data_seg_midkit.v: the same lemmas at image B's names (TWorldB.v TMAP_B and its rows,
   B/TransportGB.v G_HARNESS_B, DgnTransportBCg.v, DgnTransportBImg.v transportb_segs_low, m_set_cg.v twb_fld).

   The three pieces run over the caller's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) with the
   class-2 frame owned, between the return of send_control and the call of diginet_frame_is_keepalive. Each run
   stores into fields of g_s (bytes of G, admitted by W_journalG.v awr_ok_x_cons_g) and, in the acks piece, into the
   word of the function's own machine frame at s1 + 24 (bytes of the call's stack window, admitted by awr_ok_x_cons;
   image B keeps the shadow address of f + 28 in s8, so no piece writes a word at s1 + 16); each checked access of a
   g_s field reads a shadow byte 0 (trans_ondata_cells through DgnTransportBCg.v decode_zshadow_rd), and each checked
   access of a field of f reads a shadow byte 0 of f's 64 bytes (on_ack_cg.v trans_dframe_at's decode_rd_ok, carried
   to the cut's memory by od_cur's acall_kept_g).

   What is here:
   - the model: ondata_w2's, ondata_w3's and the duplicate store's effect on g_fail_next and on the world's length,
     the two fields the duplicate test reads, and ms as the machine computes it (odm_ms);
   - G: a payload byte of a row of TWorldB.v TMAP_B is a byte of G_HARNESS_B (odm_row_inG), hence so is every byte of
     g_s's payload (odm_inG) and every byte of ondata_wr (odm_wr_inG);
   - f's fields: the 4 bytes at f + 20 are fr_send b and the 2 bytes at f + 28 are fr_retry b, as
     DgnTransportBCg.v frame_f_bytes leaves them (odm_f20, odm_f28);
   - the shadow: g_s's payload is addressable at every AR state (odm_ra_gs), and an addressable range gives the
     shadow byte 0 of each granule it covers (odm_sh0);
   - what a run of a piece keeps: acall_kept_g over a step that changes only the call's stack window and bytes of
     ondata_wr (odm_kept_step, over TransportGFrame.v dk_kept_step_gw), f's bytes and f's shadow bytes at the cut's
     memory (odm_f_kept), and od_cur moved to a later memory with the same view (odm_cur_move). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* A store of n bytes inside g_s's payload keeps g_fail_next and the world's length. *)
Lemma odm_gs_set : forall B k (n : nat) v, length B = Z.to_nat TW.W_LEN ->
  0 <= k -> k + Z.of_nat n <= TW.SZ_g_s ->
  TW.g_fail_next (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) = TW.g_fail_next B /\
  length (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) = Z.to_nat TW.W_LEN.
Proof.
intros B k n v HL Hk Hn.
assert (LZ : Z.of_nat (length B) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
split.
- unfold TW.g_fail_next.
  rewrite (TWL.u_at_upd_out B (TW.put n v) (TW.OFF_g_s + k) TW.OFF_g_fail_next 1);
  [reflexivity
  | unfold TW.OFF_g_s; lia
  | unfold TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put; unfold TW.OFF_g_s, TW.OFF_g_fail_next, TW.SZ_g_s in *; lia
  | rewrite TWL.length_put, LZ; unfold TW.OFF_g_s, TW.SZ_g_s, TW.W_LEN in *; lia].
- rewrite TWL.length_upd_put; [exact HL | unfold TW.OFF_g_s; lia |].
  rewrite LZ. unfold TW.OFF_g_s, TW.SZ_g_s, TW.W_LEN in *. lia.
Qed.

(* A field read at an offset the store misses. *)
Lemma odm_gs_u_out : forall B k (n : nat) v a (m : nat),
  length B = Z.to_nat TW.W_LEN -> 0 <= k -> k + Z.of_nat n <= TW.SZ_g_s -> 0 <= a ->
  (a + Z.of_nat m <= TW.OFF_g_s + k \/ TW.OFF_g_s + k + Z.of_nat n <= a) ->
  TW.u_at (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) a m = TW.u_at B a m.
Proof.
intros B k n v a m HL Hk Hn Ha Hd.
assert (LZ : Z.of_nat (length B) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
apply (TWL.u_at_upd_out B (TW.put n v) (TW.OFF_g_s + k) a m);
[ unfold TW.OFF_g_s; lia
| exact Ha
| rewrite TWL.length_put; exact Hd
| rewrite TWL.length_put, LZ; unfold TW.OFF_g_s, TW.SZ_g_s, TW.W_LEN in *; lia].
Qed.

(* One store inside g_s's payload, outside [164, 172): g_fail_next, the length and the two fields the duplicate
   test reads are unchanged. *)
Lemma odm_gs_step : forall B k (n : nat) v, length B = Z.to_nat TW.W_LEN ->
  0 <= k -> k + Z.of_nat n <= TW.SZ_g_s -> (k + Z.of_nat n <= 164 \/ 172 <= k) ->
  TW.g_fail_next (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) = TW.g_fail_next B /\
  length (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) = Z.to_nat TW.W_LEN /\
  TW.S_desk_counter (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) = TW.S_desk_counter B /\
  TW.S_desk_counter_valid (TW.upd B (TW.OFF_g_s + k) (TW.put n v)) = TW.S_desk_counter_valid B.
Proof.
intros B k n v HB Hk Hn Hd. destruct (odm_gs_set B k n v HB Hk Hn) as [Hg Hl].
split; [exact Hg|]. split; [exact Hl|]. split.
- unfold TW.S_desk_counter. apply (odm_gs_u_out B k n v); unfold TW.A_S_desk_counter, TW.OFF_g_s in *; lia.
- unfold TW.S_desk_counter_valid, TW.s32_at. f_equal.
  apply (odm_gs_u_out B k n v); unfold TW.A_S_desk_counter_valid, TW.OFF_g_s in *; lia.
Qed.

(* ondata_w2: three stores at 18160, 18176, 18208 and 192, each inside g_s's payload and outside [164, 172). *)
Lemma odm_w2_ok : forall B1 b r now, length B1 = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (ondata_w2 B1 b r now) = TW.g_fail_next B1 /\
  length (ondata_w2 B1 b r now) = Z.to_nat TW.W_LEN /\
  TW.S_desk_counter (ondata_w2 B1 b r now) = TW.S_desk_counter B1 /\
  TW.S_desk_counter_valid (ondata_w2 B1 b r now) = TW.S_desk_counter_valid B1.
Proof.
intros B1 b r now HL. unfold ondata_w2. cbv zeta.
set (Ba := if r =? 0 then TW.set_S_stats_tx_acks B1 (TS0.u64 (TW.S_stats_tx_acks B1 + 1)) else B1).
assert (HA : TW.g_fail_next Ba = TW.g_fail_next B1 /\ length Ba = Z.to_nat TW.W_LEN /\
  TW.S_desk_counter Ba = TW.S_desk_counter B1 /\ TW.S_desk_counter_valid Ba = TW.S_desk_counter_valid B1).
{ unfold Ba. destruct (r =? 0); [|split; [reflexivity | split; [exact HL | split; reflexivity]]].
  unfold TW.set_S_stats_tx_acks, TW.A_S_stats_tx_acks.
  replace (TW.OFF_g_s + 18152 + 56) with (TW.OFF_g_s + 18208) by lia.
  apply (odm_gs_step B1 18208 8); [exact HL | lia | unfold TW.SZ_g_s; lia | lia]. }
destruct HA as (GA & LA & DA & VA).
set (Bb := TW.set_S_stats_rx_data Ba (TS0.u64 (TW.S_stats_rx_data Ba + 1))).
assert (HB : TW.g_fail_next Bb = TW.g_fail_next Ba /\ length Bb = Z.to_nat TW.W_LEN /\
  TW.S_desk_counter Bb = TW.S_desk_counter Ba /\ TW.S_desk_counter_valid Bb = TW.S_desk_counter_valid Ba).
{ unfold Bb, TW.set_S_stats_rx_data, TW.A_S_stats_rx_data.
  replace (TW.OFF_g_s + 18152 + 8) with (TW.OFF_g_s + 18160) by lia.
  apply (odm_gs_step Ba 18160 8); [exact LA | lia | unfold TW.SZ_g_s; lia | lia]. }
destruct HB as (GB & LB & DB & VB).
destruct (DSpec.fr_retry b =? 0).
- rewrite GB, GA, LB, DB, DA, VB, VA. split; [reflexivity | split; [reflexivity | split; reflexivity]].
- set (Bc := TW.set_S_stats_rx_desk_retries Bb (TS0.u64 (TW.S_stats_rx_desk_retries Bb + 1))).
  assert (HC : TW.g_fail_next Bc = TW.g_fail_next Bb /\ length Bc = Z.to_nat TW.W_LEN /\
    TW.S_desk_counter Bc = TW.S_desk_counter Bb /\ TW.S_desk_counter_valid Bc = TW.S_desk_counter_valid Bb).
  { unfold Bc, TW.set_S_stats_rx_desk_retries, TW.A_S_stats_rx_desk_retries.
    replace (TW.OFF_g_s + 18152 + 24) with (TW.OFF_g_s + 18176) by lia.
    apply (odm_gs_step Bb 18176 8); [exact LB | lia | unfold TW.SZ_g_s; lia | lia]. }
  destruct HC as (GC & LC0 & DC & VC).
  unfold TW.set_S_backoff_until_us, TW.A_S_backoff_until_us.
  destruct (odm_gs_step Bc 192 8 (TS0.u64 (now + TS0.ms_m (TW.S_cfg_backoff_ms Bc))) LC0 ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia) ltac:(lia)) as (GD & LD & DD & VD).
  rewrite GD, GC, GB, GA, LD, DD, DC, DB, DA, VD, VC, VB, VA.
  split; [reflexivity | split; [reflexivity | split; reflexivity]].
Qed.

Lemma odm_w3_ok : forall B2 b, length B2 = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (ondata_w3 B2 b) = TW.g_fail_next B2 /\
  length (ondata_w3 B2 b) = Z.to_nat TW.W_LEN.
Proof.
intros B2 b HL. unfold ondata_w3, TW.set_S_desk_counter_valid, TW.set_S_desk_counter.
unfold TW.A_S_desk_counter_valid, TW.A_S_desk_counter.
destruct (odm_gs_set B2 164 4 (DSpec.fr_send b) HL ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as (G1 & L1).
destruct (odm_gs_set (TW.upd B2 (TW.OFF_g_s + 164) (TW.put 4 (DSpec.fr_send b))) 168 4 1 L1 ltac:(lia)
  ltac:(unfold TW.SZ_g_s; lia)) as (G2 & L2).
rewrite G2, G1, L2. split; reflexivity.
Qed.

Lemma odm_dupw_ok : forall B2, length B2 = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_S_stats_rx_duplicates B2 (TS0.u64 (TW.S_stats_rx_duplicates B2 + 1))) =
    TW.g_fail_next B2 /\
  length (TW.set_S_stats_rx_duplicates B2 (TS0.u64 (TW.S_stats_rx_duplicates B2 + 1))) = Z.to_nat TW.W_LEN.
Proof.
intros B2 HL. unfold TW.set_S_stats_rx_duplicates, TW.A_S_stats_rx_duplicates.
replace (TW.OFF_g_s + 18152 + 16) with (TW.OFF_g_s + 18168) by lia.
apply (odm_gs_set B2 18168 8); [exact HL | lia | unfold TW.SZ_g_s; lia].
Qed.

(* ms (diginet_session.c:77) of a uint32_t: the 64-bit product, which does not wrap. *)
Lemma odm_ms : forall v, 0 <= v < 2 ^ 32 -> TS0.ms_m v = v * 1000.
Proof. intros v Hv. unfold TS0.ms_m, TS0.u64. apply Z.mod_small. lia. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The fields of f inside frame_f_bytes                             *)
(* ------------------------------------------------------------------ *)

Lemma odm_blen : forall b, DSpec.fr_code b = 0 -> (30 <= length b)%nat.
Proof.
intros b H. destruct (Nat.ltb_spec (length b) 30) as [Hlt | Hge]; [|exact Hge].
exfalso. unfold DSpec.fr_code in H.
rewrite (proj2 (Nat.ltb_lt (length b) 30) Hlt) in H. discriminate H.
Qed.

Lemma odm_nth_peel : forall (l1 l2 : list byte) (n j : nat) d,
  length l1 = n -> nth (n + j) (l1 ++ l2) d = nth j l2 d.
Proof. intros l1 l2 n j d <-. rewrite app_nth2 by lia. f_equal. lia. Qed.

Lemma odm_map_nth : forall (l : list byte) n,
  nth n (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
intros l n. rewrite <- (map_nth (fun x : byte => bv_unsigned x) l (Z_to_bv 8 0) n). reflexivity.
Qed.

(* the byte of a C4 / C2 cell, as the little-endian byte of its value *)
Lemma odm_cell_byte : forall (m : nat) (v : Z) (t : nat) d, (t < m)%nat -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (nth t (Z_to_le_bytes m (bv_unsigned (Z_to_bv 64 v))) d) = YO0f.le_byte v m t.
Proof.
intros m v t d Ht Hv.
change (Z_to_le_bytes m (bv_unsigned (Z_to_bv 64 v)))
  with (TW.put m (bv_unsigned (Z_to_bv 64 v))).
rewrite (tw_le_byte_put m (bv_unsigned (Z_to_bv 64 v)) t d Ht).
rewrite (unsigned_lit_small v Hv). reflexivity.
Qed.

Lemma odm_f20 : forall (mm : word -> option byte) fp buf b fj,
  DSpec.fr_code b = 0 -> length fj = 64%nat ->
  YI00.garr8 tfibsegs mm fp (frame_f_bytes buf b fj) ->
  YI04.val_mem tfibsegs mm (fp + 20) 4 (DSpec.fr_send b).
Proof.
intros mm fp buf b fj Hc Hfj HG.
pose proof (odm_blen b Hc) as Hb.
pose proof (DSpec.be32_range b 18) as Hsend. change (DSpec.be32 b 18) with (DSpec.fr_send b) in Hsend.
assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
assert (L2 : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia).
assert (L3 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (rewrite length_firstn, length_skipn, Hfj; lia).
assert (LB : length (frame_f_bytes buf b fj) = 64%nat).
{ unfold frame_f_bytes, frame_f_cells. rewrite Hc. cbn [Z.eqb].
  rewrite length_map. apply LC.cells_bytes_length.
  cbn [PParse.parse_cells LC.cells_wf LC.cell_wf].
  repeat split; first [exact L1 | exact L2 | exact L3 | exact I | rewrite length_skipn, Hfj; lia]. }
assert (NTH : forall t, (t < 4)%nat ->
  nth (20 + t) (frame_f_bytes buf b fj) 0 = YO0f.le_byte (DSpec.fr_send b) 4 t).
{ intros t Ht. unfold frame_f_bytes, frame_f_cells. rewrite Hc. cbn [Z.eqb].
  rewrite odm_map_nth.
  cbn [PParse.parse_cells LC.cells_bytes LC.cbytes].
  replace (20 + t)%nat with (6 + (6 + (2 + (2 + (2 + (2 + t))))))%nat by lia.
  rewrite (odm_nth_peel _ _ 6 _ _ L1), (odm_nth_peel _ _ 6 _ _ L2),
    (odm_nth_peel _ _ 2 _ _ (LMem.length_le2 _)), (odm_nth_peel _ _ 2 _ _ L3),
    (odm_nth_peel _ _ 2 _ _ (LMem.length_le2 _)), (odm_nth_peel _ _ 2 _ _ (LMem.length_le2 _)).
  rewrite app_nth1 by (rewrite LMem.length_le4; exact Ht).
  unfold LMem.le4. apply odm_cell_byte; [exact Ht | lia]. }
intros t Ht.
destruct (HG (20 + t)%nat ltac:(rewrite LB; lia)) as [HV HR].
rewrite (NTH t Ht) in HV, HR.
specialize (HV 0%nat ltac:(lia)).
replace (fp + Z.of_nat (20 + t) + Z.of_nat 0) with (fp + 20 + Z.of_nat t) in HV by lia.
rewrite HV. f_equal. f_equal. apply tw_le_byte1. exact HR.
Qed.

Lemma odm_f28 : forall (mm : word -> option byte) fp buf b fj,
  DSpec.fr_code b = 0 -> length fj = 64%nat ->
  YI00.garr8 tfibsegs mm fp (frame_f_bytes buf b fj) ->
  YI04.val_mem tfibsegs mm (fp + 28) 2 (DSpec.fr_retry b).
Proof.
intros mm fp buf b fj Hc Hfj HG.
pose proof (odm_blen b Hc) as Hb.
pose proof (DSpec.be16_range b 26) as Hretry. change (DSpec.be16 b 26) with (DSpec.fr_retry b) in Hretry.
assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
assert (L2 : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia).
assert (L3 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (rewrite length_firstn, length_skipn, Hfj; lia).
assert (LB : length (frame_f_bytes buf b fj) = 64%nat).
{ unfold frame_f_bytes, frame_f_cells. rewrite Hc. cbn [Z.eqb].
  rewrite length_map. apply LC.cells_bytes_length.
  cbn [PParse.parse_cells LC.cells_wf LC.cell_wf].
  repeat split; first [exact L1 | exact L2 | exact L3 | exact I | rewrite length_skipn, Hfj; lia]. }
assert (NTH : forall t, (t < 2)%nat ->
  nth (28 + t) (frame_f_bytes buf b fj) 0 = YO0f.le_byte (DSpec.fr_retry b) 2 t).
{ intros t Ht. unfold frame_f_bytes, frame_f_cells. rewrite Hc. cbn [Z.eqb].
  rewrite odm_map_nth.
  cbn [PParse.parse_cells LC.cells_bytes LC.cbytes].
  replace (28 + t)%nat with (6 + (6 + (2 + (2 + (2 + (2 + (4 + (4 + t))))))))%nat by lia.
  rewrite (odm_nth_peel _ _ 6 _ _ L1), (odm_nth_peel _ _ 6 _ _ L2),
    (odm_nth_peel _ _ 2 _ _ (LMem.length_le2 _)), (odm_nth_peel _ _ 2 _ _ L3),
    (odm_nth_peel _ _ 2 _ _ (LMem.length_le2 _)), (odm_nth_peel _ _ 2 _ _ (LMem.length_le2 _)),
    (odm_nth_peel _ _ 4 _ _ (LMem.length_le4 _)), (odm_nth_peel _ _ 4 _ _ (LMem.length_le4 _)).
  rewrite app_nth1 by (rewrite LMem.length_le2; exact Ht).
  unfold LMem.le2. apply odm_cell_byte; [exact Ht | lia]. }
intros t Ht.
destruct (HG (28 + t)%nat ltac:(rewrite LB; lia)) as [HV HR].
rewrite (NTH t Ht) in HV, HR.
specialize (HV 0%nat ltac:(lia)).
replace (fp + Z.of_nat (28 + t) + Z.of_nat 0) with (fp + 28 + Z.of_nat t) in HV by lia.
rewrite HV. f_equal. f_equal. apply tw_le_byte1. exact HR.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. G and the shadow                                                 *)
(* ------------------------------------------------------------------ *)

Lemma odm_row_inG : forall o bse n a, In (o, bse, n) TMAP_B -> bse <= a < bse + n -> inG TG.G_HARNESS_B a.
Proof.
intros o bse n a Hin Ha. unfold inG. apply Exists_exists. exists (bse, n).
split; [exact (TMAP_B_in_G o bse n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma odm_inG : forall a, ONDATA_S <= a < ONDATA_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. apply (odm_row_inG TW.OFF_g_s TB_g_s TW.SZ_g_s a TMAP_B_g_s).
unfold ONDATA_S in Ha. exact Ha.
Qed.

Lemma odm_tw_in_G : forall x, tw_in TMAP_B x -> inG TG.G_HARNESS_B x.
Proof.
intros x (o & bse & n & Hin & Hx). exact (odm_row_inG o bse n x Hin Hx).
Qed.

Ltac odm_try R :=
  eapply (odm_row_inG _ _ _ _ R);
  solve [ unfold TB_M, TB_g_s, TB_g_cmd, TB_g_q, TB_g_fail_next, TB_g_last_counter, TB_g_nq, TB_GOT,
    TW.OFF_M, TW.OFF_g_s, TW.OFF_g_cmd, TW.OFF_g_q, TW.OFF_g_fail_next, TW.OFF_g_last_counter, TW.OFF_g_nq,
    TW.OFF_GOT, TW.SZ_M, TW.SZ_g_s, TW.SZ_g_cmd, TW.SZ_g_q, TW.SZ_g_last_counter, TW.SZ_g_nq, TW.SZ_GOT in *;
    lia ].
Ltac odm_rows :=
  first [ odm_try TMAP_B_g_s | odm_try TMAP_B_M | odm_try TMAP_B_GOT | odm_try TMAP_B_g_fail_next
        | odm_try TMAP_B_g_last_counter | odm_try TMAP_B_g_cmd | odm_try TMAP_B_g_q | odm_try TMAP_B_g_nq ].

(* Every byte the call stores is a byte of G. *)
Lemma odm_wr_inG : forall Bw b a, ondata_wr Bw b a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw b a H.
unfold ondata_wr, iosend_wr, notice_wr, twb_fld in H.
unfold TW.A_S_stats_tx_frames, TW.A_S_stats_tx_acks, TW.A_S_stats_rx_data, TW.A_S_stats_rx_desk_retries,
  TW.A_S_backoff_until_us, TW.A_S_stats_rx_duplicates, TW.A_S_desk_counter, TW.A_S_desk_counter_valid,
  TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_GOT_desk, TW.A_GOT_foreign, TW.A_GOT_acked, TW.A_GOT_ndata,
  TW.A_GOT_n, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.A_M_host_counter, TW.A_M_next_ka, TW.A_M_last_display,
  TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter, TW.A_M_fly_retries, TW.A_M_fly_sent,
  TW.A_M_fly_len, TW.A_M_fly_frame, TW.A_Cmd_st, SENDCTL_F, TC.SPEC_MAX_FRAME, TC.CMDS_MAX, TC.TRANS_MAX in H.
repeat match goal with
| HH : _ \/ _ |- _ => destruct HH as [HH | HH]
| HH : _ /\ _ |- _ => destruct HH as [? HH]
| HH : exists _, _ |- _ => destruct HH as [? HH]
end; odm_rows.
Qed.

(* A low byte of a value is a low byte of its residue, when the byte lies inside the residue. *)
Lemma odm_shiftr_mod : forall x (m j : nat), (j < m)%nat ->
  Z.shiftr x (8 * Z.of_nat j) mod 256 =
  Z.shiftr (x mod 2 ^ (8 * Z.of_nat m)) (8 * Z.of_nat j) mod 256.
Proof.
intros x m j Hj.
set (M := 8 * Z.of_nat m). set (J := 8 * Z.of_nat j).
assert (HJ : 0 <= J) by (unfold J; lia).
assert (HJM : J + 8 <= M) by (unfold J, M; lia).
assert (HP : 2 ^ M <> 0) by (apply Z.pow_nonzero; lia).
rewrite !Z.shiftr_div_pow2 by lia.
remember (x mod 2 ^ M) as r eqn:Er. remember (x / 2 ^ M) as q eqn:Eq.
assert (Ex : x = 2 ^ M * q + r) by (rewrite Er, Eq; apply Z.div_mod; exact HP).
rewrite Ex.
replace (2 ^ M) with (2 ^ (M - J) * 2 ^ J) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
replace (2 ^ (M - J) * 2 ^ J * q + r) with (2 ^ (M - J) * q * 2 ^ J + r) by ring.
rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
rewrite <- Z.add_mod_idemp_l by lia.
replace (2 ^ (M - J) * q mod 256) with 0; [rewrite Z.add_0_l; reflexivity|].
symmetry. apply Z.mod_divide; [lia|]. apply Z.divide_mul_l.
exists (2 ^ (M - J - 8)). change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* The bytes a run left in a region's chunk, read through the view: the little-endian bytes of any value the
   chunk's expression agrees with on its own width (the form TWorldG.v tw_write asks for). *)
Lemma odm_wr_bytes : forall E (Hh : word -> bool) (mm : word -> option byte) (nn : nat) base lo hi wlo whi cs
    od (w : N) e v,
  region_ok tfibsegs E (mrestrict Hh mm) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  In (YP09.mkChunk od (CVal w e)) cs ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_nat (N.to_nat w)) =
    v mod 2 ^ (8 * Z.of_nat (N.to_nat w)) ->
  forall j, (j < N.to_nat w)%nat ->
    aview tfibsegs Hh mm (base + od + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
intros E Hh mm nn base lo hi wlo whi cs od w e v HR Hb Hin Hv j Hj.
destruct HR as (_ & _ & _ & HF).
pose proof (proj1 (Forall_forall _ _) HF _ Hin) as HC.
cbn [YP09.r_base base_val] in HC. rewrite Hb in HC.
destruct (HC (Z.of_nat j) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (bb & Hcb & Hmb).
cbn [YP09.cbyte YP09.c_off YP09.c_val YP09.byte_of_word] in Hcb, Hmb.
unfold aview. cbv beta. rewrite Hmb. cbn [option_map]. cbv beta. f_equal.
injection Hcb as Hcb. rewrite <- Hcb.
unfold YP09.byte_of_word.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte.
rewrite (odm_shiftr_mod (bv_unsigned (sv_denot E e)) (N.to_nat w) j Hj).
rewrite Hv. reflexivity.
Qed.

(* Two stored values with the same residue write the same bytes. *)
Lemma odm_put_mod : forall (n : nat) x y, x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n) ->
  TW.put n x = TW.put n y.
Proof.
intros n x y H. unfold TW.put.
rewrite <- (LMem.Z_to_le_bytes_mod n x (8 * Z.of_nat n) ltac:(lia)).
rewrite <- (LMem.Z_to_le_bytes_mod n y (8 * Z.of_nat n) ltac:(lia)).
rewrite H. reflexivity.
Qed.

(* g_s's payload is addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma odm_ra_gs {rc : YM05.RunCeil} : forall (B : asyms) ly S (W : world tfibsegs) mem md (q n : Z),
  trans_ondata_cells B -> @AR rc tfibsegs B ly S W mem md ->
  ONDATA_S <= q -> q + n <= ONDATA_S + TW.SZ_g_s ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros B ly S W mem md q n HZ HAR Hlo Hhi x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONDATA_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONDATA_S + TW.SZ_g_s)
  by (unfold ONDATA_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONDATA_S (ONDATA_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* An addressable range whose base is 8-aligned has shadow byte 0 at every granule it covers. *)
Lemma odm_sh0 : forall (rd : Z -> option Z) p len k,
  p mod 8 = 0 -> 0 <= k -> k + 8 <= len -> range_addressable rd SHADOW_OFF p len ->
  rd (SHADOW_OFF + (p + k) / 8) = Some 0.
Proof.
intros rd p len k Hp Hk Hkl HRA.
pose proof (Z.div_mod k 8 ltac:(lia)) as Dk. pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as Mk.
assert (Dp : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)) as D; lia).
set (g := p + 8 * (k / 8)) in *.
assert (Hg : p <= g /\ g + 8 <= p + len) by (unfold g; lia).
destruct (HRA (g + 7) ltac:(lia)) as (s & Hs & Hok).
assert (Eg : (g + 7) mod 8 = 7).
{ unfold g. replace (p + 8 * (k / 8) + 7) with (7 + (p / 8 + k / 8) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
assert (Es : s = 0) by (unfold saddr_ok in Hok; rewrite Eg in Hok; lia).
rewrite Es in Hs. rewrite <- Hs. unfold shadow_of_addr. f_equal. f_equal.
assert (Ed : (g + 7) / 8 = (p + k) / 8).
{ unfold g. replace (p + 8 * (k / 8) + 7) with (7 + (p / 8 + k / 8) * 8) by lia.
  replace (p + k) with (k mod 8 + (p / 8 + k / 8) * 8) by lia.
  rewrite !Z.div_add by lia. rewrite (Z.div_small 7 8) by lia. rewrite (Z.div_small (k mod 8) 8) by lia.
  reflexivity. }
symmetry. exact Ed.
Qed.

(* A view byte 0 as a region's one-byte value. *)
Lemma odm_val0 : forall (Hh : word -> bool) (m : word -> option byte) a,
  aview tfibsegs Hh m a = Some 0 -> YI04.val_mem tfibsegs (mrestrict Hh m) a 1 0.
Proof.
intros Hh m a Ha k Hk. replace k with 0%nat by lia. rewrite Nat2Z.inj_0, Z.add_0_r.
unfold aview in Ha. cbv beta in Ha.
destruct (YP09.mbyte tfibsegs (mrestrict Hh m) a) as [x|] eqn:Em; [|discriminate Ha].
cbn [option_map] in Ha. injection Ha as Ha.
f_equal. apply bv_eq. rewrite Ha. reflexivity.
Qed.

(* A view that agrees at a reads the same byte. *)
Lemma odm_mb_eq : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a,
  aview tfibsegs H2 m2 a = aview tfibsegs H1 m1 a ->
  YP09.mbyte tfibsegs (mrestrict H2 m2) a = YP09.mbyte tfibsegs (mrestrict H1 m1) a.
Proof.
intros H1 H2 m1 m2 a Ha. unfold aview in Ha. cbv beta in Ha.
destruct (YP09.mbyte tfibsegs (mrestrict H2 m2) a) as [x|] eqn:E2;
destruct (YP09.mbyte tfibsegs (mrestrict H1 m1) a) as [y|] eqn:E1;
cbn [option_map] in Ha; try discriminate Ha; [|reflexivity].
injection Ha as Ha. f_equal. apply bv_eq. exact Ha.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. What a piece's run keeps                                         *)
(* ------------------------------------------------------------------ *)

Section kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Hypothesis LAWS : AR_laws segs B.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma odm_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W'
    mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* One step of a piece: it changes only bytes of the call's stack window and bytes of ondata_wr. *)
Lemma odm_kept_step : forall lyc Sc (W : world segs) memc mdc (W1 : world segs) memX memY slo shi Bw b
    (Zs : Z -> Prop),
  AR segs B lyc Sc W memc mdc -> gx_ok segs B TG.G_HARNESS_B ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ ondata_wr Bw b a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memX slo shi (ondata_wr Bw b) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memY slo shi (ondata_wr Bw b).
Proof.
intros lyc Sc W memc mdc W1 memX memY slo shi Bw b Zs HAR HGX Hce Hshi HZ KP Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LOW : forall a, ondata_wr Bw b a -> 0 <= a < kLowMemEnd).
{ intros a Ha. exact (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX (odm_wr_inG Bw b a Ha)). }
apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W1 memX memY slo shi
  (ondata_wr Bw b) Zs HAR KP Hkp Hgr).
- intros a Ha Hac. destruct (HZ a Ha) as [Hw | Ho]; [exact Hw|].
  exfalso. pose proof (LOW a Ho). unfold kLowMemEnd in *. lia.
- intros b0 m i Hb Hi Ha. destruct (HZ _ Ha) as [Hw | Ho]; [|exact Ho].
  exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hb) as (_ & H4096 & Hbc & _). lia.
- intros a Ha Hi HnG _ _. destruct (HZ a Ha) as [Hw | Ho].
  + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  + exact (HnG (odm_wr_inG Bw b a Ho)).
- intros cid pos a Hin Hr Ha. destruct (HZ a Ha) as [Hw | Ho]; [|exact Ho].
  exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* f's 64 bytes and their shadow bytes at the cut's memory are the ones at the entry: f lies in a frame of the
   call's frames, and no byte of ondata_wr is a byte of that frame or of its shadow. *)
Lemma odm_f_kept : forall lyc Sc (W : world segs) memc mdc (W1 : world segs) memX slo shi Bw b fp,
  AR segs B lyc Sc W memc mdc -> gx_ok segs B TG.G_HARNESS_B ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W1 memX slo shi (ondata_wr Bw b) ->
  decode_in_fake lyc Sc fp FRAME_F_SIZE ->
  (forall a, fp <= a < fp + 64 -> aview segs (w_H W1) memX a = aview segs (w_H W) memc a) /\
  (forall x, fp <= x < fp + 64 -> aview segs (w_H W1) memX (SHADOW_OFF + x / 8) =
     aview segs (w_H W) memc (SHADOW_OFF + x / 8)).
Proof.
intros lyc Sc W memc mdc W1 memX slo shi Bw b fp HAR HGX HK (cid & pos & Hin & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HK as (_ & _ & _ & K4 & _).
unfold FRAME_F_SIZE in Hhi.
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hal & HFapp & _ & _).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
pose proof (dkg_frame_al64 segs B lyc Sc W memc mdc cid pos HAR Hin) as (HF64 & Hfs64 & Hfs0).
set (F := frame_addr lyc cid pos) in *.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D64. rewrite HF64, Z.add_0_r in D64. rewrite D64.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
assert (HS8 : fs_frame_bytes cid mod 8 = 0).
{ pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D64. rewrite Hfs64, Z.add_0_r in D64. rewrite D64.
  replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia. apply Z_mod_mult. }
assert (NOWR : forall a, 0 <= a < kLowMemEnd -> ~ ondata_wr Bw b a -> True) by (intros; exact I).
split.
- intros a Ha. apply (K4 cid pos a Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. fold F. lia.
  + intros Ho. pose proof (odm_wr_inG Bw b a Ho) as Hg. destruct (HGX a Hg) as [Hi _].
    exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin ltac:(fold F; lia) Hi).
- intros x Hx. apply (K4 cid pos (SHADOW_OFF + x / 8) Hin).
  + right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F.
    pose proof (Z.div_le_mono F x 8 ltac:(lia) ltac:(lia)) as D1.
    assert (D2 : x / 8 < F / 8 + fs_frame_bytes cid / 8).
    { apply Z.div_lt_upper_bound; [lia|].
      pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS. rewrite HS8, Z.add_0_r in DS. lia. }
    lia.
  + intros Ho. pose proof (odm_wr_inG Bw b (SHADOW_OFF + x / 8) Ho) as Hg.
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    unfold kLowMemEnd, SHADOW_OFF in *. lia.
Qed.

(* od_cur at a later memory whose view is the same at every address and whose presence has grown. *)
Lemma odm_cur_move : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc k regs b Bw
    pos F ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 e,
  od_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONDATA_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  od_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

End kit.
