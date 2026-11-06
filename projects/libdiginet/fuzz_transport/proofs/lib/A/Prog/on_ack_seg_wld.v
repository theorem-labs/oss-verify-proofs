(* on_ack_seg_wld: the world-field lemmas the two call pieces of on_ack's image-A walk share (the notice piece
   +0x180 .. +0x248 and the after-notice piece +0x24c .. +0x2ac of lib/A/Prog/on_ack_segs.v). Each says which fields
   of the TModel world a 4-byte or 8-byte store leaves alone, by TWorldLemmas.v's out-of-range lemmas over the
   numeral offsets of lib/TModel/TWorld.v:
   - onack_w1_facts: the store of :229 (g_s.inflight, 4 bytes at OFF_g_s + 212) keeps the state, the retry count,
     the notify pointer and its context, wake_acked and g_fail_next;
   - onack_B2_facts: notice's N_ACKED store (GOT.acked, 4 bytes at OFF_GOT + 216) keeps every g_s field the rest of
     the walk reads, GOT.n and g_fail_next;
   - onack_wake_fail: the store of :234 (g_s.wake_acked, 4 bytes at OFF_g_s + 144) keeps g_fail_next;
   - onack_maybeon_wr_eq: so the range maybe_online writes at the world on_ack hands it (notice's world with
     wake_acked set) is the range it writes at set_S_wake_acked (onack_w1 Bw) 1, which on_ack_cg.v onack_wr names.
   Nothing here runs an instruction. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
m_lost_cg check_state_data_cg notice_cg maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* A 4-byte store inside the world keeps its length. *)
Lemma onack_len_upd4 : forall (Bw : list byte) k v, 0 <= k -> k + 4 <= TW.W_LEN ->
  Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (TW.upd Bw k (TW.put 4 v))) = TW.W_LEN.
Proof.
intros Bw k v H1 H2 HL. rewrite TWL.length_upd_put; [exact HL | exact H1 | rewrite HL; exact H2].
Qed.

(* The store of :229 (g_s.inflight, 4 bytes) keeps every field the rest of the walk reads. *)
Lemma onack_w1_facts : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.S_state (onack_w1 Bw) = TW.S_state Bw /\
  TW.S_inflight_retries (onack_w1 Bw) = TW.S_inflight_retries Bw /\
  TW.S_notify (onack_w1 Bw) = TW.S_notify Bw /\
  TW.S_notify_ctx (onack_w1 Bw) = TW.S_notify_ctx Bw /\
  TW.S_wake_acked (onack_w1 Bw) = TW.S_wake_acked Bw /\
  TW.g_fail_next (onack_w1 Bw) = TW.g_fail_next Bw /\
  Z.of_nat (length (onack_w1 Bw)) = TW.W_LEN.
Proof.
intros Bw HL.
unfold onack_w1, TW.set_S_inflight, TW.S_state, TW.S_inflight_retries, TW.S_notify, TW.S_notify_ctx,
  TW.S_wake_acked, TW.g_fail_next.
assert (HP : Z.of_nat (length (TW.put 4 0)) = 4) by (rewrite TWL.length_put; reflexivity).
repeat split.
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_state, TW.OFF_g_s; lia | rewrite HP; unfold TW.A_S_inflight, TW.A_S_state, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_inflight_retries, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_inflight, TW.A_S_inflight_retries, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_notify, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_inflight, TW.A_S_notify, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_notify_ctx, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_inflight, TW.A_S_notify_ctx, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_inflight, TW.A_S_wake_acked, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | unfold TW.OFF_g_fail_next; lia
   | rewrite HP; unfold TW.A_S_inflight, TW.OFF_g_s, TW.OFF_g_fail_next; lia
   | rewrite HP, HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.length_upd_put; [exact HL | unfold TW.A_S_inflight, TW.OFF_g_s; lia
   | rewrite HL; unfold TW.A_S_inflight, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* notice's N_ACKED store (GOT.acked, 4 bytes at OFF_GOT + 216) keeps every g_s field the rest of the walk reads,
   GOT.n and g_fail_next: the ranges are apart. *)
Lemma onack_B2_facts : forall Bw a, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.S_state (TW.set_GOT_acked Bw a) = TW.S_state Bw /\
  TW.S_wake_acked (TW.set_GOT_acked Bw a) = TW.S_wake_acked Bw /\
  TW.S_e1_named_us (TW.set_GOT_acked Bw a) = TW.S_e1_named_us Bw /\
  TW.S_last_rx_us (TW.set_GOT_acked Bw a) = TW.S_last_rx_us Bw /\
  TW.S_cfg_keepalive_ms (TW.set_GOT_acked Bw a) = TW.S_cfg_keepalive_ms Bw /\
  TW.GOT_n (TW.set_GOT_acked Bw a) = TW.GOT_n Bw /\
  TW.g_fail_next (TW.set_GOT_acked Bw a) = TW.g_fail_next Bw /\
  Z.of_nat (length (TW.set_GOT_acked Bw a)) = TW.W_LEN.
Proof.
intros Bw a HL.
unfold TW.set_GOT_acked, TW.S_state, TW.S_wake_acked, TW.S_e1_named_us, TW.S_last_rx_us, TW.S_cfg_keepalive_ms,
  TW.GOT_n, TW.g_fail_next.
assert (HP : Z.of_nat (length (TW.put 4 a)) = 4) by (rewrite TWL.length_put; reflexivity).
repeat split.
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.A_S_state, TW.OFF_g_s; lia | rewrite HP; unfold TW.A_GOT_acked, TW.A_S_state, TW.OFF_GOT, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_GOT_acked, TW.A_S_wake_acked, TW.OFF_GOT, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.A_S_e1_named_us, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_GOT_acked, TW.A_S_e1_named_us, TW.OFF_GOT, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.A_S_last_rx_us, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_GOT_acked, TW.A_S_last_rx_us, TW.OFF_GOT, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.A_S_cfg_keepalive_ms, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_GOT_acked, TW.A_S_cfg_keepalive_ms, TW.OFF_GOT, TW.OFF_g_s; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia | rewrite HP; unfold TW.A_GOT_acked, TW.A_GOT_n, TW.OFF_GOT; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | unfold TW.OFF_g_fail_next; lia | rewrite HP; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.OFF_g_fail_next; lia
   | rewrite HP, HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
- rewrite TWL.length_upd_put; [exact HL | unfold TW.A_GOT_acked, TW.OFF_GOT; lia
   | rewrite HL; unfold TW.A_GOT_acked, TW.OFF_GOT, TW.W_LEN; lia].
Qed.

(* The store of :234 (g_s.wake_acked, 4 bytes) keeps g_fail_next and the length. *)
Lemma onack_wake_fail : forall Bw v, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (TW.set_S_wake_acked Bw v) = TW.g_fail_next Bw /\
  Z.of_nat (length (TW.set_S_wake_acked Bw v)) = TW.W_LEN.
Proof.
intros Bw v HL. unfold TW.set_S_wake_acked, TW.g_fail_next.
assert (HP : Z.of_nat (length (TW.put 4 v)) = 4) by (rewrite TWL.length_put; reflexivity).
split.
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | unfold TW.OFF_g_fail_next; lia | rewrite HP; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.OFF_g_fail_next; lia
   | rewrite HP, HL; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.length_upd_put; [exact HL | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | rewrite HL; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The store of :234 at a world and the fields maybe_online's written range reads. *)
Lemma onack_wake_facts : forall (Bx : list byte) w, Z.of_nat (length Bx) = TW.W_LEN ->
  TW.S_state (TW.set_S_wake_acked Bx w) = TW.S_state Bx /\
  TW.S_wake_acked (TW.set_S_wake_acked Bx w) = bv_swrap 32 w /\
  TW.S_e1_named_us (TW.set_S_wake_acked Bx w) = TW.S_e1_named_us Bx /\
  TW.S_last_rx_us (TW.set_S_wake_acked Bx w) = TW.S_last_rx_us Bx /\
  TW.S_cfg_keepalive_ms (TW.set_S_wake_acked Bx w) = TW.S_cfg_keepalive_ms Bx /\
  TW.GOT_n (TW.set_S_wake_acked Bx w) = TW.GOT_n Bx.
Proof.
intros Bx w HX. unfold TW.set_S_wake_acked, TW.S_state, TW.S_wake_acked, TW.S_e1_named_us, TW.S_last_rx_us,
  TW.S_cfg_keepalive_ms, TW.GOT_n.
assert (HP : Z.of_nat (length (TW.put 4 w)) = 4) by (rewrite TWL.length_put; reflexivity).
repeat split.
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | unfold TW.A_S_state, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_wake_acked, TW.A_S_state, TW.OFF_g_s; lia
   | rewrite HP, HX; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_put; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | rewrite HX; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | unfold TW.A_S_e1_named_us, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_wake_acked, TW.A_S_e1_named_us, TW.OFF_g_s; lia
   | rewrite HP, HX; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | unfold TW.A_S_last_rx_us, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_wake_acked, TW.A_S_last_rx_us, TW.OFF_g_s; lia
   | rewrite HP, HX; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | unfold TW.A_S_cfg_keepalive_ms, TW.OFF_g_s; lia
   | rewrite HP; unfold TW.A_S_wake_acked, TW.A_S_cfg_keepalive_ms, TW.OFF_g_s; lia
   | rewrite HP, HX; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
- rewrite TWL.s32_at_upd_out; [reflexivity | unfold TW.A_S_wake_acked, TW.OFF_g_s; lia
   | unfold TW.A_GOT_n, TW.OFF_GOT; lia
   | rewrite HP; unfold TW.A_S_wake_acked, TW.A_GOT_n, TW.OFF_g_s, TW.OFF_GOT; lia
   | rewrite HP, HX; unfold TW.A_S_wake_acked, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The written range maybe_online leaves (maybe_online_cg.v maybeon_wr) reads S_state, S_wake_acked, S_e1_named_us,
   S_last_rx_us, S_cfg_keepalive_ms and GOT.n only, each at maybeon_w1 / maybeon_w2 of the world it is called with,
   so the three lemmas above are what says notice's N_ACKED store of GOT.acked changes none of them. The piece that
   calls maybe_online states the congruence it needs over those worlds. *)
